// SPDX-License-Identifier: GPL-2.0-or-later
/*
 * Copyright (C) 2023 bmax121. All Rights Reserved.
 *
 * The ko is compiled against a fixed KMI, so struct cred fields are directly
 * addressable (KP's kpimg needs runtime cred_offset instead). Full root =
 * all capabilities + uid/gid switch via a freshly prepared cred. The SELinux
 * translabel helper is resolved at runtime like KP does.
 */
#include "accctl.h"
#include <linux/sched/signal.h>
#include <linux/capability.h>
#include <linux/cred.h>
#include <linux/err.h>
#include <linux/errno.h>
#include <linux/pid.h>
#include <linux/sched.h>
#include <linux/sched/task.h>
#include <linux/seccomp.h>
#include <linux/spinlock.h>
#include <linux/thread_info.h>
#include <asm/thread_info.h>
#include <linux/slab.h>
#include <linux/string.h>
#include <linux/version.h>
#include <scdefs.h>

#include "../include/kp_lkm.h"
#include "../infra/symbol_resolver.h"

/* security_secctx_to_secid is EXPORT_SYMBOL on 5.15 — link it directly. */
extern int security_secctx_to_secid(const char *secdata, u32 seclen, u32 *secid);

/* selinux_blob_sizes is a global; resolve via kallsyms. cred->security is a
 * pointer to the LSM cred blob; the selinux part lives at +lbs_cred. */
struct kp_lsm_blob_sizes {
	int lbs_cred;
	int lbs_file;
	int lbs_inode;
	int lbs_superblock;
	int lbs_ipc;
	int lbs_msg_msg;
	int lbs_task;
};

static struct kp_lsm_blob_sizes *kp_selinux_blob_sizes;

/*
 * seccomp_filter_release() is not a stable exported KMI on every GKI build.
 * Resolve its runtime entry instead of creating a hard link dependency.
 */
typedef void (*kp_seccomp_filter_release_t)(struct task_struct *tsk);
typedef int (*kp_kallsyms_lookup_size_offset_t)(unsigned long addr,
						       unsigned long *symbolsize,
						       unsigned long *offset);

static kp_seccomp_filter_release_t kp_seccomp_filter_release;
static bool kp_seccomp_compat_ready;
static bool kp_seccomp_release_needs_pf_exiting;
static bool kp_seccomp_release_needs_null_sighand;

/* AArch64 BL decoder, matching the runtime compatibility check in KSU. */
#if defined(CONFIG_ARM64)
static bool kp_seccomp_scan_call_to(void *start, size_t size, void *target)
{
	const u32 *insn = (const u32 *)start;
	size_t count = size / sizeof(*insn);
	size_t i;

	for (i = 0; i < count; i++) {
		int32_t imm26;
		unsigned long branch_target;

		if ((insn[i] & 0xfc000000U) != 0x94000000U)
			continue;

		imm26 = (int32_t)((insn[i] & 0x03ffffffU) << 6) >> 6;
		branch_target = (unsigned long)&insn[i] + (long)(imm26 * 4LL);
		if (branch_target == (unsigned long)target)
			return true;
	}
	return false;
}
#else
static bool kp_seccomp_scan_call_to(void *start, size_t size, void *target)
{
	/* Android GKI targets supported by this LKM are arm64. */
	return false;
}
#endif

/*
 * Minimal fallback for kernels where seccomp_filter_release() cannot be
 * resolved/classified, or when the temporary task allocation fails.
 * Keep filter/filter_count intact: the current task still owns that reference
 * and the normal task-exit path must be allowed to release it.
 */
static bool kp_disable_current_seccomp_fallback(struct sighand_struct *sighand)
{
	if (!sighand)
		return false;

	spin_lock_irq(&sighand->siglock);
#if defined(CONFIG_GENERIC_ENTRY) && LINUX_VERSION_CODE >= KERNEL_VERSION(5, 11, 0)
	clear_syscall_work(SECCOMP);
#else
	clear_thread_flag(TIF_SECCOMP);
#endif
	current->seccomp.mode = SECCOMP_MODE_DISABLED;
	spin_unlock_irq(&sighand->siglock);

	logkw("seccomp filter teardown unavailable; disabled mode only, filter retained\n");
	return true;
}

/*
 * KSU-compatible seccomp teardown. This is deliberately called only after
 * commit_creds() succeeds and only for current; kp_task_su() is untouched.
 */
__attribute__((no_sanitize("cfi")))
static bool kp_disable_current_seccomp(void)
{
	struct task_struct *fake;
	struct sighand_struct *sighand;
	struct seccomp *seccomp;

	sighand = current->sighand;
	if (!sighand) {
		logkw("seccomp teardown skipped: current has no sighand\n");
		return false;
	}

	/* If full teardown is unavailable, use the safe mode-only fallback. */
	if (!kp_seccomp_filter_release || !kp_seccomp_compat_ready)
		return kp_disable_current_seccomp_fallback(sighand);

	fake = kmalloc(sizeof(*fake), GFP_KERNEL);
	if (!fake)
		return kp_disable_current_seccomp_fallback(sighand);

	spin_lock_irq(&sighand->siglock);
#if defined(CONFIG_GENERIC_ENTRY) && LINUX_VERSION_CODE >= KERNEL_VERSION(5, 11, 0)
	clear_syscall_work(SECCOMP);
#else
	clear_thread_flag(TIF_SECCOMP);
#endif
	/* Preserve the original filter in fake so release() drops its reference. */
	memcpy(fake, current, sizeof(*fake));

	seccomp = &current->seccomp;
	seccomp->mode = SECCOMP_MODE_DISABLED;
	seccomp->filter = NULL;
	atomic_set(&seccomp->filter_count, 0);
	spin_unlock_irq(&sighand->siglock);

	/*
	 * seccomp_filter_release() changed its teardown expectations in newer
	 * kernels. These compatibility adjustments mirror KSU:
	 *  - >= 6.11: PF_EXITING is required by the release path;
	 *  - 6.6..6.10: detect the Android backport at runtime;
	 *  - >= 5.11: older release paths must not dereference sighand.
	 */
	if (kp_seccomp_release_needs_pf_exiting)
		fake->flags |= PF_EXITING;
	else if (kp_seccomp_release_needs_null_sighand)
		fake->sighand = NULL;

	kp_seccomp_filter_release(fake);
	kfree(fake);
	return true;
}

/* Resolve and classify the release implementation before any task is changed. */
__attribute__((no_sanitize("cfi")))
static void kp_seccomp_init(void)
{
	void *release_body;
	void *raw_spin_lock_irq;
	void *size_lookup_sym;

	kp_seccomp_filter_release =	(kp_seccomp_filter_release_t)
		kp_resolve_symbol_variant("seccomp_filter_release");
	if (!kp_seccomp_filter_release) {
		logkw("seccomp_filter_release not found; seccomp teardown disabled\n");
		return;
	}

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 11, 0)
	kp_seccomp_release_needs_pf_exiting = true;
#elif LINUX_VERSION_CODE >= KERNEL_VERSION(6, 6, 0)
	/*
	 * Android 6.6 GKI has mixed backport states. Do not infer the behavior
	 * from uname: inspect whether seccomp_filter_release calls
	 * _raw_spin_lock_irq, as KernelSU does.
	 */
	release_body = (void *)kp_resolve_symbol("seccomp_filter_release");
	raw_spin_lock_irq = (void *)kp_resolve_symbol("_raw_spin_lock_irq");
	size_lookup_sym = kp_resolve_symbol_variant("kallsyms_lookup_size_offset");
	if (!release_body || !raw_spin_lock_irq || !size_lookup_sym) {
		logkw("cannot classify 6.6-6.10 seccomp release; teardown disabled\n");
		return;
	} else {
		kp_kallsyms_lookup_size_offset_t size_lookup =
			(kp_kallsyms_lookup_size_offset_t)size_lookup_sym;
		unsigned long size = 0;
		unsigned long offset = 0;
		int ret = size_lookup((unsigned long)release_body, &size, &offset);

		if (ret || !size)
			size = 128; /* Same bounded fallback used by KernelSU. */

		if (kp_seccomp_scan_call_to(release_body, size, raw_spin_lock_irq))
			kp_seccomp_release_needs_pf_exiting = true;
		else
			kp_seccomp_release_needs_null_sighand = true;
	}
#elif LINUX_VERSION_CODE >= KERNEL_VERSION(5, 11, 0)
	kp_seccomp_release_needs_null_sighand = true;
#endif

	kp_seccomp_compat_ready = true;
	logki("seccomp teardown ready (pf_exiting=%d null_sighand=%d)\n",
	      kp_seccomp_release_needs_pf_exiting,
	      kp_seccomp_release_needs_null_sighand);
}

/* task_security_struct { osid, sid, ... } — RANDSTRUCT is off, so sid is the
 * second u32 (offset 4). */
struct kp_task_sec {
	u32 osid;
	u32 sid;
};

int kp_accctl_init(void)
{
	kp_seccomp_init();
	kp_selinux_blob_sizes = (struct kp_lsm_blob_sizes *)kp_resolve_symbol("selinux_blob_sizes");
	if (!kp_selinux_blob_sizes) {
		logke("failed to resolve selinux_blob_sizes; selinux translabel disabled\n");
		return 0;
	}
	logki("selinux blob sizes: lbs_cred=%d\n", kp_selinux_blob_sizes->lbs_cred);
	return 0;
}

/* Translabel a freshly-prepared cred to the given SELinux context (5.15 has no
 * set_security_override_from_ctx; it was removed in GKI). Resolve the context
 * to a sid and write tsec->sid directly. */
static int kp_selinux_set_cred_context(struct cred *new, const char *sctx)
{
	struct kp_task_sec *tsec;
	u32 sid;
	int rc;

	if (!kp_selinux_blob_sizes || !sctx || !sctx[0])
		return -EINVAL;

	rc = security_secctx_to_secid(sctx, strlen(sctx), &sid);
	if (rc || !sid) {
		logkw("secctx_to_secid(%s) failed: %d sid=%u\n", sctx, rc, sid);
		return rc ? rc : -EINVAL;
	}

	tsec = (struct kp_task_sec *)((char *)new->security + kp_selinux_blob_sizes->lbs_cred);
	tsec->sid = sid;
	return 0;
}

/* Fill every capability in a kernel_cap_t. */
static void fill_caps(struct cred *new)
{
	kernel_cap_t all = CAP_FULL_SET;
	new->cap_effective = all;
	new->cap_permitted = all;
	new->cap_inheritable = all;
	new->cap_bset = all;
	new->cap_ambient = all;
}

static void su_cred(struct cred *new, uid_t uid)
{
	fill_caps(new);
	new->uid = make_kuid(current_user_ns(), uid);
	new->euid = new->uid;
	new->fsuid = new->uid;
	new->suid = new->uid;
	new->gid = make_kgid(current_user_ns(), uid);
	new->egid = new->gid;
	new->fsgid = new->gid;
	new->sgid = new->gid;
}

/* no_sanitize("cfi") keeps indirect calls in this function from tripping
 * __cfi_check on traditional-CFI 5.15 kernels. */
__attribute__((no_sanitize("cfi")))
static int commit_common_su(uid_t to_uid, const char *sctx)
{
	struct cred *new = prepare_creds();
	if (!new)
		return -ENOMEM;

	su_cred(new, to_uid);

	/* Translabel to sctx (e.g. u:r:magisk:s0 / u:r:kp:s0). Without this the
	 * granted process keeps its untrusted_app SELinux domain while running as
	 * uid 0 with all caps — Android blocks it and the app fails to open. If
	 * translabel fails, abort the creds so the caller falls back to another
	 * domain instead of committing an untranslabelled root. */
	if (sctx && sctx[0]) {
		int rc = kp_selinux_set_cred_context(new, sctx);
		if (rc) {
			logkw("selinux set context(%s) failed: %d\n", sctx, rc);
			abort_creds(new);
			return rc;
		}
	}

	commit_creds(new);
	return 0;
}

__attribute__((no_sanitize("cfi")))
int kp_commit_su(uid_t to_uid, const char *sctx)
{
	int rc;

	/* Empty sctx: default to the magisk domain (KP initializes all_allow_sctx
	 * to ALL_ALLOW_SCONTEXT_MAGISK). The u:r:kernel:s0 domain cannot connect
	 * sockets or run ART (seen: libsu RootServer ClassNotFoundException after
	 * Natives.su(0,null) granted kernel cred). Use the fully-qualified
	 * u:r:magisk:s0, resolved via security_secctx_to_secid. Fall back to
	 * kernel cred only if the domain is unavailable. */
	if (!sctx || !sctx[0]) {
		if (kp_selinux_blob_sizes) {
			rc = commit_common_su(to_uid, ALL_ALLOW_SCONTEXT_MAGISK);
			if (!rc) {
				kp_disable_current_seccomp();
				logki("commit_su: to_uid=%u magisk domain\n", to_uid);
				return 0;
			}
			logkw("magisk domain translabel failed (%d), kernel cred fallback\n", rc);
		}
		struct cred *new = prepare_kernel_cred(NULL);
		if (!new)
			return -ENOMEM;
		commit_creds(new);
		kp_disable_current_seccomp();
		logki("commit_su: to_uid=%u kernel cred (u:r:kernel:s0)\n", to_uid);
		return 0;
	}

	/* Explicit sctx: try the translabel, fall back to kernel cred if it fails
	 * so the caller still gets root. */
	rc = commit_common_su(to_uid, sctx);
	if (rc) {
		logkw("commit_common_su failed (%d), falling back to kernel cred\n", rc);
		struct cred *new = prepare_kernel_cred(NULL);
		if (!new)
			return -ENOMEM;
		commit_creds(new);
		kp_disable_current_seccomp();
		return 0;
	}
	kp_disable_current_seccomp();
	return 0;
}

int kp_task_su(pid_t pid, uid_t to_uid, const char *sctx)
{
	struct task_struct *task;
	const struct cred *old;
	struct cred *new;

	task = find_get_task_by_vpid(pid);
	if (!task) {
		logke("task_su: no task pid %d\n", pid);
		return -ESRCH;
	}

	new = prepare_creds();
	if (!new) {
		put_task_struct(task);
		return -ENOMEM;
	}
	su_cred(new, to_uid);
	(void)sctx;

	rcu_read_lock();
	old = task->cred;
	rcu_assign_pointer(task->cred, new);
	rcu_assign_pointer(task->real_cred, new);
	rcu_read_unlock();
	put_cred(old);

	put_task_struct(task);
	logki("task_su: pid %d -> uid %u\n", pid, to_uid);
	return 0;
}
