/* jail.c — the Linux isolation of one judged attempt (pod/runner.py). hol4/delta3/harness · 2026-11-25
 *
 *   jail --probe                      prints what this kernel/container allows, exits 0
 *   jail <writable-dir> -- cmd args   runs cmd with:
 *     1. no_new_privs;
 *     2. seccomp: socket() refused (EACCES) for every family but AF_UNIX, io_uring_setup refused (ENOSYS;
 *        io_uring can open sockets on its own), non-native syscall ABIs killed — so no network of any kind
 *        whether or not the container grants a network namespace;
 *     3. Landlock (when the kernel has it): file writes, creations, removals and renames only beneath
 *        <writable-dir> and /tmp (Poly/ML's temporary files), plus writing to /dev/null. Reads stay open.
 *        Without Landlock the runner's slot user (one unprivileged uid per slot, owner of nothing but its
 *        own run directory) is the only write barrier; the probe says which one holds.
 * Build: gcc -O2 -Wall -o jail jail.c   (Ubuntu 24.04: linux headers from linux-libc-dev)
 * MIT licensed. Part of cert-machine. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/socket.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <linux/landlock.h>

#if defined(__x86_64__)
#define ARCH_NR AUDIT_ARCH_X86_64
#elif defined(__aarch64__)
#define ARCH_NR AUDIT_ARCH_AARCH64
#else
#error "jail.c: unsupported architecture"
#endif
#ifndef __NR_io_uring_setup
#define __NR_io_uring_setup 425
#endif

static int install_seccomp(void) {
  struct sock_filter f[] = {
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, arch)),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, ARCH_NR, 1, 0),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
#if defined(__x86_64__)
    BPF_JUMP(BPF_JMP | BPF_JGE | BPF_K, 0x40000000, 0, 1),          /* x32 ABI */
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
#endif
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_io_uring_setup, 0, 1),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | ENOSYS),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_socket, 0, 3),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, args[0])),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AF_UNIX, 1, 0),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EACCES),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
  };
  struct sock_fprog prog = { .len = sizeof f / sizeof f[0], .filter = f };
  return prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog);
}

static int ll_abi(void) {
  return (int)syscall(__NR_landlock_create_ruleset, NULL, 0, LANDLOCK_CREATE_RULESET_VERSION);
}

static __u64 write_rights(int abi) {
  __u64 r = LANDLOCK_ACCESS_FS_WRITE_FILE | LANDLOCK_ACCESS_FS_REMOVE_DIR | LANDLOCK_ACCESS_FS_REMOVE_FILE |
            LANDLOCK_ACCESS_FS_MAKE_CHAR | LANDLOCK_ACCESS_FS_MAKE_DIR | LANDLOCK_ACCESS_FS_MAKE_REG |
            LANDLOCK_ACCESS_FS_MAKE_SOCK | LANDLOCK_ACCESS_FS_MAKE_FIFO | LANDLOCK_ACCESS_FS_MAKE_BLOCK |
            LANDLOCK_ACCESS_FS_MAKE_SYM;
#ifdef LANDLOCK_ACCESS_FS_REFER
  if (abi >= 2) r |= LANDLOCK_ACCESS_FS_REFER;
#endif
#ifdef LANDLOCK_ACCESS_FS_TRUNCATE
  if (abi >= 3) r |= LANDLOCK_ACCESS_FS_TRUNCATE;
#endif
  return r;
}

static int add_path(int rs, const char *path, __u64 rights) {
  int fd = open(path, O_PATH | O_CLOEXEC);
  if (fd < 0) return -1;
  struct landlock_path_beneath_attr pb = { .allowed_access = rights, .parent_fd = fd };
  int r = (int)syscall(__NR_landlock_add_rule, rs, LANDLOCK_RULE_PATH_BENEATH, &pb, 0);
  close(fd);
  return r;
}

static int install_landlock(const char *dir) {
  int abi = ll_abi();
  if (abi < 1) return 1;                              /* not available: caller reports it */
  __u64 all = write_rights(abi);
  struct landlock_ruleset_attr ra = { .handled_access_fs = all };
  int rs = (int)syscall(__NR_landlock_create_ruleset, &ra, sizeof ra, 0);
  if (rs < 0) return 1;
  __u64 file_w = LANDLOCK_ACCESS_FS_WRITE_FILE;
#ifdef LANDLOCK_ACCESS_FS_TRUNCATE
  if (abi >= 3) file_w |= LANDLOCK_ACCESS_FS_TRUNCATE;
#endif
  if (add_path(rs, dir, all) || add_path(rs, "/tmp", all) || add_path(rs, "/dev/null", file_w)) {
    perror("jail: landlock_add_rule"); return -1;
  }
  if (syscall(__NR_landlock_restrict_self, rs, 0)) { perror("jail: landlock_restrict_self"); return -1; }
  close(rs);
  return 0;
}

int main(int argc, char **argv) {
  if (argc == 2 && !strcmp(argv[1], "--probe")) {
    int abi = ll_abi();
    printf("landlock_abi=%d\n", abi > 0 ? abi : 0);
    return 0;
  }
  if (argc < 4 || strcmp(argv[2], "--")) { fprintf(stderr, "usage: jail <writable-dir> -- cmd args\n"); return 2; }
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)) { perror("jail: no_new_privs"); return 2; }
  int ll = install_landlock(argv[1]);
  if (ll < 0) return 2;
  fprintf(stderr, "jail: landlock %s\n", ll == 0 ? "on" : "UNAVAILABLE (uid separation only)");
  if (install_seccomp()) { perror("jail: seccomp"); return 2; }
  execvp(argv[3], argv + 3);
  perror("jail: exec");
  return 127;
}
