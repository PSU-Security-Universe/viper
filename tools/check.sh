#!/bin/bash

set -ex

objdump -d $1 | grep "@plt>:" | grep "exec\|system\|clone\|unlink\|removeAlreadyExistingData\|chown\|chmod\|symlink\|fchmod\|mprotect\|mremap\|fork\|vfork\|chdir\|fchdir\|fchmod\|fchown\|lchown\|setuid\|setgid\|setreuid\|setregid\|setgroups\|setfsuid\|setfsgid\|setrlimit\|chroot\|uselib\|delete_module\|fchownat\|unlinkat\|symlinkat\|seteuid\|setresuid\|remove"
