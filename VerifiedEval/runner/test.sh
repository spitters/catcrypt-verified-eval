#!/usr/bin/env bash
# Build vrun and check it on hand-written x86-64 byte sequences.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
cc -O2 -Wall -Wextra -o "$here/vrun" "$here/vrun.c" || exit 1
fail=0
check() { # name expected-output expected-rc input
  local out rc
  out="$(printf '%b' "$4" | "$here/vrun" 2>/dev/null)"; rc=$?
  if [ "$out" = "$2" ] && [ "$rc" = "$3" ]; then echo "ok   $1"
  else echo "FAIL $1: got '$out' rc=$rc, want '$2' rc=$3"; fail=1; fi
}
R0='0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0'
# mov %rbx,%rax (48 89 d8), result %rax
check rax-nonzero 1 0 "VRUN1\ncode 3 4889d8\nregs 0 0 0 5 0 0 0 0 0 0 0 0 0 0 0 0\nres 0\nend\n"
check rax-zero    0 0 "VRUN1\ncode 3 4889d8\nregs 9 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0\nres 0\nend\n"
# mov (%rsi),%rcx; mov %rcx,%rsp (48 8b 0e 48 89 cc), result %rsp; the arena word at 0x100008
check load-7   1 0 "VRUN1\ncode 6 488b0e4889cc\nregs 0 0 0 0 0 0 100008 0 0 0 0 0 0 0 0 0\nres 4\nregion 100000 8 0000000000000000\nregion 100008 8 0700000000000000\nend\n"
check load-0   0 0 "VRUN1\ncode 6 488b0e4889cc\nregs 0 0 0 0 ffff 0 100008 0 0 0 0 0 0 0 0 0\nres 4\nregion 100008 8 0000000000000000\nend\n"
# mov %r8,%r12 (4d 89 c4), result %r12 (REX.R in the epilogue)
check r12      1 0 "VRUN1\ncode 3 4d89c4\nregs 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0\nres 12\nend\n"
# a load from an unmapped arena address faults
check unmapped '' 139 "VRUN1\ncode 3 488b0e\nregs 0 0 0 0 0 0 200000 0 0 0 0 0 0 0 0 0\nres 1\nend\n"
# a region below mmap_min_addr cannot be mapped
check low-page '' 2 "VRUN1\ncode 0 -\nregs $R0\nres 1\nregion 1000 8 0000000000000000\nend\n"
exit $fail
