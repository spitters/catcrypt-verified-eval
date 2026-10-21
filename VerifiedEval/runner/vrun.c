/*
 * Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
 * Released under MIT license as described in the file LICENSE.
 *
 * vrun: run a block of x86-64 machine code on the host CPU from a given register file
 * and memory image, and print whether a chosen register is nonzero afterwards.
 *
 * Input (stdin), whitespace-separated tokens; numbers marked hex have no 0x prefix:
 *
 *   VRUN1
 *   code <n> <2n hex digits, or - when n = 0>
 *   regs <16 hex words>            register k in SDM numbering: rax rcx rdx rbx rsp rbp
 *                                  rsi rdi r8 .. r15
 *   res <k>                        decimal register number of the result, 0..15
 *   region <base hex> <n> <2n hex digits, or - when n = 0>     zero or more times
 *   end
 *
 * Every page that meets a region is mapped read-write at its fixed address with
 * MAP_FIXED_NOREPLACE (a collision with an existing mapping is an error), zero-filled,
 * and the region's bytes are copied in. The code is copied into fresh pages followed by
 * an epilogue `mov %r<res>, slot(%rip); jmp *ret(%rip)`, and the pages are made
 * read-execute. The trampoline `vrun_enter` saves the host's callee-saved registers and
 * %rsp, loads all sixteen registers (including %rsp) and jumps to the code; the epilogue
 * returns to `vrun_return`, which restores the host state.
 *
 * Output: `1` when the result register is nonzero at the end of the block, `0` otherwise.
 * Exit status 0 on a completed run, 2 on malformed input or a mapping failure. A fault
 * inside the code kills the process by its signal.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#ifndef MAP_FIXED_NOREPLACE
#define MAP_FIXED_NOREPLACE 0x100000
#endif

extern void vrun_enter(uint64_t *regs, void *entry);
extern char vrun_return[];

__asm__(
    ".text\n"
    ".globl vrun_enter\n"
    ".type vrun_enter,@function\n"
    "vrun_enter:\n"
    "  push %rbx\n  push %rbp\n  push %r12\n  push %r13\n  push %r14\n  push %r15\n"
    "  mov %rsp, vrun_saved_rsp(%rip)\n"
    "  mov %rsi, vrun_entry(%rip)\n"
    "  mov 0(%rdi), %rax\n  mov 8(%rdi), %rcx\n  mov 16(%rdi), %rdx\n"
    "  mov 24(%rdi), %rbx\n  mov 32(%rdi), %rsp\n  mov 40(%rdi), %rbp\n"
    "  mov 48(%rdi), %rsi\n  mov 64(%rdi), %r8\n  mov 72(%rdi), %r9\n"
    "  mov 80(%rdi), %r10\n  mov 88(%rdi), %r11\n  mov 96(%rdi), %r12\n"
    "  mov 104(%rdi), %r13\n  mov 112(%rdi), %r14\n  mov 120(%rdi), %r15\n"
    "  mov 56(%rdi), %rdi\n"
    "  jmp *vrun_entry(%rip)\n"
    ".globl vrun_return\n"
    "vrun_return:\n"
    "  mov vrun_saved_rsp(%rip), %rsp\n"
    "  pop %r15\n  pop %r14\n  pop %r13\n  pop %r12\n  pop %rbp\n  pop %rbx\n"
    "  cld\n"
    "  ret\n"
    ".bss\n"
    ".balign 8\n"
    "vrun_saved_rsp: .skip 8\n"
    "vrun_entry: .skip 8\n"
    ".text\n");

static void die(const char *msg) {
  fprintf(stderr, "vrun: %s\n", msg);
  exit(2);
}

/* Read one whitespace-delimited token into a growing buffer. */
static char *tok(void) {
  static char *buf = NULL;
  static size_t cap = 0;
  size_t n = 0;
  int c;
  do { c = getchar(); } while (c == ' ' || c == '\n' || c == '\t' || c == '\r');
  if (c == EOF) die("unexpected end of input");
  while (c != EOF && c != ' ' && c != '\n' && c != '\t' && c != '\r') {
    if (n + 1 >= cap) {
      cap = cap ? 2 * cap : 256;
      buf = realloc(buf, cap);
      if (!buf) die("out of memory");
    }
    buf[n++] = (char)c;
    c = getchar();
  }
  buf[n] = 0;
  return buf;
}

static uint64_t hexword(const char *s) {
  char *end;
  errno = 0;
  uint64_t v = strtoull(s, &end, 16);
  if (errno || *s == 0 || *end != 0) die("bad hex number");
  return v;
}

static uint64_t decnum(const char *s) {
  char *end;
  errno = 0;
  uint64_t v = strtoull(s, &end, 10);
  if (errno || *s == 0 || *end != 0) die("bad decimal number");
  return v;
}

static int hexdigit(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  die("bad hex digit");
  return 0;
}

/* Read `n` bytes given as one token of 2n hex digits ("-" when n = 0). */
static uint8_t *hexbytes(uint64_t n) {
  const char *s = tok();
  if (n == 0) {
    if (strcmp(s, "-") != 0) die("expected - for an empty byte string");
    return NULL;
  }
  if (strlen(s) != 2 * n) die("byte string length mismatch");
  uint8_t *out = malloc(n);
  if (!out) die("out of memory");
  for (uint64_t i = 0; i < n; i++)
    out[i] = (uint8_t)(hexdigit(s[2 * i]) << 4 | hexdigit(s[2 * i + 1]));
  return out;
}

static void expect(const char *want) {
  if (strcmp(tok(), want) != 0) {
    fprintf(stderr, "vrun: expected %s\n", want);
    exit(2);
  }
}

struct region { uint64_t base, len; uint8_t *data; };

static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y;
}

int main(void) {
  uint64_t page = (uint64_t)sysconf(_SC_PAGESIZE);
  expect("VRUN1");
  expect("code");
  uint64_t ncode = decnum(tok());
  uint8_t *code = hexbytes(ncode);
  expect("regs");
  uint64_t regs[16];
  for (int k = 0; k < 16; k++) regs[k] = hexword(tok());
  expect("res");
  uint64_t res = decnum(tok());
  if (res >= 16) die("result register out of range");

  struct region *rs = NULL;
  size_t nr = 0, cr = 0;
  for (;;) {
    const char *t = tok();
    if (strcmp(t, "end") == 0) break;
    if (strcmp(t, "region") != 0) die("expected region or end");
    if (nr == cr) {
      cr = cr ? 2 * cr : 8;
      rs = realloc(rs, cr * sizeof *rs);
      if (!rs) die("out of memory");
    }
    rs[nr].base = hexword(tok());
    rs[nr].len = decnum(tok());
    rs[nr].data = hexbytes(rs[nr].len);
    if (rs[nr].len && rs[nr].base + rs[nr].len < rs[nr].base) die("region wraps");
    nr++;
  }

  /* The set of pages meeting a region, mapped in maximal runs. */
  size_t np = 0, cp = 0;
  uint64_t *pages = NULL;
  for (size_t i = 0; i < nr; i++) {
    if (rs[i].len == 0) continue;
    for (uint64_t p = rs[i].base / page; p <= (rs[i].base + rs[i].len - 1) / page; p++) {
      if (np == cp) {
        cp = cp ? 2 * cp : 64;
        pages = realloc(pages, cp * sizeof *pages);
        if (!pages) die("out of memory");
      }
      pages[np++] = p;
    }
  }
  qsort(pages, np, sizeof *pages, cmp_u64);
  size_t i = 0;
  while (i < np) {
    size_t j = i;
    while (j + 1 < np && pages[j + 1] <= pages[j] + 1) j++;
    uint64_t lo = pages[i] * page, hi = (pages[j] + 1) * page;
    void *want = (void *)(uintptr_t)lo;
    void *got = mmap(want, hi - lo, PROT_READ | PROT_WRITE,
                     MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (got == MAP_FAILED) {
      fprintf(stderr, "vrun: cannot map [%#llx, %#llx): %s\n", (unsigned long long)lo,
              (unsigned long long)hi, strerror(errno));
      return 2;
    }
    if (got != want) {
      fprintf(stderr, "vrun: kernel placed [%#llx, %#llx) elsewhere\n",
              (unsigned long long)lo, (unsigned long long)hi);
      return 2;
    }
    i = j + 1;
  }
  for (size_t k = 0; k < nr; k++)
    if (rs[k].len) memcpy((void *)(uintptr_t)rs[k].base, rs[k].data, rs[k].len);

  /* Code pages followed by one data page holding the result and return-address slots. */
  uint64_t epi = 13;
  uint64_t codepages = (ncode + epi + page - 1) / page;
  if (codepages == 0) codepages = 1;
  uint8_t *cpg = mmap(NULL, (codepages + 1) * page, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (cpg == MAP_FAILED) die("cannot map code pages");
  for (size_t k = 0; k < nr; k++) {
    uint64_t b = rs[k].base, e = rs[k].base + rs[k].len;
    uint64_t cb = (uint64_t)(uintptr_t)cpg, ce = cb + (codepages + 1) * page;
    if (rs[k].len && b < ce && cb < e) die("code pages overlap a region");
  }
  if (ncode) memcpy(cpg, code, ncode);
  uint8_t *slots = cpg + codepages * page;
  uint8_t *p = cpg + ncode;
  /* mov %r<res>, resslot(%rip) */
  int32_t d1 = (int32_t)((slots + 0) - (p + 7));
  p[0] = (uint8_t)(0x48 | ((res >> 3) << 2));
  p[1] = 0x89;
  p[2] = (uint8_t)(((res & 7) << 3) | 5);
  memcpy(p + 3, &d1, 4);
  p += 7;
  /* jmp *retslot(%rip) */
  int32_t d2 = (int32_t)((slots + 8) - (p + 6));
  p[0] = 0xff;
  p[1] = 0x25;
  memcpy(p + 2, &d2, 4);
  uint64_t ret = (uint64_t)(uintptr_t)vrun_return;
  memcpy(slots + 8, &ret, 8);
  memset(slots, 0, 8);
  if (mprotect(cpg, codepages * page, PROT_READ | PROT_EXEC) != 0)
    die("cannot make the code executable");

  vrun_enter(regs, cpg);

  uint64_t result;
  memcpy(&result, slots, 8);
  printf("%d\n", result != 0);
  return 0;
}
