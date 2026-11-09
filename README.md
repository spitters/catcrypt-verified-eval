# Verified native evaluation for Lean

Lean proves a closed decidable proposition `P x` in one of two ways. Kernel reduction
(`decide`, `decide +kernel`, `rfl`) trusts only the kernel, but it gets stuck on definitions
by well-founded recursion and on bodies that a `module` file does not expose, and on data of
realistic size it takes seconds to minutes. The tactic `native_decide` evaluates the decision
procedure with code from Lean's compiler and asserts the result by an auxiliary axiom
`e = true` (`Lean.Meta.nativeEqTrue`, since Lean v4.35.0). Its trusted base therefore includes
the whole code generator and every definition the evaluation reaches.

This package replaces `native_decide` by evaluation through fixed code: a compiler, an
encoder, a decoder and an x86 machine model, the same for every decision procedure. A
compiler proved correct for all programs of a fragment of Lean translates the procedure to
x86-64 bytes, a decoder with a proved round trip reads them back, and the proposition follows
from one run of the machine model on the decoded code. Lean's compiled code or the host
processor performs that run.

All declarations below are in the namespace `VerifiedEval`, and module paths are relative to
`VerifiedEval/`. The address-memory machine `runBlockA`, the encoder `encodeJBlock6` and the
decoder `decodeJStream6` with its round trip `roundtrip_block6` are part of the CatCrypt
verified compiler (package `catcrypt-compiler`), in the namespaces
`CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem`,
`CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms` and
`CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip`.

## Theorems

### The fragment

A decision procedure is a program of a fragment of Lean (`Fragment.lean`). The grammar
`FExpr`, `FStmt`, `FProg` has fixed-width unsigned words, spans and tagged values. A span is
a fixed-capacity buffer of fixed-width cells and models `Array UIntN`, `ByteArray` and ASCII
strings; a tagged value models `Option UIntN`. Every loop is bounded, by a literal trip count
(`forLit`) or by the length of a span (`forLen`), and the fragment has no `while`. The
semantics `FExpr.eval`, `FStmt.exec`, `FProg.run` is total by structural recursion, and the
checker `FProg.wf` rejects an ill-scoped or ill-typed program with a named `FragmentGap`.

The reifier `reifyFragment%` (`FragmentReflect.lean`) elaborates a Lean function into an
`FProg`. Its surface has `UInt8`…`UInt64`, bounded `Nat`, `Bool`, `Array UIntN`, `ByteArray`
and `Option UIntN`, with the bounded folds `List.range n |>.foldl` and `Nat.fold`. A head
outside the surface gives an elaboration error that names the constant and the gap. The
module `FragmentFixtures.lean` pins one accepted and one rejected example per grammar
constructor and per reifier head.

The transfer front (`Arena.lean`, `ArenaTransfer.lean`) relates a statement over
specification types (`List`, ASCII `String`, `Option`, bounded `Nat`) to a statement over a
little-endian byte arena, through the class `StmtTransfer` and registered value squares. Its
instance for substring occurrence is `substring_iff_spanSearch`.

### The compilers

The compiler `compileProg` (`FragmentCompile.lean`) translates the loop-free fragment to
straight-line `JInstr 64` code, and `compileProgL` (`FragmentCompileLoop.lean`) extends it to
the two loop forms by guarded unrolling. A `forLen` loop unrolls to a static capacity, with
each copy guarded by a length comparison. The emitted code has no branches: a comparison is a
`cmp` followed by a conditional move, and `ite` and `matchTag` run every arm under a guard
register.

Each compiler has one correctness theorem for every program in scope, against the
address-memory machine `runBlockA`. The theorems `compileProg_correct` and
`compileProgL_correct` take a program in scope (`FProg.fits`, `FProg.fitsL`) and a machine
state related to the source state by `StateRel`; with loops, the span lengths must also lie
within their capacities (`CapOK`). After the compiled code, the result temporary is nonzero
exactly when `FProg.run` answers `true`. The code length is `FStmt.codeSize`
(`compileStmtL_length`), to which a `forLit` loop contributes `n * (6 + body)` instructions
and a `forLen` loop `cap t * (10 + body)`. In the compiled layout every span cell is a 64-bit
word, whatever its declared width, and the register allocation has sixteen registers.

### Coverage and byte round trip

The encoder `encodeJBlock6` resolves register names through an allocation and writes x86-64
bytes. The modules `Block6Roundtrip.lean` and `Block6RoundtripMem.lean` re-export the decoder
`decodeJStream6` and the round trip `roundtrip_block6` from the compiler package. The module
`FragmentCoverageLoop.lean` proves three theorems:

- `compileProgL_covered`: every instruction the compiler emits is in the decoder's covered
  set `blockCovered6`.
- `compileProgL_roundtrip`: the `encodeJBlock6` bytes of a compiled program decode, by
  `decodeJStream6`, to the compiled block with every register name resolved through the
  allocation.
- `compileProgL_bytes_correct`: the block decoded from the bytes, run on a physical state
  related to the source state, leaves a nonzero value in the physical register of the result
  temporary exactly when `FProg.run` answers `true`. Its hypotheses are `AllocOK` (no
  temporary is allocated to `%rsp`), `RenInjOn` (the allocation is injective on the names
  the block mentions) and `FProg.litsFitL` (every literal is below `2 ^ 64`). For a concrete
  program, `planCheck` discharges the first two.

### The machine answer and soundness

The function `machineAccepts` (`VerifiedDecide.lean`) decodes a byte stream with
`decodeJStream6`, runs the decoded block with `runBlockA`, and tests one register. It takes
no program and no decision procedure: a procedure enters only through its bytes and its
initial state `initState`. A `DecisionProc α P` has a fragment program, its layout and
register plan, the side conditions of the compiler theorems, and a proof `spec` that the
program answers `true` on the state of `x` exactly when `P x`. The theorem
`verifiedDecide_sound` derives `P x` from
`machineAccepts d.bytes d.code.length (d.init x) d.resReg = true` for an admissible `x`.

## The three tactics

The three tactics rest on the theorems above and differ in which evaluation they trust. In
each case the Lean kernel checks the proof.

### `verified_decide`: the machine model under Lean's compiler

The tactic `verified_decide d` closes `P x` for a concrete `x`. It evaluates one application
of `machineAccepts` to the procedure's bytes, its code length and its initial state, and
asserts the result by an auxiliary axiom `machineAccepts … = true`, which
`Lean.Meta.nativeEqTrue` adds as for `native_decide`. On a false instance it fails with the
message `verified_decide: the machine returned false on`, followed by the evaluated term.

Lean's code generator evaluates the whole asserted term: the compiler `compileProgL`, the
encoder `encodeJBlock6` and the initial state, then the decoder `decodeJStream6`, the machine
`runBlockA` and the register test. The theorem `verifiedDecide_sound` covers the correctness
of the procedure, the compiler and the encoder; their execution by Lean's code generator is
trusted, as is the machine's. The trusted code is the same for every check, and it is larger
than the machine model alone. The trusted base excludes the fidelity of `runBlockA` to a real
processor, because the conclusion follows from the model's answer alone.

### `verified_decide_hw`: the bytes on the host processor

The definition `machineAcceptsHW` (`VerifiedDecideHW.lean`) equals `machineAccepts` on the
initial state (`machineAcceptsHW_eq`). Its implementation `machineAcceptsHWImpl` serialises
the code, the sixteen initial registers, the sink cell and every span cell into the input
format of the runner. The runner executes the bytes on the host processor and prints whether
the result register is nonzero. The implementation answers `false` without running when the
bytes do not decode or the runner fails. The soundness theorem is `verifiedDecideHW_sound`;
the tactic `verified_decide_hw d` adds the auxiliary axiom `machineAcceptsHW … = true`.

The trusted evaluation is the host's execution of the bytes: the serialiser `vrunInput`
under Lean's compiler, the runner, the processor, and the agreement of the processor's
execution with `runBlockA` on the decoded block. This tactic therefore trusts the x86
machine model as a description of the processor, and `verified_decide` does not.

### `verified_decide_lit`: the machine answer on literal data

The module `VerifiedDecideLit.lean` restates the machine answer over raw natural-number
literals. The function `machineAcceptsNat code n regs regions res` runs the concatenated
chunks of `code` from the state `stateOfLit regs regions`. The variant `machineAcceptsNatD`
takes a further proof of `codeDecodes code n`, because the processor runs any bytes, while
`machineAcceptsNat` is `false` on bytes that do not decode. The lemmas `stateOfLit_eq` and
`machineAccepts_of_lit` connect the literal state to `initState`.

A `DecisionProcLit` has the literal code in chunks of 16 bytes (produced by `nat_chunks%`),
the instruction count and the result register, with equations proved by `decide +kernel`.
Its soundness theorem is `verifiedDecideLit_sound`. The tactic `verified_decide_lit` adds the
auxiliary axiom `machineAcceptsNatD r₁ r₂ h r₄ r₅ r₆ = true`, one application of
`machineAcceptsNatD` to five raw literals and the decoding proof, and its compiled
implementation runs the bytes through the same runner as `verified_decide_hw`. The five data
arguments of the asserted term consist of natural-number literals, `List.cons`, `List.nil`
and `Prod.mk` only, so a checker reads them without unfolding any definition.

### Axioms and trusted bases

A proof by one of the three tactics depends on one auxiliary axiom per evaluated run, in
addition to the axioms of the procedure's own proofs. The axiom is named
`<theorem>._native.<tactic>.ax_<k>` and states that the evaluated term equals `true`. Each of
the three demos pins the axiom list of its decided instance by `#print axioms` under
`#guard_msgs`: `propext`, `Classical.choice`, `Quot.sound` and the auxiliary axiom.

The [lean4lean](https://github.com/spitters/lean4lean) checker has a
[machine-evaluation rule](https://github.com/spitters/lean4lean#machine-evaluation)
(`--machine-eval`, off by default). With it, the checker runs the bytes of an auxiliary axiom
of type `machineAcceptsNatD … = true` on raw literal arguments through the runner, and
rejects the axiom when the runner does not answer `true`. Only `verified_decide_lit` adds
axioms of that shape. The checker accepts the axioms of `verified_decide` and
`verified_decide_hw` (`machineAccepts … = true`, `machineAcceptsHW … = true`) as stated, like
any `native_decide` axiom.

| Tactic | Evaluation trusted | Fidelity of the x86 model trusted |
|---|---|---|
| `native_decide` | the decision procedure compiled by Lean's code generator, with every `implemented_by` and `extern` replacement in its call graph, the C compiler and the runtime | no machine model |
| `verified_decide` | the machine answer `machineAccepts`, with the compiler and encoder that produce its input, compiled by Lean's code generator | no |
| `verified_decide_hw` | the serialiser compiled by Lean, the runner and the host processor | yes |
| `verified_decide_lit` | the serialiser compiled by Lean, the runner and the host processor | yes |

For the three verified tactics, proofs cover the fragment program, the compiler, the encoder
and the decoder, and the procedure's `spec` field connects the statement `P` to the program.

### Cost

The machine model represents registers and memory as closures, so the cost of a run grows
quadratically with the code length. One measured check comes from the compiler: a length
decoder for the instruction classes of the compiler's x86 output for `mpn_mul_1`, written as
a fragment program and run for 128 steps from offset `0`, ends exactly at the end of the 360
encoded bytes. As thirteen `verified_decide` calls on an eight-step program of about 3,500
machine instructions, joined by a composition lemma for step counts, the check took about
9.3 s; the same statement by `decide +kernel` took 3.8–5.1 s. A single program of 94,000
instructions took 582 s. On such checks, `verified_decide` removes the decision procedure's
code from the trusted base and takes longer than kernel reduction.

## The runner

The runner `runner/vrun.c` executes a block of x86-64 machine code on the host processor from
a given register file and memory image, and prints whether a chosen register is nonzero
afterwards. It maps every page that meets a region of the input at its fixed address with
`MAP_FIXED_NOREPLACE` and copies the code into fresh pages, followed by an epilogue that saves
the result register and returns. It then loads all sixteen registers, `%rsp` included, and
jumps to the code. The header of `runner/vrun.c` states its input format and calling
convention. The runner needs an x86-64 Linux host; its arena starts at address `2 ^ 20`, above
the default `mmap_min_addr`.

The runner path is the value of the environment variable `CATCRYPT_VRUN` when it is set, and
otherwise `vrunDefaultPath`: the absolute path of `runner/vrun` beside
`VerifiedDecideHW.lean`, recorded when that module was elaborated. A checkout that moves
after the build names its runner by `CATCRYPT_VRUN`.

```
cc -O2 -o VerifiedEval/runner/vrun VerifiedEval/runner/vrun.c
VerifiedEval/runner/test.sh
```

The script `runner/test.sh` builds the runner and checks it on hand-written byte sequences:
register moves, a load from the arena, a result in `%r12`, a fault on an unmapped address and
the refusal of a region below `mmap_min_addr`.

## Usage

The demos decide one instance of substring search, `IsSubstr ("hello world", "lo w")`.

The module `VerifiedDecideDemo.lean` defines the fragment program `substrProg` (a haystack of
at most 16 cells and a needle of at most 4 cells, one 64-bit cell per character), its layout
and register plan, the specification `substr_spec` and the registered procedure
`substrDecide`. It proves `substr_hello` by `verified_decide substrDecide` and pins the axiom
list and the failure message on the false instance `("hello world", "low")`. The modules
`VerifiedDecideHWDemo.lean` and `VerifiedDecideLitDemo.lean` prove `substr_hello_hw` by
`verified_decide_hw substrDecide` and `substr_hello_lit` by
`verified_decide_lit substrDecideLit`. These two run the runner when they are elaborated, so
the runner is built first (see above) or named by `CATCRYPT_VRUN`.

```
lake build VerifiedEval.VerifiedDecideDemo
lake build VerifiedEval.VerifiedDecideHWDemo VerifiedEval.VerifiedDecideLitDemo
```

The module `Demos/VerifiedEvalDemo.lean` follows the chain at `substrDecide` without
evaluating anything. The theorems `substrDecide_code_eq` and `substrDecide_bytes_eq` identify
the procedure's code and bytes as the output of `compileProgL` and `encodeJBlock6` on
`substrProg`, and `isSubstr_of_machineAccepts` instantiates `verifiedDecide_sound`: an
accepting machine run on those bytes proves `IsSubstr` for any admissible pair of strings. An
auxiliary axiom enters only where a tactic asserts a concrete run, as in `substr_hello`, which
`hello_lo_w` restates.

A new procedure needs a `DecisionProc` with these fields: the program, written as an `FProg`
or produced by `reifyFragment%`; a layout (`stdLayout`); a `RegPlan` that passes
`planCheck`; the scope facts `FProg.fitsL` and `FProg.litsFitL`; an admissibility test
`admit` with its capacity and length consequences; and the specification theorem. The
procedure `substrDecide` fills every field and is the template. Its program `substrProg` is
written directly as an `FProg`; the fixtures in `FragmentFixtures.lean` exercise the reifier.

## Building

The package uses Lean `v4.35.0` (`lean-toolchain`) and Mathlib `v4.35.0`. It requires four
CatCrypt packages, `catcrypt-compiler`, `CatCrypt-core`, `ParamTransfer` and `hax-lean`, at
the revisions pinned in `lakefile.lean`. Every module is compiled with `-E hasSorry`, so a
declaration whose proof reaches `sorryAx` is a build error.

Lake fetches the four packages at their pinned revisions:

```
lake exe cache get
cc -O2 -o VerifiedEval/runner/vrun VerifiedEval/runner/vrun.c
lake build
```

The command `lake build` builds the umbrella module `VerifiedEval` and every module under
`VerifiedEval/`, the demos included.

In the CatCrypt development workspace the package is a local dependency of the top-level
package, and builds run from that package's root (`lake build VerifiedEval`). Lake keys the
freshness of a module on the whole `LEAN_PATH` of the build, so a second build root would
rebuild the same modules each time the root changes.

## Licence

MIT; see `LICENSE`.
