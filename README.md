# Verified native evaluation for Lean

A closed decidable proposition `P x` is proved in Lean in one of two ways. Kernel reduction
(`decide`, `decide +kernel`, `rfl`) trusts only the kernel, but it gets stuck on definitions
by well-founded recursion and on bodies that a `module` file does not expose, and on data of
realistic size it takes seconds to minutes. `native_decide` evaluates the decision procedure
with code produced by Lean's compiler and asserts the result by an auxiliary axiom
`e = true` (`Lean.Meta.nativeEqTrue`, since Lean v4.35.0); the trusted base then includes the
whole code generator and every definition the evaluation reaches.

This package replaces the second option by a chain whose only evaluated function is a fixed
x86 machine model. The decision procedure is compiled to x86-64 bytes by a compiler proved
correct once, for all programs; the bytes are decoded by a decoder with a proved round trip;
and the proposition follows from one run of the machine model on those bytes. The run is
evaluated by Lean's compiled code or by the host processor.

All declarations below live in the namespace `VerifiedEval`, and module paths are relative
to `VerifiedEval/`. The address-memory machine `runBlockA`, the encoder `encodeJBlock6` and
the decoder `decodeJStream6` with its round trip `roundtrip_block6` belong to the CatCrypt
verified compiler (package `catcrypt-compiler`), in the namespaces
`CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem`,
`CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms` and
`CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip`.

## What is proved

### The fragment

A decision procedure is written in a fragment of Lean (`Fragment.lean`): the grammar
`FExpr`, `FStmt`, `FProg` over fixed-width unsigned words, spans (fixed-capacity buffers of
fixed-width cells, standing for `Array UIntN`, `ByteArray` and ASCII strings) and tagged
values (standing for `Option UIntN`). Loops are bounded, by a literal trip count (`forLit`)
or by the length of a span (`forLen`); there is no `while`. The semantics `FExpr.eval`,
`FStmt.exec`, `FProg.run` is total by structural recursion, and the checker `FProg.wf`
rejects ill-scoped or ill-typed programs with a named `FragmentGap`.

`reifyFragment%` (`FragmentReflect.lean`) elaborates a Lean function over `UInt8`…`UInt64`,
bounded `Nat`, `Bool`, `Array UIntN`, `ByteArray` and `Option UIntN`, with bounded folds
(`List.range n |>.foldl`, `Nat.fold`), into an `FProg`. A head outside the surface is
rejected by an elaboration error naming the constant and the gap. `FragmentFixtures.lean`
pins one accepted and one rejected example per grammar constructor and per reifier head.

The transfer front (`Arena.lean`, `ArenaTransfer.lean`) relates statements over spec types
(`List`, ASCII `String`, `Option`, bounded `Nat`) to statements over a little-endian byte
arena, through the class `StmtTransfer` and registered value squares.
`substring_iff_spanSearch` is its instance for substring occurrence.

### The compilers

`compileProg` (`FragmentCompile.lean`) compiles the loop-free fragment to straight-line
`JInstr 64` code; `compileProgL` (`FragmentCompileLoop.lean`) extends it to the two loop
forms by guarded unrolling, with `forLen` unrolled to a static capacity and each copy guarded
by a length comparison. The emitted code has no branches: comparisons become `cmp` followed
by a conditional move, and `ite` and `matchTag` run every arm under a guard register.

Both compilers are proved correct once, over all programs in scope, against the
address-memory machine `runBlockA`. `compileProg_correct` and `compileProgL_correct` state
that, for a program in scope (`FProg.fits`, `FProg.fitsL`) and a machine state related to
the source state by `StateRel` (with loops, also span lengths within their capacities,
`CapOK`), the result temporary is nonzero after the compiled code exactly when `FProg.run`
answers `true`. The code length is `FStmt.codeSize` (`compileStmtL_length`), in which a
`forLit` loop contributes `n * (6 + body)` and a `forLen` loop `cap t * (10 + body)`
instructions. In the compiled layout every span cell is a 64-bit word, whatever its declared
width, and the register allocation has sixteen registers.

### Coverage and byte round trip

The encoder `encodeJBlock6` resolves register names through an allocation and writes x86-64
bytes; `Block6Roundtrip.lean` and `Block6RoundtripMem.lean` re-export the decoder
`decodeJStream6` and the round trip `roundtrip_block6` from the compiler package. In
`FragmentCoverageLoop.lean`:

- `compileProgL_covered`: every instruction the compiler emits is in the decoder's covered
  set `blockCovered6`.
- `compileProgL_roundtrip`: the `encodeJBlock6` bytes of a compiled program decode, by
  `decodeJStream6`, to the compiled block with every register name resolved through the
  allocation.
- `compileProgL_bytes_correct`: the block decoded from the bytes, run on a physical state
  related to the source state, leaves a nonzero value in the physical register of the result
  temporary exactly when `FProg.run` answers `true`. Its hypotheses are `AllocOK` (no
  temporary is allocated to `%rsp`), `RenInjOn` (the allocation is injective on the names
  the block mentions) and `FProg.litsFitL` (every literal is below `2 ^ 64`); `planCheck`
  discharges the first two for a concrete program.

### The machine answer and soundness

`machineAccepts` (`VerifiedDecide.lean`) decodes a byte stream with `decodeJStream6`, runs
the decoded block with `runBlockA`, and tests one register. It takes no program and no
decision procedure; a procedure enters only through its bytes and its initial state
`initState`. A `DecisionProc α P` packages a fragment program, its layout and register plan,
the side conditions of the compiler theorems, and a proof `spec` that the program answers
`true` on the state of `x` exactly when `P x`. `verifiedDecide_sound` derives `P x` from
`machineAccepts d.bytes d.code.length (d.init x) d.resReg = true` for an admissible `x`.

## The three tactics

The three tactics share the soundness theorem and differ in which evaluation is trusted.
The checker is the Lean kernel in each case.

### `verified_decide`: the machine model under Lean's compiler

`verified_decide d` closes `P x` for a concrete `x` by evaluating one application of
`machineAccepts` to the procedure's bytes, its code length and its initial state, and
asserting the result by an auxiliary axiom `machineAccepts … = true`, added by
`Lean.Meta.nativeEqTrue` as for `native_decide`. On a false instance it fails with the
message `verified_decide: the machine returned false on` followed by the evaluated term.

Lean's code generator evaluates the whole asserted term: the compiler `compileProgL`, the
encoder `encodeJBlock6`, the initial state, and then the decoder `decodeJStream6`, the
machine `runBlockA` and the register test. The correctness of the procedure, the compiler and
the encoder is covered by `verifiedDecide_sound`; their execution by Lean's code generator is
trusted, together with the machine's. The trusted code is therefore fixed (the same compiler,
encoder and machine for every check) but larger than the interpreter alone. The fidelity of
`runBlockA` to a real processor is not part of the trusted base, because the conclusion is
derived from the model's answer alone.

### `verified_decide_hw`: the bytes on the host processor

`machineAcceptsHW` (`VerifiedDecideHW.lean`) is, as a definition, `machineAccepts` on the
initial state (`machineAcceptsHW_eq`). Its implementation `machineAcceptsHWImpl` serialises
the code, the sixteen initial registers, the sink cell and every span cell into the input
format of the runner, which runs the bytes on the host processor and prints whether the
result register is nonzero. The implementation answers `false` without running when the
bytes do not decode or the runner fails. `verifiedDecideHW_sound` is the soundness theorem
and `verified_decide_hw d` the tactic. It adds the auxiliary axiom
`machineAcceptsHW … = true`.

The trusted evaluation is the host's execution of the bytes: the serialiser `vrunInput`
under Lean's compiler, the runner, the processor, and the agreement of the processor's
execution with `runBlockA` on the decoded block. This deployment therefore trusts the x86
machine model as a description of the processor, which `verified_decide` does not.

### `verified_decide_lit`: the machine answer on literal data

`VerifiedDecideLit.lean` restates the machine answer over raw natural-number literals:
`machineAcceptsNat code n regs regions res` runs the concatenated chunks of `code` from the
state `stateOfLit regs regions`, and `machineAcceptsNatD` adds a proof argument of
`codeDecodes code n`, because the processor runs any bytes while `machineAcceptsNat` is
`false` on bytes that do not decode. `stateOfLit_eq` and `machineAccepts_of_lit` connect the
literal state to `initState`. A `DecisionProcLit` carries the literal code (in chunks of 16
bytes, produced by `nat_chunks%`), the instruction count and the result register with
equations proved by `decide +kernel`, and `verifiedDecideLit_sound` is the soundness
theorem. The tactic `verified_decide_lit` adds the auxiliary axiom
`machineAcceptsNatD r₁ r₂ h r₄ r₅ r₆ = true`, one application of `machineAcceptsNatD` to five
raw literals and the decoding proof, and the
compiled implementation runs the bytes through the same runner as `verified_decide_hw`. The
five data arguments of the asserted term are built from natural-number literals,
`List.cons`, `List.nil` and `Prod.mk` only, so they are read without unfolding any
definition.

### Axioms and trusted bases

A proof by one of the three tactics depends on one auxiliary axiom per evaluated run, named
`<theorem>._native.<tactic>.ax_<k>` and stating that the evaluated term equals `true`, in
addition to the axioms of the procedure's own proofs. The three demos pin, by
`#print axioms` under `#guard_msgs`, the axiom list of their decided instance: `propext`,
`Classical.choice`, `Quot.sound` and the auxiliary axiom.

The lean4lean checker with its machine-evaluation rule (`--machine-eval`) re-checks an
auxiliary axiom of type `machineAcceptsNatD … = true` on raw literal arguments by running the
bytes through the runner, and rejects it when the runner does not answer `true`. Only
`verified_decide_lit` adds axioms of that shape. The axioms of `verified_decide` and
`verified_decide_hw` (`machineAccepts … = true`, `machineAcceptsHW … = true`) are accepted by
that checker as stated, like any `native_decide` axiom.

| Route | Evaluation trusted | Fidelity of the x86 model trusted |
|---|---|---|
| `native_decide` | the decision procedure compiled by Lean's code generator, with every `implemented_by` and `extern` replacement in its call graph, the C compiler and the runtime | no machine model |
| `verified_decide` | the fixed interpreter `machineAccepts`, with the compiler and encoder that produce its input, compiled by Lean's code generator | no |
| `verified_decide_hw` | the serialiser compiled by Lean, the runner and the host processor | yes |
| `verified_decide_lit` | the serialiser compiled by Lean, the runner and the host processor | yes |

In the three verified rows the fragment program, the compiler, the encoder and the decoder are
covered by proofs, and the statement `P` is connected to the program by the procedure's
`spec` field.

### Cost

The machine model represents registers and memory as closures, so the cost of a run grows
quadratically with the code length. One measured check comes from the compiler chain: a
length decoder for the instruction classes of the compiler's x86 output for `mpn_mul_1`,
written as a fragment program and run for 128 steps from offset `0`, ends exactly at the end
of the 360 encoded bytes. As thirteen `verified_decide` calls on an eight-step program, of
about 3,500 machine instructions each, joined by a composition lemma for step counts, the
check took about 9.3 s; the same statement by `decide +kernel` took 3.8–5.1 s. A single
program of 94,000 instructions took 582 s. On such checks the verified route removes the
decision procedure's code from the trusted base without saving time over kernel reduction.

## The runner

`runner/vrun.c` runs a block of x86-64 machine code on the host processor from a given
register file and memory image, and prints whether a chosen register is nonzero afterwards.
It maps every page that meets a region of the input at its fixed address with
`MAP_FIXED_NOREPLACE`, copies the code into fresh pages followed by an epilogue that saves the
result register and returns, loads all sixteen registers (including `%rsp`) and jumps to the
code. Its input format and calling convention are stated in the header of `runner/vrun.c`.
It runs on an x86-64 Linux host; the arena starts at address `2 ^ 20`, above the default
`mmap_min_addr`.

The runner path is the value of the environment variable `CATCRYPT_VRUN` when it is set, and
otherwise `vrunDefaultPath`: the absolute path of `runner/vrun` beside
`VerifiedDecideHW.lean`, recorded when that module was elaborated. A checkout that moves
after the build names its runner by `CATCRYPT_VRUN`.

```
cc -O2 -o VerifiedEval/runner/vrun VerifiedEval/runner/vrun.c
VerifiedEval/runner/test.sh
```

`runner/test.sh` builds the runner and checks it on hand-written byte sequences: register
moves, a load from the arena, a result in `%r12`, a fault on an unmapped address and the
refusal of a region below `mmap_min_addr`.

## Using it

The demos decide one instance of substring search, `IsSubstr ("hello world", "lo w")`.

`VerifiedDecideDemo.lean` defines the fragment program `substrProg` (haystack of at most 16
cells, needle of at most 4 cells, one 64-bit cell per character), its layout and register
plan, the specification `substr_spec`, and the registered procedure `substrDecide`.
`substr_hello` is proved by `verified_decide substrDecide`; the module pins its axiom list
and the failure message on the false instance `("hello world", "low")`.
`VerifiedDecideHWDemo.lean` proves `substr_hello_hw` by `verified_decide_hw substrDecide`,
and `VerifiedDecideLitDemo.lean` proves `substr_hello_lit` by
`verified_decide_lit substrDecideLit`. These two run the runner when they are elaborated, so
it is built first (see above) or named by `CATCRYPT_VRUN`.

```
lake build VerifiedEval.VerifiedDecideDemo
lake build VerifiedEval.VerifiedDecideHWDemo VerifiedEval.VerifiedDecideLitDemo
```

`Demos/VerifiedEvalDemo.lean` walks through the chain at `substrDecide` without evaluating
anything: `substrDecide_code_eq` and `substrDecide_bytes_eq` identify the procedure's code
and bytes as the output of `compileProgL` and `encodeJBlock6` on `substrProg`, and
`isSubstr_of_machineAccepts` instantiates `verifiedDecide_sound`, so that an accepting
machine run on those bytes proves `IsSubstr` for any admissible pair of strings. An auxiliary
axiom enters only where a tactic asserts a concrete run, as in `substr_hello`, which
`hello_lo_w` restates.

A new procedure needs a `DecisionProc`: the program (written as an `FProg` or produced by
`reifyFragment%`), a layout (`stdLayout`), a `RegPlan` that passes `planCheck`, the scope
facts `FProg.fitsL` and `FProg.litsFitL`, an admissibility test `admit` with its capacity
and length consequences, and the specification theorem. `substrDecide` fills every field
and is the template; `substrProg` is written directly as an `FProg`, and
`FragmentFixtures.lean` exercises the reifier.

## Building

The package uses Lean `v4.33.1` (`lean-toolchain`) and Mathlib `v4.33.1`. It requires four
packages of the CatCrypt workspace as local path dependencies, checked out next to this
directory: `catcrypt-compiler`, `CatCrypt-core`, `ParamTransfer` and `hax-lean`. Every
module is compiled with `-E hasSorry`, so a declaration whose proof reaches `sorryAx` is a
build error.

Inside the CatCrypt workspace the package is a path dependency of the top-level package
SSProve-lean, and every build runs from that package's root:

```
lake build VerifiedEval
```

Lake keys the freshness of a module on the whole `LEAN_PATH` of the build, so building the
same modules alternately from this directory and from the workspace root rebuilds them each
time; the workspace keeps one build root.

Standalone, with the four sibling packages next to this directory:

```
lake exe cache get
cc -O2 -o VerifiedEval/runner/vrun VerifiedEval/runner/vrun.c
lake build
```

`lake build` builds the umbrella module `VerifiedEval` and every module under
`VerifiedEval/`, the demos included.

## Licence

MIT; see `LICENSE`.
