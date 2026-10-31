/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.VerifiedDecide
public meta import VerifiedEval.VerifiedDecide
public import Lean

/-!
# Deciding a proposition by running the compiled bytes on the host CPU

`machineAcceptsHW L plan σ bytes n res` is, as a definition, `machineAccepts` on the initial
state `initState L plan σ`. Its compiled implementation `machineAcceptsHWImpl` runs the bytes
on the host x86-64 processor through the external runner `runner/vrun` (source
`runner/vrun.c` beside this file): it serialises the code, the sixteen initial registers,
the sink cell and the cells of every span of the layout at their addresses in the address
map of `VerifiedDecide`, and reads back whether the result register is nonzero.

The tactic `verified_decide_hw d` closes `P x` as `verified_decide d` does, except that the
auxiliary axiom it adds is `machineAcceptsHW … = true`. The trusted evaluation is then the
host processor's execution of the bytes, in place of the evaluation of the machine model.
The machine-evaluation rule of the lean4lean checker does not recognise this axiom and
accepts it as stated; `verified_decide_lit` produces the axiom that rule confirms.

## The runner

The runner path is the value of the environment variable `CATCRYPT_VRUN` when it is set,
and otherwise `vrunDefaultPath`, the absolute path of `runner/vrun` in the source tree that
elaborated this module. The runner is built by `cc -O2 -o runner/vrun runner/vrun.c`. Its
input format and calling convention are stated in the header of `runner/vrun.c`.

The implementation answers `false`, without running anything, when `decodeJStream6 n bytes`
fails (where `machineAccepts` also answers `false`) or when `res` is not one of the sixteen
register names; it answers `false` when the runner cannot be started, exits with a nonzero
status or prints anything other than `0` or `1`.

## Main definitions

* `vrunInput`: the runner input for a layout, plan, source state, code and result register.
* `machineAcceptsHW`, `machineAcceptsHWImpl`: the answer and its hardware implementation.
* `verified_decide_hw`: the tactic.

## Main results

* `machineAcceptsHW_eq`: `machineAcceptsHW` is `machineAccepts` on the initial state.
* `verifiedDecideHW_sound`: an accepting `machineAcceptsHW` run on the bytes of a
  registered procedure proves the proposition.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip (decodeJStream6)

/-! ## The runner input -/

/-- The lowercase hexadecimal digit of `d < 16`. -/
def hexDigit (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- The two hexadecimal digits of a byte value. -/
def hexByte (b : Nat) : String := String.ofList [hexDigit (b / 16 % 16), hexDigit (b % 16)]

/-- The hexadecimal digits of a natural number. -/
def hexNat (v : Nat) : String := String.ofList (Nat.toDigits 16 v)

/-- A byte string as hexadecimal digits, `-` when empty. -/
def hexBytes (bs : List Nat) : String :=
  if bs.isEmpty then "-" else String.join (bs.map hexByte)

/-- The eight little-endian bytes of a word. -/
def wordBytes (v : BitVec 64) : List Nat := (List.range 8).map fun j => v.toNat / 2 ^ (8 * j) % 256

/-- A `region` line of the runner input: base address, byte count and bytes. -/
def regionLine (base : BitVec 64) (bs : List Nat) : String :=
  s!"region {hexNat base.toNat} {bs.length} {hexBytes bs}\n"

/-- The runner input: the code bytes, the initial value of the sixteen registers of
`initRegs L plan σ`, the number of the result register, the zero sink cell at `sinkAddr`
and the cells of every span of the layout from `spanBase`. -/
def vrunInput (L : Layout) (plan : RegPlan) (σ : FState) (bytes : List (BitVec 8))
    (res : Nat) : String :=
  let regs := (List.range 16).map fun k => hexNat (initRegs L plan σ (regName k)).toNat
  "VRUN1\n" ++ s!"code {bytes.length} {hexBytes (bytes.map BitVec.toNat)}\n" ++
    "regs " ++ " ".intercalate regs ++ "\n" ++ s!"res {res}\n" ++
    regionLine sinkAddr (wordBytes 0) ++
    String.join (L.spans.map fun t => regionLine (spanBase L t) ((σ.bufs t).flatMap wordBytes)) ++
    "end\n"

/-! ## The runner location -/

/-- `vrun_source_path%` is the absolute path of `runner/vrun` in the directory of the source
file being elaborated. -/
syntax (name := vrunSourcePath) "vrun_source_path%" : term

open Lean Elab Term in
/-- The elaborator of `vrun_source_path%`. -/
@[term_elab vrunSourcePath] meta def elabVrunSourcePath : TermElab := fun _ _ => do
  let f : System.FilePath := ← getFileName
  let f ← if f.isAbsolute then pure f else do pure ((← IO.currentDir) / f)
  let dir := f.parent.getD "."
  return mkStrLit (dir / "runner" / "vrun").toString

/-- The absolute path of `runner/vrun` in the source tree that elaborated this module. -/
def vrunDefaultPath : String := vrun_source_path%

/-- Run the runner on an input and read its answer. -/
def runVrun (input : String) : IO Bool := do
  let path := (← IO.getEnv "CATCRYPT_VRUN").getD vrunDefaultPath
  let out ← IO.Process.output { cmd := path } (some input)
  if out.exitCode != 0 then
    throw (IO.userError s!"vrun: exit status {out.exitCode}: {out.stderr}")
  if out.stdout == "1\n" then return true
  if out.stdout == "0\n" then return false
  throw (IO.userError s!"vrun: unexpected output {out.stdout}")

/-! ## The answer on the host processor -/

/-- The hardware implementation of `machineAcceptsHW`: when `decodeJStream6 n bytes`
succeeds and `res` is a register name, the answer of the runner on
`vrunInput L plan σ bytes (gpNum res)`; `false` otherwise and on any runner failure. -/
unsafe def machineAcceptsHWImpl (L : Layout) (plan : RegPlan) (σ : FState)
    (bytes : List (BitVec 8)) (n : Nat) (res : String) : Bool :=
  match decodeJStream6 n bytes, gpNum? res with
  | some _, some k => unsafeBaseIO do
      match ← (runVrun (vrunInput L plan σ bytes k)).toBaseIO with
      | .ok b => pure b
      | .error _ => pure false
  | _, _ => false

/-- The machine model's answer on a byte stream from the initial state of a source state;
compiled code runs the bytes on the host processor through `machineAcceptsHWImpl`. -/
@[implemented_by machineAcceptsHWImpl]
def machineAcceptsHW (L : Layout) (plan : RegPlan) (σ : FState) (bytes : List (BitVec 8))
    (n : Nat) (res : String) : Bool :=
  machineAccepts bytes n (initState L plan σ) res

theorem machineAcceptsHW_eq (L : Layout) (plan : RegPlan) (σ : FState)
    (bytes : List (BitVec 8)) (n : Nat) (res : String) :
    machineAcceptsHW L plan σ bytes n res = machineAccepts bytes n (initState L plan σ) res :=
  rfl

/-- **Soundness of the hardware run.** For a registered procedure and an admissible input,
an accepting `machineAcceptsHW` run of the procedure's bytes from the input's initial state
proves the proposition. -/
theorem verifiedDecideHW_sound {α : Type} {P : α → Prop} (d : DecisionProc α P) (x : α)
    (ha : d.admit x = true)
    (h : machineAcceptsHW d.layout d.plan (d.toState x) d.bytes d.code.length d.resReg = true) :
    P x :=
  verifiedDecide_sound d x ha h

/-! ## The tactic -/

/-- `machine_accepts_hw` closes `machineAcceptsHW L plan σ bytes n res = true` for closed
arguments by running the bytes on the host processor and asserting the result by an
auxiliary axiom. -/
syntax (name := machineAcceptsHWTac) "machine_accepts_hw" : tactic

open Lean Elab Tactic in
/-- The elaborator of `machine_accepts_hw`. -/
@[tactic machineAcceptsHWTac] meta def evalMachineAcceptsHWTac : Tactic := fun _ => do
  evalMachineAccepts (← getMainGoal) ``machineAcceptsHW 6
  replaceMainGoal []

/-- `verified_decide_hw d` closes a goal `P x`, for a registered `d : DecisionProc α P` and
a concrete input `x`: it applies `verifiedDecideHW_sound d x`, decides admissibility of `x`
by `decide`, and closes the run by `machine_accepts_hw`. -/
macro "verified_decide_hw " d:term : tactic =>
  `(tactic| (refine verifiedDecideHW_sound $d _ (by decide) ?_; machine_accepts_hw))

end VerifiedEval

end
