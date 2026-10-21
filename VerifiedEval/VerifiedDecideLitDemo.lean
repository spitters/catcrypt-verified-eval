/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.VerifiedDecideLit
public import VerifiedEval.VerifiedDecideDemo
public meta import VerifiedEval.VerifiedDecide
public meta import VerifiedEval.VerifiedDecideHW
public meta import VerifiedEval.VerifiedDecideLit
public meta import VerifiedEval.VerifiedDecideDemo
public meta import VerifiedEval.ArenaTransfer

/-!
# A substring search decided on literal data

`substrDecideLit` registers `substrDecide` with the byte values of its shipped bytes, its
instruction count and its result register number as raw literals, computed at elaboration
time by `nat_chunks%` and `nat_lits%`. The code is a list of chunks of `16` bytes; its
equation is `flatten_map_eq_of_chunksMatch` over a `chunksMatch` check by `decide +kernel`,
and the other two equations are checked by `decide +kernel`.

`substr_hello_lit` states the instance of `substr_hello` and is closed by
`verified_decide_lit substrDecideLit`: the asserted auxiliary definition is one application
of `machineAcceptsNatD` to raw literals and the decoding proof `substrDecideLit.decodes`, and the compiled evaluation runs the bytes on the host
processor through the runner `runner/vrun`, which must be built before this module is
elaborated (`cc -O2 -o runner/vrun runner/vrun.c` in this directory) or named by
`CATCRYPT_VRUN`.

## Main definitions

* `substrCodeLit`, `substrNLit`, `substrResLit`: the literal code, instruction count and
  result register number of `substrDecide`.
* `substrDecideLit`: the registered procedure with literal code.

## Main results

* `substrCodeLit_eq`, `substrNLit_eq`, `substrResLit_eq`: the literal equations.
* `substr_hello_lit`: `"lo w"` occurs in `"hello world"`, by `verified_decide_lit`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder (gpNum)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (regName)

/-! ## The literal code of the substring search -/

/-- The byte values of the shipped bytes of `substrDecide`, as raw literals in chunks of
`16`. -/
def substrCodeLit : List (List Nat) := nat_chunks% (substrDecide.bytes.map BitVec.toNat)

/-- The number of compiled instructions of `substrDecide`. -/
def substrNLit : Nat := nat_lits% substrDecide.code.length

/-- The SDM number of the result register of `substrDecide`. -/
def substrResLit : Nat := nat_lits% (gpNum substrDecide.resReg)

theorem substrCodeLit_eq : substrCodeLit.flatten.map (BitVec.ofNat 8) = substrDecide.bytes :=
  flatten_map_eq_of_chunksMatch _ _ (by decide +kernel)

theorem substrNLit_eq : substrDecide.code.length = substrNLit := by decide +kernel

theorem substrResLit_eq : regName substrResLit = substrDecide.resReg := by decide +kernel

/-- The substring search registered with its literal code. -/
def substrDecideLit : DecisionProcLit (String × String) IsSubstr where
  toDecisionProc := substrDecide
  codeLit := substrCodeLit
  nLit := substrNLit
  resLit := substrResLit
  code_eq := substrCodeLit_eq
  n_eq := substrNLit_eq
  res_eq := substrResLit_eq
  decodes := codeDecodes_of_eqs substrDecide substrCodeLit_eq substrNLit_eq

/-! ## Decided instances

The axiom list of `substr_hello_lit` is pinned as a static check that `verified_decide_lit`
contributes `Lean.ofReduceBool` and `Lean.trustCompiler` only. The false instance is pinned
as a static check of the tactic's failure message. -/

theorem substr_hello_lit : IsSubstr ("hello world", "lo w") := by
  verified_decide_lit substrDecideLit

/--
info: 'VerifiedEval.substr_hello_lit' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
-/
#guard_msgs in
#print axioms substr_hello_lit

/--
error: verified_decide_lit: the machine returned false on
  machineAcceptsNatD substrDecideLit.codeLit substrDecideLit.nLit ⋯
    (regsOf substrDecideLit.layout substrDecideLit.plan (substrDecideLit.toState ("hello world", "low")))
    (regionsOf substrDecideLit.layout substrDecideLit.plan (substrDecideLit.toState ("hello world", "low")))
    substrDecideLit.resLit
-/
#guard_msgs in
example : IsSubstr ("hello world", "low") := by verified_decide_lit substrDecideLit

end VerifiedEval

end
