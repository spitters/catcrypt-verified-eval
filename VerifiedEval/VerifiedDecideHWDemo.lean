/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.VerifiedDecideHW
public import VerifiedEval.VerifiedDecideDemo
public meta import VerifiedEval.VerifiedDecide
public meta import VerifiedEval.VerifiedDecideHW
public meta import VerifiedEval.VerifiedDecideDemo
public meta import VerifiedEval.ArenaTransfer

/-!
# A substring search decided on the host processor

`substr_hello_hw` states the instance of `substr_hello` and is closed by
`verified_decide_hw substrDecide`: the bytes of `substrDecide` run on the host processor
through the runner `runner/vrun`, which must be built before this module is elaborated
(`cc -O2 -o runner/vrun runner/vrun.c` in this directory) or named by `CATCRYPT_VRUN`.

## Main results

* `substr_hello_hw`: `"lo w"` occurs in `"hello world"`, by `verified_decide_hw`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

/-! ## Decided instances

The axiom list of `substr_hello_hw` is pinned as a static check that `verified_decide_hw`
contributes `Lean.ofReduceBool` and `Lean.trustCompiler` only. The false instance is pinned
as a static check of the tactic's failure message. -/

theorem substr_hello_hw : IsSubstr ("hello world", "lo w") := by
  verified_decide_hw substrDecide

/--
info: 'VerifiedEval.substr_hello_hw' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
-/
#guard_msgs in
#print axioms substr_hello_hw

/--
error: verified_decide: the machine returned false on
  machineAcceptsHW substrDecide.layout substrDecide.plan (substrDecide.toState ("hello world", "low"))
    substrDecide.bytes substrDecide.code.length substrDecide.resReg
-/
#guard_msgs in
example : IsSubstr ("hello world", "low") := by verified_decide_hw substrDecide

end VerifiedEval

end
