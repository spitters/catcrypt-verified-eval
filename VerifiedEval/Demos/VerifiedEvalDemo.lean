/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.VerifiedDecideDemo

/-!
# Verified evaluation: a worked example

This module walks through the links of the verified-evaluation chain on the registered
substring procedure `substrDecide` of `VerifiedEval/VerifiedDecideDemo.lean`. It runs no
evaluation of its own: every statement is a restatement or a composition of results proved
elsewhere, and the one decided instance is `substr_hello`, imported.

The chain has four links.

1. The fragment program `substrProg` is related to the proposition `IsSubstr` by the
   procedure's `spec` field, proved once for every admissible input (`substr_spec`).
2. The compiler `compileProgL` turns the program into `JInstr 64` code
   (`substrDecide_code_eq`), and the encoder `encodeJBlock6` turns that code into bytes
   (`substrDecide_bytes_eq`).
3. `compileProgL_bytes_correct` states that the block decoded from those bytes by
   `decodeJStream6` answers as the program does.
4. `machineAccepts` decodes the bytes, runs the block on the address-memory machine
   `runBlockA` and tests the result register. `verifiedDecide_sound` composes the three
   links before it, so an accepting run proves the proposition
   (`isSubstr_of_machineAccepts`).

`verified_decide substrDecide` evaluates the one Boolean `machineAccepts` term of link 4 on a
concrete input and asserts the answer through `Lean.ofReduceBool`.

## Main results

* `substrDecide_code_eq`, `substrDecide_bytes_eq`: the code and the bytes of the procedure
  are the compiler's and the encoder's output on `substrProg`.
* `isSubstr_of_machineAccepts`: for an admissible pair of strings, an accepting machine run
  on the bytes of `substrDecide` proves `IsSubstr`.
* `hello_lo_w`: `"lo w"` occurs in `"hello world"`, the instance decided by
  `verified_decide` in `substr_hello`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval.VerifiedEvalDemo

open VerifiedEval
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (encodeJBlock6)

/-- The code of `substrDecide` is `compileProgL` applied to its layout, its loop capacity and
`substrProg`. -/
theorem substrDecide_code_eq :
    substrDecide.code = compileProgL substrLayout (fun _ => 16) substrProg := rfl

/-- The bytes of `substrDecide` are `encodeJBlock6` applied to the allocation of its register
plan and its compiled code. -/
theorem substrDecide_bytes_eq :
    substrDecide.bytes = encodeJBlock6 (substrPlan.alloc substrLayout) substrDecide.code := rfl

/-- **The chain at the substring procedure.** For an admissible pair of strings, a run of the
machine model that decodes the bytes of `substrDecide` and leaves a nonzero value in its
result register proves that the second string occurs in the first. -/
theorem isSubstr_of_machineAccepts (x : String × String) (ha : substrAdmit x = true)
    (h : machineAccepts substrDecide.bytes substrDecide.code.length (substrDecide.init x)
      substrDecide.resReg = true) :
    IsSubstr x :=
  verifiedDecide_sound substrDecide x ha h

/-- `"lo w"` occurs in `"hello world"`: the instance decided by `verified_decide` in
`substr_hello`. -/
theorem hello_lo_w : IsSubstr ("hello world", "lo w") := substr_hello

end VerifiedEval.VerifiedEvalDemo

end
