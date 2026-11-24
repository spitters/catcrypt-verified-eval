/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.Fragment

/-!
# Correctness of reified fragment programs: judgments and per-construct lemmas

The statement that a fragment program computes a Lean function, and one lemma per
construct of the reifier's surface from which the statement is assembled.

A Lean value of a fragment scalar type is encoded as a 64-bit word by `FEnc.enc`: a word
`UIntN` by its value, `Nat` by its value modulo `2 ^ 64`, `Bool` by `0` or `1`. A span is
encoded as the list of its cells' encodings, an `Option` as the two-cell buffer
`[tag, payload]`.

A state `st` *agrees* with a scalar binding list `L` and a buffer binding list `B`
(`Agree L B st`) when every name bound in `L` (first binding wins) holds its word and every
name bound in `B` holds its buffer. The judgments are

* `ExprTo Γ L B pre e v L'`: from a state agreeing with `L`, the prelude `pre` reaches a
  state agreeing with `L'`; in any state agreeing with `L'` the expression `e` evaluates to
  `v`; and agreement with `L'` implies agreement with `L`;
* `StmtTo Γ L B s t v`: from a state agreeing with `L`, the statement `s` reaches a state
  agreeing with `(t, v) :: L`.

`StmtTo.run` turns a judgment about a program's body into the statement
`p.run st = b` for every `st` agreeing with the parameters' encodings: the form from which
the field `spec` of `DecisionProc` follows (`spec_of_run_eq`).

## Main definitions

* `FEnc`, `FWord`: encodings of scalar types and the arithmetic laws of the word types.
* `Agree`, `ExprTo`, `StmtTo`: the judgments.

## Main results

* `StmtTo.run`: a judgment about the body gives the program's answer.
* `spec_of_run_eq`: the `spec` field of a decision procedure from the program's answer and
  the link from the source function to the proposition.
* One lemma per construct (`ExprTo.add`, …, `StmtTo.foldlLit`, `StmtTo.matchSome`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval.Spec

open VerifiedEval

/-! ## Encodings -/

theorem mask_toNat (w : FWidth) (v : BitVec 64) : (v &&& w.mask).toNat = v.toNat % 2 ^ w.bits := by
  have hb : w.bits ≤ 64 := by cases w <;> decide
  have : w.mask.toNat = 2 ^ w.bits - 1 := by
    simp only [FWidth.mask, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hb
    omega
  rw [BitVec.toNat_and, this, Nat.and_two_pow_sub_one_eq_mod]

/-- The encoding of a fragment scalar type: its assignment width and the 64-bit word of a
value, which the mask of that width leaves unchanged. -/
class FEnc (α : Type) where
  /-- The width at which values of the type are assigned. -/
  w : FWidth
  /-- The word of a value. -/
  enc : α → BitVec 64
  enc_mask : ∀ a, enc a &&& w.mask = enc a

export FEnc (enc)

/-- The word types `UInt8` … `UInt64`: the fragment's operators at the type's width are the
encodings of Lean's operators. -/
class FWord (α : Type) [Add α] [Sub α] [Mul α] [AndOp α] [OrOp α] [XorOp α]
    [HShiftLeft α α α] [HShiftRight α α α] [LT α] [LE α] [Inhabited α] extends FEnc α where
  add : ∀ a b : α, enc (a + b) = (enc a + enc b) &&& w.mask
  sub : ∀ a b : α, enc (a - b) = (enc a - enc b) &&& w.mask
  mul : ∀ a b : α, enc (a * b) = (enc a * enc b) &&& w.mask
  and : ∀ a b : α, enc (a &&& b) = (enc a &&& enc b) &&& w.mask
  or : ∀ a b : α, enc (a ||| b) = (enc a ||| enc b) &&& w.mask
  xor : ∀ a b : α, enc (a ^^^ b) = (enc a ^^^ enc b) &&& w.mask
  shl : ∀ (a k : α) (n : Nat), n < w.bits → enc k = BitVec.ofNat 64 n →
    enc (a <<< k) = (enc a <<< n) &&& w.mask
  shr : ∀ (a k : α) (n : Nat), n < w.bits → enc k = BitVec.ofNat 64 n →
    enc (a >>> k) = (enc a >>> n) &&& w.mask
  inj : ∀ a b : α, enc a = enc b → a = b
  lt : ∀ a b : α, a < b ↔ enc a < enc b
  le : ∀ a b : α, a ≤ b ↔ enc a ≤ enc b
  dflt : enc (default : α) = 0

instance : FEnc Bool where
  w := .w8
  enc b := if b then 1 else 0
  enc_mask b := by cases b <;> decide

instance : FEnc Nat where
  w := .w64
  enc n := BitVec.ofNat 64 n
  enc_mask n := by
    apply BitVec.eq_of_toNat_eq; rw [mask_toNat]; simp [FWidth.bits, FWidth.bytes]

theorem enc_bool (b : Bool) : enc b = if b then 1 else 0 := rfl
theorem enc_nat (n : Nat) : enc n = BitVec.ofNat 64 n := rfl

theorem encUInt8_toNat (a : UInt8) : (BitVec.ofNat 64 a.toNat).toNat = a.toNat := by
  have := a.toNat_lt; simp; try omega

instance : FWord UInt8 where
  w := .w8
  enc a := BitVec.ofNat 64 a.toNat
  enc_mask a := by
    apply BitVec.eq_of_toNat_eq; rw [mask_toNat, encUInt8_toNat]; have := a.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  add a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_add, encUInt8_toNat, encUInt8_toNat, encUInt8_toNat, UInt8.toNat_add]
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  sub a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_sub, encUInt8_toNat, encUInt8_toNat, encUInt8_toNat, UInt8.toNat_sub]
    have := a.toNat_lt; have := b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  mul a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_mul, encUInt8_toNat, encUInt8_toNat, encUInt8_toNat, UInt8.toNat_mul]
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
    try rw [Nat.mod_mod_of_dvd _ (by decide)]
  and a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_and, encUInt8_toNat, encUInt8_toNat, encUInt8_toNat, UInt8.toNat_and]
    have := Nat.and_lt_two_pow (n := 8) a.toNat b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  or a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_or, encUInt8_toNat, encUInt8_toNat, encUInt8_toNat, UInt8.toNat_or]
    have := Nat.or_lt_two_pow (n := 8) a.toNat_lt b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  xor a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_xor, encUInt8_toNat, encUInt8_toNat, encUInt8_toNat, UInt8.toNat_xor]
    have := Nat.xor_lt_two_pow (n := 8) a.toNat_lt b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  shl a k n hn hk := by
    have hkn : k.toNat = n := by
      have := congrArg BitVec.toNat hk; rw [encUInt8_toNat] at this
      simp [FWidth.bits, FWidth.bytes] at hn this ⊢; omega
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_shiftLeft, encUInt8_toNat, encUInt8_toNat, UInt8.toNat_shiftLeft]
    simp [FWidth.bits, FWidth.bytes] at hn ⊢
    rw [hkn, Nat.mod_eq_of_lt (by omega : n < 8)]
    try simp [Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 2 ^ 64)]
  shr a k n hn hk := by
    have hkn : k.toNat = n := by
      have := congrArg BitVec.toNat hk; rw [encUInt8_toNat] at this
      simp [FWidth.bits, FWidth.bytes] at hn this ⊢; omega
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_ushiftRight, encUInt8_toNat, encUInt8_toNat, UInt8.toNat_shiftRight]
    simp [FWidth.bits, FWidth.bytes] at hn ⊢
    rw [hkn, Nat.mod_eq_of_lt (by omega : n < 8)]
    rw [Nat.shiftRight_eq_div_pow]
    have h1 : a.toNat / 2 ^ n < 2 ^ 8 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.toNat_lt
    first
      | rw [Nat.mod_eq_of_lt h1]
      | rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 (by decide))]
      | skip
    try simp [Nat.mod_eq_of_lt h1]
  inj a b h := by
    have := congrArg BitVec.toNat h; rw [encUInt8_toNat, encUInt8_toNat] at this
    exact UInt8.toNat_inj.mp this
  lt a b := by rw [BitVec.lt_def, encUInt8_toNat, encUInt8_toNat]; exact UInt8.lt_iff_toNat_lt
  le a b := by rw [BitVec.le_def, encUInt8_toNat, encUInt8_toNat]; exact UInt8.le_iff_toNat_le
  dflt := rfl

theorem encUInt16_toNat (a : UInt16) : (BitVec.ofNat 64 a.toNat).toNat = a.toNat := by
  have := a.toNat_lt; simp; try omega

instance : FWord UInt16 where
  w := .w16
  enc a := BitVec.ofNat 64 a.toNat
  enc_mask a := by
    apply BitVec.eq_of_toNat_eq; rw [mask_toNat, encUInt16_toNat]; have := a.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  add a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_add, encUInt16_toNat, encUInt16_toNat, encUInt16_toNat, UInt16.toNat_add]
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  sub a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_sub, encUInt16_toNat, encUInt16_toNat, encUInt16_toNat, UInt16.toNat_sub]
    have := a.toNat_lt; have := b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  mul a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_mul, encUInt16_toNat, encUInt16_toNat, encUInt16_toNat, UInt16.toNat_mul]
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
    try rw [Nat.mod_mod_of_dvd _ (by decide)]
  and a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_and, encUInt16_toNat, encUInt16_toNat, encUInt16_toNat, UInt16.toNat_and]
    have := Nat.and_lt_two_pow (n := 16) a.toNat b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  or a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_or, encUInt16_toNat, encUInt16_toNat, encUInt16_toNat, UInt16.toNat_or]
    have := Nat.or_lt_two_pow (n := 16) a.toNat_lt b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  xor a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_xor, encUInt16_toNat, encUInt16_toNat, encUInt16_toNat, UInt16.toNat_xor]
    have := Nat.xor_lt_two_pow (n := 16) a.toNat_lt b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  shl a k n hn hk := by
    have hkn : k.toNat = n := by
      have := congrArg BitVec.toNat hk; rw [encUInt16_toNat] at this
      simp [FWidth.bits, FWidth.bytes] at hn this ⊢; omega
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_shiftLeft, encUInt16_toNat, encUInt16_toNat, UInt16.toNat_shiftLeft]
    simp [FWidth.bits, FWidth.bytes] at hn ⊢
    rw [hkn, Nat.mod_eq_of_lt (by omega : n < 16)]
    try simp [Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 16 ∣ 2 ^ 64)]
  shr a k n hn hk := by
    have hkn : k.toNat = n := by
      have := congrArg BitVec.toNat hk; rw [encUInt16_toNat] at this
      simp [FWidth.bits, FWidth.bytes] at hn this ⊢; omega
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_ushiftRight, encUInt16_toNat, encUInt16_toNat, UInt16.toNat_shiftRight]
    simp [FWidth.bits, FWidth.bytes] at hn ⊢
    rw [hkn, Nat.mod_eq_of_lt (by omega : n < 16)]
    rw [Nat.shiftRight_eq_div_pow]
    have h1 : a.toNat / 2 ^ n < 2 ^ 16 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.toNat_lt
    first
      | rw [Nat.mod_eq_of_lt h1]
      | rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 (by decide))]
      | skip
    try simp [Nat.mod_eq_of_lt h1]
  inj a b h := by
    have := congrArg BitVec.toNat h; rw [encUInt16_toNat, encUInt16_toNat] at this
    exact UInt16.toNat_inj.mp this
  lt a b := by rw [BitVec.lt_def, encUInt16_toNat, encUInt16_toNat]; exact UInt16.lt_iff_toNat_lt
  le a b := by rw [BitVec.le_def, encUInt16_toNat, encUInt16_toNat]; exact UInt16.le_iff_toNat_le
  dflt := rfl

theorem encUInt32_toNat (a : UInt32) : (BitVec.ofNat 64 a.toNat).toNat = a.toNat := by
  have := a.toNat_lt; simp; try omega

instance : FWord UInt32 where
  w := .w32
  enc a := BitVec.ofNat 64 a.toNat
  enc_mask a := by
    apply BitVec.eq_of_toNat_eq; rw [mask_toNat, encUInt32_toNat]; have := a.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  add a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_add, encUInt32_toNat, encUInt32_toNat, encUInt32_toNat, UInt32.toNat_add]
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  sub a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_sub, encUInt32_toNat, encUInt32_toNat, encUInt32_toNat, UInt32.toNat_sub]
    have := a.toNat_lt; have := b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  mul a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_mul, encUInt32_toNat, encUInt32_toNat, encUInt32_toNat, UInt32.toNat_mul]
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
    try rw [Nat.mod_mod_of_dvd _ (by decide)]
  and a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_and, encUInt32_toNat, encUInt32_toNat, encUInt32_toNat, UInt32.toNat_and]
    have := Nat.and_lt_two_pow (n := 32) a.toNat b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  or a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_or, encUInt32_toNat, encUInt32_toNat, encUInt32_toNat, UInt32.toNat_or]
    have := Nat.or_lt_two_pow (n := 32) a.toNat_lt b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  xor a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_xor, encUInt32_toNat, encUInt32_toNat, encUInt32_toNat, UInt32.toNat_xor]
    have := Nat.xor_lt_two_pow (n := 32) a.toNat_lt b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  shl a k n hn hk := by
    have hkn : k.toNat = n := by
      have := congrArg BitVec.toNat hk; rw [encUInt32_toNat] at this
      simp [FWidth.bits, FWidth.bytes] at hn this ⊢; omega
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_shiftLeft, encUInt32_toNat, encUInt32_toNat, UInt32.toNat_shiftLeft]
    simp [FWidth.bits, FWidth.bytes] at hn ⊢
    rw [hkn, Nat.mod_eq_of_lt (by omega : n < 32)]
    try simp [Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]
  shr a k n hn hk := by
    have hkn : k.toNat = n := by
      have := congrArg BitVec.toNat hk; rw [encUInt32_toNat] at this
      simp [FWidth.bits, FWidth.bytes] at hn this ⊢; omega
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_ushiftRight, encUInt32_toNat, encUInt32_toNat, UInt32.toNat_shiftRight]
    simp [FWidth.bits, FWidth.bytes] at hn ⊢
    rw [hkn, Nat.mod_eq_of_lt (by omega : n < 32)]
    rw [Nat.shiftRight_eq_div_pow]
    have h1 : a.toNat / 2 ^ n < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.toNat_lt
    first
      | rw [Nat.mod_eq_of_lt h1]
      | rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 (by decide))]
      | skip
    try simp [Nat.mod_eq_of_lt h1]
  inj a b h := by
    have := congrArg BitVec.toNat h; rw [encUInt32_toNat, encUInt32_toNat] at this
    exact UInt32.toNat_inj.mp this
  lt a b := by rw [BitVec.lt_def, encUInt32_toNat, encUInt32_toNat]; exact UInt32.lt_iff_toNat_lt
  le a b := by rw [BitVec.le_def, encUInt32_toNat, encUInt32_toNat]; exact UInt32.le_iff_toNat_le
  dflt := rfl

theorem encUInt64_toNat (a : UInt64) : (BitVec.ofNat 64 a.toNat).toNat = a.toNat := by
  have := a.toNat_lt; simp; try omega

instance : FWord UInt64 where
  w := .w64
  enc a := BitVec.ofNat 64 a.toNat
  enc_mask a := by
    apply BitVec.eq_of_toNat_eq; rw [mask_toNat, encUInt64_toNat]; have := a.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  add a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_add, encUInt64_toNat, encUInt64_toNat, encUInt64_toNat, UInt64.toNat_add]
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  sub a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_sub, encUInt64_toNat, encUInt64_toNat, encUInt64_toNat, UInt64.toNat_sub]
    have := a.toNat_lt; have := b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  mul a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_mul, encUInt64_toNat, encUInt64_toNat, encUInt64_toNat, UInt64.toNat_mul]
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
    try rw [Nat.mod_mod_of_dvd _ (by decide)]
  and a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_and, encUInt64_toNat, encUInt64_toNat, encUInt64_toNat, UInt64.toNat_and]
    have := Nat.and_lt_two_pow (n := 64) a.toNat b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  or a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_or, encUInt64_toNat, encUInt64_toNat, encUInt64_toNat, UInt64.toNat_or]
    have := Nat.or_lt_two_pow (n := 64) a.toNat_lt b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  xor a b := by
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_xor, encUInt64_toNat, encUInt64_toNat, encUInt64_toNat, UInt64.toNat_xor]
    have := Nat.xor_lt_two_pow (n := 64) a.toNat_lt b.toNat_lt
    simp [FWidth.bits, FWidth.bytes] <;> (try omega)
  shl a k n hn hk := by
    have hkn : k.toNat = n := by
      have := congrArg BitVec.toNat hk; rw [encUInt64_toNat] at this
      simp [FWidth.bits, FWidth.bytes] at hn this ⊢; omega
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_shiftLeft, encUInt64_toNat, encUInt64_toNat, UInt64.toNat_shiftLeft]
    simp [FWidth.bits, FWidth.bytes] at hn ⊢
    rw [hkn, Nat.mod_eq_of_lt (by omega : n < 64)]
    try simp [Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 64 ∣ 2 ^ 64)]
  shr a k n hn hk := by
    have hkn : k.toNat = n := by
      have := congrArg BitVec.toNat hk; rw [encUInt64_toNat] at this
      simp [FWidth.bits, FWidth.bytes] at hn this ⊢; omega
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat, BitVec.toNat_ushiftRight, encUInt64_toNat, encUInt64_toNat, UInt64.toNat_shiftRight]
    simp [FWidth.bits, FWidth.bytes] at hn ⊢
    rw [hkn, Nat.mod_eq_of_lt (by omega : n < 64)]
    rw [Nat.shiftRight_eq_div_pow]
    have h1 : a.toNat / 2 ^ n < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.toNat_lt
    first
      | rw [Nat.mod_eq_of_lt h1]
      | rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 (by decide))]
      | skip
    try simp [Nat.mod_eq_of_lt h1]
  inj a b h := by
    have := congrArg BitVec.toNat h; rw [encUInt64_toNat, encUInt64_toNat] at this
    exact UInt64.toNat_inj.mp this
  lt a b := by rw [BitVec.lt_def, encUInt64_toNat, encUInt64_toNat]; exact UInt64.lt_iff_toNat_lt
  le a b := by rw [BitVec.le_def, encUInt64_toNat, encUInt64_toNat]; exact UInt64.le_iff_toNat_le
  dflt := rfl

/-! ## Buffers -/

/-- The cells of an array. -/
def encArr {α : Type} [FEnc α] (a : Array α) : List (BitVec 64) := a.toList.map enc

/-- The cells of a byte array. -/
def encBytes (b : ByteArray) : List (BitVec 64) := b.data.toList.map enc

/-- The `[tag, payload]` buffer of an optional value. -/
def encOpt {α : Type} [FEnc α] : Option α → List (BitVec 64)
  | none => [0, 0]
  | some a => [1, enc a]

/-! ## Judgments -/

/-- Scalar bindings: a name and its word; the first binding of a name counts. -/
abbrev SEnv := List (String × BitVec 64)

/-- Buffer bindings: a name and its cells. -/
abbrev BEnv := List (String × List (BitVec 64))

/-- The state holds the words of `L` and the buffers of `B`. -/
def Agree (L : SEnv) (B : BEnv) (st : FState) : Prop :=
  (∀ x v, L.lookup x = some v → st.scalars x = v) ∧ (∀ s b, B.lookup s = some b → st.bufs s = b)

/-- Every binding of `L` is a binding of `L'`, so agreement with `L'` implies agreement
with `L` (`Ext.agree`). -/
def Ext (L' L : SEnv) : Prop := ∀ y w, L.lookup y = some w → L'.lookup y = some w

/-- The prelude `pre` takes agreement with `L` to agreement with `L'`, in which the
expression `e` evaluates to `v`. -/
def ExprTo (Γ : String → FWidth) (L : SEnv) (B : BEnv) (pre : FStmt) (e : FExpr)
    (v : BitVec 64) (L' : SEnv) : Prop :=
  (∀ st, Agree L B st → Agree L' B (pre.exec Γ st)) ∧
    (∀ st, Agree L' B st → e.eval Γ st = v) ∧ Ext L' L

/-- The statement `s` takes agreement with `L` to agreement with `(t, v) :: L`. -/
def StmtTo (Γ : String → FWidth) (L : SEnv) (B : BEnv) (s : FStmt) (t : String)
    (v : BitVec 64) : Prop :=
  ∀ st, Agree L B st → Agree ((t, v) :: L) B (s.exec Γ st)

/-! ## Agreement -/

theorem lookup_cons (x y : String) (v : BitVec 64) (L : SEnv) :
    ((y, v) :: L).lookup x = if x = y then some v else L.lookup x := by
  simp only [List.lookup]
  by_cases h : x = y
  · subst h; simp
  · have : (x == y) = false := by simpa using h
    simp [this, h]

theorem lookup_none_of_contains {L : SEnv} {x : String}
    (h : (L.map Prod.fst).contains x = false) : L.lookup x = none := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨y, v⟩ := p
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff] at h
    have hne : x ≠ y := by intro e; subst e; simp at h
    rw [lookup_cons]; simp only [hne, ite_false]; exact ih h.2

theorem Agree.set {L : SEnv} {B : BEnv} {st : FState} (h : Agree L B st) (x : String)
    (v : BitVec 64) : Agree ((x, v) :: L) B (st.set x v) := by
  refine ⟨fun y w hy => ?_, fun s b hs => h.2 s b hs⟩
  rw [lookup_cons] at hy
  simp only [FState.set]
  by_cases hyx : y = x
  · simp_all
  · simp only [hyx, ite_false] at hy ⊢; exact h.1 y w hy

theorem Agree.setBufsEq {L : SEnv} {B : BEnv} {st st' : FState} (h : Agree L B st)
    (hb : st'.bufs = st.bufs) (hs : st'.scalars = st.scalars) : Agree L B st' := by
  obtain ⟨s1, b1⟩ := st; obtain ⟨s2, b2⟩ := st'
  simp only at hb hs; subst hb; subst hs; exact h

theorem Ext.agree {B : BEnv} {L' L : SEnv} {st : FState} (h : Ext L' L) (hst : Agree L' B st) :
    Agree L B st := ⟨fun y w hy => hst.1 y w (h y w hy), hst.2⟩

theorem Ext.refl (L : SEnv) : Ext L L := fun _ _ h => h

theorem Ext.trans {L1 L2 L3 : SEnv} (h12 : Ext L1 L2) (h23 : Ext L2 L3) : Ext L1 L3 :=
  fun y w h => h12 y w (h23 y w h)

theorem Ext.cons {L' L : SEnv} (p : String × BitVec 64) (h : Ext L' L) : Ext (p :: L') (p :: L) := by
  obtain ⟨x, v⟩ := p
  intro y w hy
  rw [lookup_cons] at hy ⊢
  by_cases hyx : y = x
  · simp_all
  · simp only [hyx, ite_false] at hy ⊢; exact h y w hy

theorem Ext.fresh {L : SEnv} {x : String} (v : BitVec 64) (h : (L.map Prod.fst).contains x = false) :
    Ext ((x, v) :: L) L := by
  intro y w hy
  rw [lookup_cons]
  by_cases hyx : y = x
  · subst hyx; rw [lookup_none_of_contains h] at hy; cases hy
  · simp only [hyx, ite_false]; exact hy

theorem Ext.drop {L : SEnv} (q p : String × BitVec 64)
    (h : (p.1 == q.1 || !(L.map Prod.fst).contains p.1) = true) : Ext (q :: p :: L) (q :: L) := by
  obtain ⟨x, v⟩ := q; obtain ⟨z, u⟩ := p
  intro y w hy
  rw [lookup_cons] at hy ⊢
  by_cases hyx : y = x
  · simp_all
  · simp only [hyx, ite_false] at hy ⊢
    rw [lookup_cons]
    by_cases hyz : y = z
    · subst hyz
      simp only [beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
      rcases h with h | h
      · exact absurd h hyx
      · rw [lookup_none_of_contains h] at hy; cases hy
    · simp only [hyz, ite_false]; exact hy

/-! ## Expressions: the general rules -/

section Rules

variable {Γ : String → FWidth} {L L' La Lb : SEnv} {B : BEnv}

theorem ExprTo.var {x : String} {v : BitVec 64} (h : L.lookup x = some v) :
    ExprTo Γ L B .skip (.var x) v L :=
  ⟨fun _ h => h, fun _ hst => hst.1 x v h, Ext.refl L⟩

theorem ExprTo.lit {n : Nat} {v : BitVec 64} (h : BitVec.ofNat 64 n = v) :
    ExprTo Γ L B .skip (.lit n) v L :=
  ⟨fun _ h => h, fun _ _ => h, Ext.refl L⟩

/-- A conditional, loop or match in expression position, assigned to the fresh local `x`. -/
theorem ExprTo.hoist {s : FStmt} {x : String} {v : BitVec 64} (h : StmtTo Γ L B s x v)
    (hx : (L.map Prod.fst).contains x = false) :
    ExprTo Γ L B s (.var x) v ((x, v) :: L) :=
  ⟨h, fun _ hst => hst.1 x v (by rw [lookup_cons]; simp), Ext.fresh v hx⟩

theorem ExprTo.bin {pa pb : FStmt} {fa fb : FExpr} {va vb v : BitVec 64} {op : FBinop}
    (ha : ExprTo Γ L B pa fa va La) (hb : ExprTo Γ La B pb fb vb Lb)
    (hv : (if op.isCompare then op.eval va vb
      else op.eval va vb &&& (((FExpr.bin op fa fb).width Γ).getD .w64).mask) = v) :
    ExprTo Γ L B (.seq pa pb) (.bin op fa fb) v Lb := by
  refine ⟨fun st h => hb.1 _ (ha.1 st h), fun st h => ?_, hb.2.2.trans ha.2.2⟩
  simp only [FExpr.eval]
  rw [ha.2.1 st (hb.2.2.agree h), hb.2.1 st h]
  exact hv

theorem ExprTo.binLit {pa : FStmt} {fa : FExpr} {va v : BitVec 64} {op : FBinop} {n : Nat}
    (ha : ExprTo Γ L B pa fa va La)
    (hv : (if op.isCompare then op.eval va (BitVec.ofNat 64 n)
      else op.eval va (BitVec.ofNat 64 n) &&&
        (((FExpr.bin op fa (.lit n)).width Γ).getD .w64).mask) = v) :
    ExprTo Γ L B pa (.bin op fa (.lit n)) v La := by
  refine ⟨ha.1, fun st h => ?_, ha.2.2⟩
  simp only [FExpr.eval]
  rw [ha.2.1 st h]
  exact hv

theorem ExprTo.not {pa : FStmt} {fa : FExpr} {va v : BitVec 64}
    (ha : ExprTo Γ L B pa fa va La) (hv : (if va = 0 then 1 else 0) = v) :
    ExprTo Γ L B pa (.not fa) v La := by
  refine ⟨ha.1, fun st h => ?_, ha.2.2⟩
  simp only [FExpr.eval]
  rw [ha.2.1 st h]
  exact hv

end Rules

/-! ## Booleans and propositions -/

section Bools

variable {Γ : String → FWidth} {L La Lb : SEnv} {B : BEnv} {pa pb : FStmt} {fa fb : FExpr}

theorem enc_ne_zero (b : Bool) : (enc b != 0) = b := by cases b <;> decide

theorem bool_and_mask (a b : Bool) (w : FWidth) : (enc a &&& enc b) &&& w.mask = enc (a && b) := by
  cases a <;> cases b <;> cases w <;> decide

theorem bool_or_mask (a b : Bool) (w : FWidth) : (enc a ||| enc b) &&& w.mask = enc (a || b) := by
  cases a <;> cases b <;> cases w <;> decide

theorem bool_xor_mask (a b : Bool) (w : FWidth) : (enc a ^^^ enc b) &&& w.mask = enc (xor a b) := by
  cases a <;> cases b <;> cases w <;> decide

theorem enc_decide (p : Prop) [Decidable p] :
    (if p then (1 : BitVec 64) else 0) = enc (decide p) := by
  by_cases h : p <;> simp [h, enc_bool]

theorem ExprTo.band {a b : Bool} (ha : ExprTo Γ L B pa fa (enc a) La)
    (hb : ExprTo Γ La B pb fb (enc b) Lb) :
    ExprTo Γ L B (.seq pa pb) (.bin .and fa fb) (enc (a && b)) Lb :=
  ExprTo.bin ha hb (by simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false,
    bool_and_mask])

theorem ExprTo.bor {a b : Bool} (ha : ExprTo Γ L B pa fa (enc a) La)
    (hb : ExprTo Γ La B pb fb (enc b) Lb) :
    ExprTo Γ L B (.seq pa pb) (.bin .or fa fb) (enc (a || b)) Lb :=
  ExprTo.bin ha hb (by simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false,
    bool_or_mask])

theorem ExprTo.bxor {a b : Bool} (ha : ExprTo Γ L B pa fa (enc a) La)
    (hb : ExprTo Γ La B pb fb (enc b) Lb) :
    ExprTo Γ L B (.seq pa pb) (.bin .xor fa fb) (enc (xor a b)) Lb :=
  ExprTo.bin ha hb (by simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false,
    bool_xor_mask])

theorem ExprTo.bnot {a : Bool} (ha : ExprTo Γ L B pa fa (enc a) La) :
    ExprTo Γ L B pa (.not fa) (enc (!a)) La :=
  ExprTo.not ha (by cases a <;> decide)

theorem ExprTo.bbeq {inst : BEq Bool} [LawfulBEq Bool] {a b : Bool}
    (ha : ExprTo Γ L B pa fa (enc a) La) (hb : ExprTo Γ La B pb fb (enc b) Lb) :
    ExprTo Γ L B (.seq pa pb) (.bin .eq fa fb) (enc (a == b)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, ite_true]
    cases a <;> cases b <;> simp [enc_bool])

theorem ExprTo.bbne {inst : BEq Bool} [LawfulBEq Bool] {a b : Bool}
    (ha : ExprTo Γ L B pa fa (enc a) La) (hb : ExprTo Γ La B pb fb (enc b) Lb) :
    ExprTo Γ L B (.seq pa pb) (.not (.bin .eq fa fb)) (enc (a != b)) Lb :=
  ExprTo.not (ExprTo.bbeq ha hb) (by cases a <;> cases b <;> simp [enc_bool])

theorem ExprTo.bdeq {a b : Bool} {i : Decidable (a = b)}
    (ha : ExprTo Γ L B pa fa (enc a) La) (hb : ExprTo Γ La B pb fb (enc b) Lb) :
    ExprTo Γ L B (.seq pa pb) (.bin .eq fa fb) (enc (@decide (a = b) i)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, ite_true]
    cases a <;> cases b <;> simp [enc_bool])

theorem ExprTo.pand {p q : Prop} {ip : Decidable p} {iq : Decidable q} {i : Decidable (p ∧ q)}
    (ha : ExprTo Γ L B pa fa (enc (@decide p ip)) La)
    (hb : ExprTo Γ La B pb fb (enc (@decide q iq)) Lb) :
    ExprTo Γ L B (.seq pa pb) (.bin .and fa fb) (enc (@decide (p ∧ q) i)) Lb := by
  have := ExprTo.band ha hb
  rwa [show (@decide p ip && @decide q iq) = @decide (p ∧ q) i by
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]] at this

theorem ExprTo.por {p q : Prop} {ip : Decidable p} {iq : Decidable q} {i : Decidable (p ∨ q)}
    (ha : ExprTo Γ L B pa fa (enc (@decide p ip)) La)
    (hb : ExprTo Γ La B pb fb (enc (@decide q iq)) Lb) :
    ExprTo Γ L B (.seq pa pb) (.bin .or fa fb) (enc (@decide (p ∨ q) i)) Lb := by
  have := ExprTo.bor ha hb
  rwa [show (@decide p ip || @decide q iq) = @decide (p ∨ q) i by
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]] at this

theorem ExprTo.pnot {p : Prop} {ip : Decidable p} {i : Decidable (¬p)}
    (ha : ExprTo Γ L B pa fa (enc (@decide p ip)) La) :
    ExprTo Γ L B pa (.not fa) (enc (@decide (¬p) i)) La := by
  have := ExprTo.bnot ha
  rwa [show (!@decide p ip) = @decide (¬p) i by by_cases hp : p <;> simp [hp]] at this

/-- A `Bool` used as a proposition `c = true`. -/
theorem ExprTo.ptrue {e : FExpr} {c : Bool} {i : Decidable (c = true)}
    (ha : ExprTo Γ L B pa e (enc c) La) :
    ExprTo Γ L B pa e (enc (@decide (c = true) i)) La := by
  rwa [show @decide (c = true) i = c by cases c <;> simp]

theorem ExprTo.bne' {a b : Bool} {i : Decidable (a ≠ b)}
    (ha : ExprTo Γ L B pa fa (enc a) La) (hb : ExprTo Γ La B pb fb (enc b) Lb) :
    ExprTo Γ L B (.seq pa pb) (.not (.bin .eq fa fb)) (enc (@decide (a ≠ b) i)) Lb :=
  ExprTo.pnot (ExprTo.bdeq (i := inferInstance) ha hb)

end Bools

/-! ## Words -/

section Words

variable {Γ : String → FWidth} {L La Lb : SEnv} {B : BEnv} {pa pb : FStmt} {fa fb : FExpr}
variable {α : Type} [Add α] [Sub α] [Mul α] [AndOp α] [OrOp α] [XorOp α]
  [HShiftLeft α α α] [HShiftRight α α α] [LT α] [LE α] [Inhabited α] [FWord α]

/-- The width side condition of an arithmetic operator. -/
abbrev WidthIs (Γ : String → FWidth) (e : FExpr) (w : FWidth) : Prop :=
  (e.width Γ).getD .w64 = w

theorem ExprTo.add {x y : α} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hw : WidthIs Γ (.bin .add fa fb) (FEnc.w α)) :
    ExprTo Γ L B (.seq pa pb) (.bin .add fa fb) (enc (x + y)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false]
    rw [hw, FWord.add])

theorem ExprTo.sub {x y : α} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hw : WidthIs Γ (.bin .sub fa fb) (FEnc.w α)) :
    ExprTo Γ L B (.seq pa pb) (.bin .sub fa fb) (enc (x - y)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false]
    rw [hw, FWord.sub])

theorem ExprTo.mul {x y : α} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hw : WidthIs Γ (.bin .mul fa fb) (FEnc.w α)) :
    ExprTo Γ L B (.seq pa pb) (.bin .mul fa fb) (enc (x * y)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false]
    rw [hw, FWord.mul])

theorem ExprTo.wand {x y : α} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hw : WidthIs Γ (.bin .and fa fb) (FEnc.w α)) :
    ExprTo Γ L B (.seq pa pb) (.bin .and fa fb) (enc (x &&& y)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false]
    rw [hw, FWord.and])

theorem ExprTo.wor {x y : α} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hw : WidthIs Γ (.bin .or fa fb) (FEnc.w α)) :
    ExprTo Γ L B (.seq pa pb) (.bin .or fa fb) (enc (x ||| y)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false]
    rw [hw, FWord.or])

theorem ExprTo.wxor {x y : α} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hw : WidthIs Γ (.bin .xor fa fb) (FEnc.w α)) :
    ExprTo Γ L B (.seq pa pb) (.bin .xor fa fb) (enc (x ^^^ y)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false]
    rw [hw, FWord.xor])

theorem ExprTo.shl {x k : α} {n : Nat} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hk : enc k = BitVec.ofNat 64 n) (hn : n < (FEnc.w α).bits)
    (hw : WidthIs Γ (.bin .shl fa (.lit n)) (FEnc.w α)) :
    ExprTo Γ L B pa (.bin .shl fa (.lit n)) (enc (x <<< k)) La :=
  ExprTo.binLit ha (by
    simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false]
    rw [hw, FWord.shl x k n hn hk]
    congr 2
    have : n < 2 ^ 64 := Nat.lt_trans hn (by cases (FEnc.w α) <;> decide)
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this])

theorem ExprTo.shr {x k : α} {n : Nat} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hk : enc k = BitVec.ofNat 64 n) (hn : n < (FEnc.w α).bits)
    (hw : WidthIs Γ (.bin .shr fa (.lit n)) (FEnc.w α)) :
    ExprTo Γ L B pa (.bin .shr fa (.lit n)) (enc (x >>> k)) La :=
  ExprTo.binLit ha (by
    simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false]
    rw [hw, FWord.shr x k n hn hk]
    congr 2
    have : n < 2 ^ 64 := Nat.lt_trans hn (by cases (FEnc.w α) <;> decide)
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this])

theorem ExprTo.wdeq {x y : α} {i : Decidable (x = y)} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) :
    ExprTo Γ L B (.seq pa pb) (.bin .eq fa fb) (enc (@decide (x = y) i)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, ite_true]
    by_cases h : x = y
    · subst h; simp [enc_bool]
    · have : enc x ≠ enc y := fun e => h (FWord.inj _ _ e)
      simp [h, this, enc_bool])

theorem ExprTo.wbeq [BEq α] [LawfulBEq α] {x y : α} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) :
    ExprTo Γ L B (.seq pa pb) (.bin .eq fa fb) (enc (x == y)) Lb := by
  have := ExprTo.wdeq (i := instDecidableEqOfLawfulBEq x y) ha hb
  rwa [show @decide (x = y) (instDecidableEqOfLawfulBEq x y) = (x == y) by
    cases h : x == y <;> simp_all] at this

theorem ExprTo.wbne [BEq α] [LawfulBEq α] {x y : α} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) :
    ExprTo Γ L B (.seq pa pb) (.not (.bin .eq fa fb)) (enc (x != y)) Lb :=
  ExprTo.not (ExprTo.wbeq ha hb) (by cases h : x == y <;> simp [h, bne, enc_bool])

theorem ExprTo.wne {x y : α} {i : Decidable (x ≠ y)} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) :
    ExprTo Γ L B (.seq pa pb) (.not (.bin .eq fa fb)) (enc (@decide (x ≠ y) i)) Lb :=
  ExprTo.pnot (ExprTo.wdeq (i := Classical.propDecidable _) ha hb)

theorem ExprTo.wlt {x y : α} {i : Decidable (x < y)} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) :
    ExprTo Γ L B (.seq pa pb) (.bin .lt fa fb) (enc (@decide (x < y) i)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, ite_true]
    by_cases h : x < y
    · simp [h, (FWord.lt x y).mp h, enc_bool]
    · have : ¬ enc x < enc y := fun e => h ((FWord.lt x y).mpr e)
      simp [h, this, enc_bool])

theorem ExprTo.wle {x y : α} {i : Decidable (x ≤ y)} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) :
    ExprTo Γ L B (.seq pa pb) (.bin .ule fa fb) (enc (@decide (x ≤ y) i)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, ite_true]
    by_cases h : x ≤ y
    · simp [h, (FWord.le x y).mp h, enc_bool]
    · have : ¬ enc x ≤ enc y := fun e => h ((FWord.le x y).mpr e)
      simp [h, this, enc_bool])

theorem ExprTo.wgt {x y : α} {i : Decidable (x > y)} (hb : ExprTo Γ L B pb fb (enc y) Lb)
    (ha : ExprTo Γ Lb B pa fa (enc x) La) :
    ExprTo Γ L B (.seq pb pa) (.bin .lt fb fa) (enc (@decide (x > y) i)) La :=
  ExprTo.wlt hb ha

theorem ExprTo.wge {x y : α} {i : Decidable (x ≥ y)} (hb : ExprTo Γ L B pb fb (enc y) Lb)
    (ha : ExprTo Γ Lb B pa fa (enc x) La) :
    ExprTo Γ L B (.seq pb pa) (.bin .ule fb fa) (enc (@decide (x ≥ y) i)) La :=
  ExprTo.wle hb ha

end Words

/-! ## `Nat` as a 64-bit word -/

section Nats

variable {Γ : String → FWidth} {L La Lb : SEnv} {B : BEnv} {pa pb : FStmt} {fa fb : FExpr}

theorem enc_nat_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : enc x = enc y ↔ x = y := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [enc_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
    exact this
  · rintro rfl; rfl

theorem enc_nat_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : enc x < enc y ↔ x < y := by
  simp only [enc_nat, BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem enc_nat_le {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : enc x ≤ enc y ↔ x ≤ y := by
  simp only [enc_nat, BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem ExprTo.nadd {x y : Nat} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hw : WidthIs Γ (.bin .add fa fb) .w64) :
    ExprTo Γ L B (.seq pa pb) (.bin .add fa fb) (enc (x + y)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, Bool.false_eq_true, ite_false]
    rw [hw]
    apply BitVec.eq_of_toNat_eq
    rw [mask_toNat]
    simp [enc_nat, FWidth.bits, FWidth.bytes, BitVec.toNat_add])

theorem ExprTo.ndeq {x y : Nat} {i : Decidable (x = y)} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    ExprTo Γ L B (.seq pa pb) (.bin .eq fa fb) (enc (@decide (x = y) i)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, ite_true]
    by_cases h : x = y
    · subst h; simp [enc_bool]
    · have : enc x ≠ enc y := fun e => h ((enc_nat_inj hx hy).mp e)
      simp [h, this, enc_bool])

theorem ExprTo.nbeq {x y : Nat} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    ExprTo Γ L B (.seq pa pb) (.bin .eq fa fb) (enc (x == y)) Lb := by
  have := ExprTo.ndeq (i := inferInstance) ha hb hx hy
  rwa [show decide (x = y) = (x == y) by cases h : x == y <;> simp_all] at this

theorem ExprTo.nbne {x y : Nat} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    ExprTo Γ L B (.seq pa pb) (.not (.bin .eq fa fb)) (enc (x != y)) Lb :=
  ExprTo.not (ExprTo.nbeq ha hb hx hy) (by cases h : x == y <;> simp [h, bne, enc_bool])

theorem ExprTo.nne {x y : Nat} {i : Decidable (x ≠ y)} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    ExprTo Γ L B (.seq pa pb) (.not (.bin .eq fa fb)) (enc (@decide (x ≠ y) i)) Lb :=
  ExprTo.pnot (ExprTo.ndeq (i := inferInstance) ha hb hx hy)

theorem ExprTo.nlt {x y : Nat} {i : Decidable (x < y)} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    ExprTo Γ L B (.seq pa pb) (.bin .lt fa fb) (enc (@decide (x < y) i)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, ite_true]
    by_cases h : x < y
    · simp [h, (enc_nat_lt hx hy).mpr h, enc_bool]
    · have : ¬ enc x < enc y := fun e => h ((enc_nat_lt hx hy).mp e)
      simp [h, this, enc_bool])

theorem ExprTo.nle {x y : Nat} {i : Decidable (x ≤ y)} (ha : ExprTo Γ L B pa fa (enc x) La)
    (hb : ExprTo Γ La B pb fb (enc y) Lb) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    ExprTo Γ L B (.seq pa pb) (.bin .ule fa fb) (enc (@decide (x ≤ y) i)) Lb :=
  ExprTo.bin ha hb (by
    simp only [FBinop.isCompare, FBinop.eval, ite_true]
    by_cases h : x ≤ y
    · simp [h, (enc_nat_le hx hy).mpr h, enc_bool]
    · have : ¬ enc x ≤ enc y := fun e => h ((enc_nat_le hx hy).mp e)
      simp [h, this, enc_bool])

theorem ExprTo.ngt {x y : Nat} {i : Decidable (x > y)} (hb : ExprTo Γ L B pb fb (enc y) Lb)
    (ha : ExprTo Γ Lb B pa fa (enc x) La) (hy : y < 2 ^ 64) (hx : x < 2 ^ 64) :
    ExprTo Γ L B (.seq pb pa) (.bin .lt fb fa) (enc (@decide (x > y) i)) La :=
  ExprTo.nlt hb ha hy hx

theorem ExprTo.nge {x y : Nat} {i : Decidable (x ≥ y)} (hb : ExprTo Γ L B pb fb (enc y) Lb)
    (ha : ExprTo Γ Lb B pa fa (enc x) La) (hy : y < 2 ^ 64) (hx : x < 2 ^ 64) :
    ExprTo Γ L B (.seq pb pa) (.bin .ule fb fa) (enc (@decide (x ≥ y) i)) La :=
  ExprTo.nle hb ha hy hx

end Nats

/-! ## Spans and tagged values -/

section Buffers

variable {Γ : String → FWidth} {L L' : SEnv} {B : BEnv} {pi : FStmt} {fi : FExpr} {s : String}
variable {α : Type} [Add α] [Sub α] [Mul α] [AndOp α] [OrOp α] [XorOp α]
  [HShiftLeft α α α] [HShiftRight α α α] [LT α] [LE α] [Inhabited α] [FWord α]

theorem getD_map_enc (l : List α) (i : Nat) : (l.map enc).getD i 0 = enc (l.getD i default) := by
  induction l generalizing i with
  | nil => simp [FWord.dflt]
  | cons a l ih => cases i <;> simp_all

omit [Add α] [Sub α] [Mul α] [AndOp α] [OrOp α] [XorOp α] [HShiftLeft α α α] [HShiftRight α α α]
  [LT α] [LE α] [FWord α] in
theorem getElem!_eq_getD (a : Array α) (i : Nat) : a[i]! = a.toList.getD i default := by
  simp only [getElem!_def, Array.getElem?_toList, List.getD_eq_getElem?_getD]
  cases a[i]? <;> rfl

theorem ExprTo.sizeArr {β : Type} [FEnc β] {a : Array β} (hs : B.lookup s = some (encArr a)) :
    ExprTo Γ L B .skip (.spanLen s) (enc a.size) L :=
  ⟨fun _ h => h, fun st h => by simp [FExpr.eval, h.2 s _ hs, encArr, enc_nat], Ext.refl L⟩

theorem ExprTo.sizeBytes {b : ByteArray} (hs : B.lookup s = some (encBytes b)) :
    ExprTo Γ L B .skip (.spanLen s) (enc b.size) L :=
  ⟨fun _ h => h, fun st h => by
    simp only [FExpr.eval, h.2 s _ hs, encBytes, enc_nat, List.length_map, Array.length_toList]
    rfl, Ext.refl L⟩

theorem ExprTo.getArr {a : Array α} {i : Nat} (hi : ExprTo Γ L B pi fi (enc i) L')
    (hs : B.lookup s = some (encArr a)) (hb : i < 2 ^ 64) :
    ExprTo Γ L B pi (.spanGet s fi) (enc a[i]!) L' := by
  refine ⟨hi.1, fun st h => ?_, hi.2.2⟩
  simp only [FExpr.eval]
  rw [hi.2.1 st h, (hi.2.2.agree h).2 s _ hs, enc_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb,
    encArr, getD_map_enc, getElem!_eq_getD]

theorem ExprTo.getBytes {b : ByteArray} {i : Nat} (hi : ExprTo Γ L B pi fi (enc i) L')
    (hs : B.lookup s = some (encBytes b)) (hb : i < 2 ^ 64) :
    ExprTo Γ L B pi (.spanGet s fi) (enc (b.get! i)) L' := by
  refine ⟨hi.1, fun st h => ?_, hi.2.2⟩
  simp only [FExpr.eval]
  rw [hi.2.1 st h, (hi.2.2.agree h).2 s _ hs, enc_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb,
    encBytes, getD_map_enc]
  show _ = enc b.data[i]!
  rw [getElem!_eq_getD]

theorem ExprTo.isSome {β : Type} [FEnc β] {o : Option β} (hs : B.lookup s = some (encOpt o)) :
    ExprTo Γ L B .skip (.bin .eq (.tagOf s) (.lit 1)) (enc o.isSome) L :=
  ⟨fun _ h => h, fun st h => by
    cases o <;> simp [FExpr.eval, h.2 s _ hs, encOpt, FBinop.isCompare, FBinop.eval, enc_bool],
    Ext.refl L⟩

theorem ExprTo.isNone {β : Type} [FEnc β] {o : Option β} (hs : B.lookup s = some (encOpt o)) :
    ExprTo Γ L B .skip (.bin .eq (.tagOf s) (.lit 0)) (enc o.isNone) L :=
  ⟨fun _ h => h, fun st h => by
    cases o <;> simp [FExpr.eval, h.2 s _ hs, encOpt, FBinop.isCompare, FBinop.eval, enc_bool],
    Ext.refl L⟩

theorem ExprTo.payload {β : Type} [FEnc β] {o : Option β} {v : β}
    (hs : B.lookup s = some (encOpt o)) (ho : o = some v) :
    ExprTo Γ L B .skip (.payload s) (enc v) L :=
  ⟨fun _ h => h, fun st h => by subst ho; simp [FExpr.eval, h.2 s _ hs, encOpt], Ext.refl L⟩

end Buffers

/-! ## Conversions between `UInt64` and `Nat` -/

section Conversions

variable {Γ : String → FWidth} {L L' : SEnv} {B : BEnv} {pa : FStmt} {fa : FExpr}

/-- `UInt64.toNat` is the identity on the word. -/
theorem ExprTo.toNat64 {a : UInt64} (ha : ExprTo Γ L B pa fa (enc a) L') :
    ExprTo Γ L B pa fa (enc a.toNat) L' := ha

/-- `Nat.toUInt64` is the identity on the word. -/
theorem ExprTo.ofNat64 {n : Nat} (ha : ExprTo Γ L B pa fa (enc n) L') :
    ExprTo Γ L B pa fa (enc n.toUInt64) L' := by
  have : enc n.toUInt64 = enc n := by
    apply BitVec.eq_of_toNat_eq
    simp [FEnc.enc, Nat.toUInt64]
  rwa [this]

/-- A read of an array at a `UInt64` index converted to `Nat`: no bound is needed. -/
theorem ExprTo.getArrU64 {α : Type} [Add α] [Sub α] [Mul α] [AndOp α] [OrOp α] [XorOp α]
    [HShiftLeft α α α] [HShiftRight α α α] [LT α] [LE α] [Inhabited α] [FWord α] {s : String}
    {a : Array α} {k : UInt64} (hi : ExprTo Γ L B pa fa (enc k) L')
    (hs : B.lookup s = some (encArr a)) :
    ExprTo Γ L B pa (.spanGet s fa) (enc a[k.toNat]!) L' :=
  ExprTo.getArr (ExprTo.toNat64 hi) hs k.toNat_lt

end Conversions

/-! ## Statements -/

section Stmts

variable {Γ : String → FWidth} {L L' : SEnv} {B : BEnv} {t : String}

theorem StmtTo.expr {β : Type} [FEnc β] {pre : FStmt} {fe : FExpr} {a : β}
    (h : ExprTo Γ L B pre fe (enc a) L') (hw : Γ t = FEnc.w β) :
    StmtTo Γ L B (.seq pre (.assign t fe)) t (enc a) := by
  intro st hst
  have h1 := h.1 st hst
  simp only [FStmt.exec]
  rw [h.2.1 _ h1, hw, FEnc.enc_mask]
  exact (Ext.cons _ h.2.2).agree (h1.set t (enc a))

theorem StmtTo.letE {α β : Type} [FEnc α] [FEnc β] {s1 s2 : FStmt} {x : String} {a : α}
    {b : α → β} (h1 : StmtTo Γ L B s1 x (enc a))
    (h2 : StmtTo Γ ((x, enc a) :: L) B s2 t (enc (b a)))
    (hx : (x == t || !(L.map Prod.fst).contains x) = true) :
    StmtTo Γ L B (.seq s1 s2) t (enc (b a)) := by
  intro st hst
  exact (Ext.drop (t, _) (x, _) hx).agree (h2 _ (h1 st hst))

/-- A `let` of a decidable proposition, held as a boolean local. -/
theorem StmtTo.letProp {β : Type} [FEnc β] {s1 s2 : FStmt} {x : String} {p : Prop}
    [i : Decidable p] {b : Prop → β} (h1 : StmtTo Γ L B s1 x (enc (@decide p i)))
    (h2 : StmtTo Γ ((x, enc (@decide p i)) :: L) B s2 t (enc (b p)))
    (hx : (x == t || !(L.map Prod.fst).contains x) = true) :
    StmtTo Γ L B (.seq s1 s2) t (enc (b p)) := by
  intro st hst
  exact (Ext.drop (t, _) (x, _) hx).agree (h2 _ (h1 st hst))

theorem StmtTo.ite {β : Type} [FEnc β] {pre st se : FStmt} {c : FExpr} {p : Prop}
    {i : Decidable p} {a b : β} (hc : ExprTo Γ L B pre c (enc (@decide p i)) L')
    (ht : StmtTo Γ L' B st t (enc a)) (he : StmtTo Γ L' B se t (enc b)) :
    StmtTo Γ L B (.seq pre (.ite c st se)) t (enc (@ite β p i a b)) := by
  intro σ hσ
  have h1 := hc.1 σ hσ
  have hcv := hc.2.1 _ h1
  simp only [FStmt.exec]
  by_cases hp : p
  · have : c.eval Γ (pre.exec Γ σ) ≠ 0 := by rw [hcv]; simp [hp, enc_bool]
    simp only [this, hp, ite_false, ite_true]
    exact (Ext.cons _ hc.2.2).agree (ht _ h1)
  · have : c.eval Γ (pre.exec Γ σ) = 0 := by rw [hcv]; simp [hp, enc_bool]
    simp only [this, hp, ite_false, ite_true]
    exact (Ext.cons _ hc.2.2).agree (he _ h1)

theorem StmtTo.cond {β : Type} [FEnc β] {pre st se : FStmt} {c : FExpr} {cb : Bool} {a b : β}
    (hc : ExprTo Γ L B pre c (enc cb) L')
    (ht : StmtTo Γ L' B st t (enc a)) (he : StmtTo Γ L' B se t (enc b)) :
    StmtTo Γ L B (.seq pre (.ite c st se)) t (enc (_root_.cond cb a b)) := by
  have := StmtTo.ite (p := cb = true) (i := inferInstance) (a := a) (b := b)
    (by rwa [show decide (cb = true) = cb by cases cb <;> rfl]) ht he
  rwa [show (if cb = true then a else b) = _root_.cond cb a b by cases cb <;> rfl] at this

theorem StmtTo.getD {β : Type} [FEnc β] {s : String} {sd : FStmt} {o : Option β} {d : β}
    (hs : B.lookup s = some (encOpt o)) (hw : Γ t = FEnc.w β) (hd : StmtTo Γ L B sd t (enc d)) :
    StmtTo Γ L B (.ite (.bin .eq (.tagOf s) (.lit 1)) (.assign t (.payload s)) sd) t
      (enc (o.getD d)) := by
  intro σ hσ
  cases o with
  | none =>
    have : (FExpr.bin .eq (.tagOf s) (.lit 1)).eval Γ σ = 0 := by
      simp [FExpr.eval, hσ.2 s _ hs, encOpt, FBinop.isCompare, FBinop.eval]
    simp only [FStmt.exec, this, ite_true, Option.getD_none]
    exact hd σ hσ
  | some v =>
    have : (FExpr.bin .eq (.tagOf s) (.lit 1)).eval Γ σ ≠ 0 := by
      simp [FExpr.eval, hσ.2 s _ hs, encOpt, FBinop.isCompare, FBinop.eval]
    simp only [FStmt.exec, this, ite_false, Option.getD_some]
    have hp : (FExpr.payload s).eval Γ σ = enc v := by simp [FExpr.eval, hσ.2 s _ hs, encOpt]
    rw [hp, hw, FEnc.enc_mask]
    exact hσ.set t (enc v)

theorem StmtTo.matchSome {α β : Type} [FEnc α] [FEnc β] {s : String} {arm dflt : FStmt}
    {o : Option α} {D : β} {A : α → β} (hs : B.lookup s = some (encOpt o))
    (hd : StmtTo Γ L B dflt t (enc D)) (ha : ∀ v, o = some v → StmtTo Γ L B arm t (enc (A v))) :
    StmtTo Γ L B (.matchTag s [(1, arm)] dflt) t
      (enc (@Option.casesOn α (fun _ => β) o D A)) := by
  intro σ hσ
  cases o with
  | none =>
    simp only [FStmt.exec, hσ.2 s _ hs, encOpt, FStmt.execArms]
    exact hd σ hσ
  | some v =>
    simp only [FStmt.exec, hσ.2 s _ hs, encOpt, FStmt.execArms]
    exact ha v rfl σ hσ

/-! ### Loops -/

theorem loop_step {β : Type} [FEnc β] {i : String} {body : FStmt} {acc acc' : β} {k : Nat}
    {σ : FState} (hi : (t :: L.map Prod.fst).contains i = false)
    (hb : StmtTo Γ ((i, enc k) :: (t, enc acc) :: L) B body t (enc acc'))
    (hσ : Agree ((t, enc acc) :: L) B σ) :
    Agree ((t, enc acc') :: L) B (body.exec Γ (σ.set i (BitVec.ofNat 64 k))) := by
  have h1 := hb _ (hσ.set i (enc k))
  have hd1 : (i == t || !(((t, enc acc) :: L).map Prod.fst).contains i) = true := by
    simp only [List.contains_cons, Bool.or_eq_false_iff] at hi
    simp only [List.map_cons, List.contains_cons, hi.1, hi.2, Bool.or_false, Bool.not_false,
      Bool.or_true]
  have h2 := (Ext.drop (t, enc acc') (i, enc k) hd1).agree h1
  exact (Ext.drop (t, enc acc') (t, enc acc) (by simp)).agree h2

theorem loop_foldl {β : Type} [FEnc β] {i : String} {body : FStmt} {g : β → Nat → β} {n : Nat}
    (hi : (t :: L.map Prod.fst).contains i = false)
    (hb : ∀ (acc : β) (k : Nat), k < n →
      StmtTo Γ ((i, enc k) :: (t, enc acc) :: L) B body t (enc (g acc k))) :
    ∀ (l : List Nat), (∀ k ∈ l, k < n) → ∀ (acc : β) (σ : FState), Agree ((t, enc acc) :: L) B σ →
      Agree ((t, enc (l.foldl g acc)) :: L) B
        (l.foldl (fun σ k => body.exec Γ (σ.set i (BitVec.ofNat 64 k))) σ) := by
  intro l
  induction l with
  | nil => intro _ acc σ h; exact h
  | cons k l ih =>
    intro hl acc σ h
    simp only [List.foldl_cons]
    exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ _
      (loop_step hi (hb acc k (hl k List.mem_cons_self)) h)

theorem StmtTo.foldlLit {β : Type} [FEnc β] {s0 body : FStmt} {i : String} {n : Nat}
    {init : β} {g : β → Nat → β} (h0 : StmtTo Γ L B s0 t (enc init))
    (hb : ∀ (acc : β) (k : Nat), k < n →
      StmtTo Γ ((i, enc k) :: (t, enc acc) :: L) B body t (enc (g acc k)))
    (hi : (t :: L.map Prod.fst).contains i = false) :
    StmtTo Γ L B (.seq s0 (.forLit i n body)) t (enc ((List.range n).foldl g init)) := by
  intro σ hσ
  simp only [FStmt.exec]
  exact loop_foldl hi hb _ (fun k hk => List.mem_range.mp hk) _ _ (h0 σ hσ)

theorem StmtTo.foldlArr {α β : Type} [FEnc α] [FEnc β] {s0 body : FStmt} {i s : String}
    {a : Array α} {init : β} {g : β → Nat → β} (hs : B.lookup s = some (encArr a))
    (h0 : StmtTo Γ L B s0 t (enc init))
    (hb : ∀ (acc : β) (k : Nat), k < a.size →
      StmtTo Γ ((i, enc k) :: (t, enc acc) :: L) B body t (enc (g acc k)))
    (hi : (t :: L.map Prod.fst).contains i = false) :
    StmtTo Γ L B (.seq s0 (.forLen i s body)) t (enc ((List.range a.size).foldl g init)) := by
  intro σ hσ
  have h1 := h0 σ hσ
  simp only [FStmt.exec, h1.2 s _ hs, encArr, List.length_map, Array.length_toList]
  exact loop_foldl hi hb _ (fun k hk => List.mem_range.mp hk) _ _ h1

theorem StmtTo.foldlBytes {β : Type} [FEnc β] {s0 body : FStmt} {i s : String}
    {a : ByteArray} {init : β} {g : β → Nat → β} (hs : B.lookup s = some (encBytes a))
    (h0 : StmtTo Γ L B s0 t (enc init))
    (hb : ∀ (acc : β) (k : Nat), k < a.size →
      StmtTo Γ ((i, enc k) :: (t, enc acc) :: L) B body t (enc (g acc k)))
    (hi : (t :: L.map Prod.fst).contains i = false) :
    StmtTo Γ L B (.seq s0 (.forLen i s body)) t (enc ((List.range a.size).foldl g init)) := by
  intro σ hσ
  have h1 := h0 σ hσ
  simp only [FStmt.exec, h1.2 s _ hs, encBytes, List.length_map, Array.length_toList]
  exact loop_foldl hi hb _ (fun k hk => List.mem_range.mp hk) _ _ h1

theorem loop_natFold {β : Type} [FEnc β] {i : String} {body : FStmt} {n : Nat}
    {f : (k : Nat) → k < n → β → β} (hi : (t :: L.map Prod.fst).contains i = false)
    (hb : ∀ (acc : β) (k : Nat) (hk : k < n),
      StmtTo Γ ((i, enc k) :: (t, enc acc) :: L) B body t (enc (f k hk acc)))
    (init : β) (σ : FState) (hσ : Agree ((t, enc init) :: L) B σ) :
    ∀ m (hm : m ≤ n), Agree ((t, enc (Nat.fold m (fun k hk => f k (Nat.lt_of_lt_of_le hk hm)) init))
      :: L) B ((List.range m).foldl (fun σ k => body.exec Γ (σ.set i (BitVec.ofNat 64 k))) σ) := by
  intro m
  induction m with
  | zero => intro _; simpa using hσ
  | succ m ih =>
    intro hm
    rw [Nat.fold_succ, List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact loop_step hi (hb _ m (by omega)) (ih (by omega))

theorem StmtTo.natFoldLit {β : Type} [FEnc β] {s0 body : FStmt} {i : String} {n : Nat}
    {init : β} {f : (k : Nat) → k < n → β → β} (h0 : StmtTo Γ L B s0 t (enc init))
    (hb : ∀ (acc : β) (k : Nat) (hk : k < n),
      StmtTo Γ ((i, enc k) :: (t, enc acc) :: L) B body t (enc (f k hk acc)))
    (hi : (t :: L.map Prod.fst).contains i = false) :
    StmtTo Γ L B (.seq s0 (.forLit i n body)) t (enc (Nat.fold n f init)) := by
  intro σ hσ
  simp only [FStmt.exec]
  exact loop_natFold hi hb init _ (h0 σ hσ) n (Nat.le_refl n)

theorem StmtTo.natFoldArr {α β : Type} [FEnc α] [FEnc β] {s0 body : FStmt} {i s : String}
    {a : Array α} {init : β} {f : (k : Nat) → k < a.size → β → β}
    (hs : B.lookup s = some (encArr a)) (h0 : StmtTo Γ L B s0 t (enc init))
    (hb : ∀ (acc : β) (k : Nat) (hk : k < a.size),
      StmtTo Γ ((i, enc k) :: (t, enc acc) :: L) B body t (enc (f k hk acc)))
    (hi : (t :: L.map Prod.fst).contains i = false) :
    StmtTo Γ L B (.seq s0 (.forLen i s body)) t (enc (Nat.fold a.size f init)) := by
  intro σ hσ
  have h1 := h0 σ hσ
  simp only [FStmt.exec, h1.2 s _ hs, encArr, List.length_map, Array.length_toList]
  exact loop_natFold hi hb init _ h1 a.size (Nat.le_refl _)

theorem StmtTo.natFoldBytes {β : Type} [FEnc β] {s0 body : FStmt} {i s : String}
    {a : ByteArray} {init : β} {f : (k : Nat) → k < a.size → β → β}
    (hs : B.lookup s = some (encBytes a)) (h0 : StmtTo Γ L B s0 t (enc init))
    (hb : ∀ (acc : β) (k : Nat) (hk : k < a.size),
      StmtTo Γ ((i, enc k) :: (t, enc acc) :: L) B body t (enc (f k hk acc)))
    (hi : (t :: L.map Prod.fst).contains i = false) :
    StmtTo Γ L B (.seq s0 (.forLen i s body)) t (enc (Nat.fold a.size f init)) := by
  intro σ hσ
  have h1 := h0 σ hσ
  have hlen : (encBytes a).length = a.size := by simp [encBytes]
  simp only [FStmt.exec, h1.2 s _ hs, hlen]
  exact loop_natFold hi hb init _ h1 a.size (Nat.le_refl _)

end Stmts

/-! ## Programs -/

/-- The state holding exactly the bindings `L` and `B`, every other scalar `0` and every other
buffer empty. -/
def stateOfEnv (L : SEnv) (B : BEnv) : FState where
  scalars x := (L.lookup x).getD 0
  bufs s := (B.lookup s).getD []

theorem agree_stateOfEnv (L : SEnv) (B : BEnv) : Agree L B (stateOfEnv L B) :=
  ⟨fun x v h => by simp [stateOfEnv, h], fun s b h => by simp [stateOfEnv, h]⟩

/-- **The correctness statement.** A judgment that the body leaves the encoding of `b` in the
result local gives the program's answer `b` on every state agreeing with the bindings. -/
theorem StmtTo.run {p : FProg} {L : SEnv} {B : BEnv} {r : String} {b : Bool}
    (hr : p.result = .var r) (h : StmtTo p.widths L B p.body r (enc b)) :
    ∀ st, Agree L B st → p.run st = b := by
  intro st hst
  have := (h st hst).1 r (enc b) (by simp [List.lookup])
  simp only [FProg.run, hr, FExpr.eval, this, enc_ne_zero]

/-- The field `spec` of a decision procedure from the program's answer on admissible inputs
(`StmtTo.run`) and the link from the source function to the proposition. -/
theorem spec_of_run_eq {α : Type} {P : α → Prop} {p : FProg} {toState : α → FState}
    {admit : α → Bool} (f : α → Bool) (hrun : ∀ x, admit x = true → p.run (toState x) = f x)
    (hf : ∀ x, admit x = true → (f x = true ↔ P x)) :
    ∀ x, admit x = true → (p.run (toState x) = true ↔ P x) := by
  intro x hx
  rw [hrun x hx]
  exact hf x hx

end VerifiedEval.Spec

end
