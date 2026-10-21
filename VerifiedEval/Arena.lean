/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Init

/-!
# Byte arena for verified evaluation

The byte arena through which a verified evaluation route passes a decision
procedure's input into emitted x86 code and reads a result byte back.
Every multi-byte quantity is little-endian.

* **Word view**: `encodeWord` / `decodeWord` for `BitVec (8 * w)`, with the
  round trip `decodeWord_encodeWord` and injectivity.
* **Fixed-size codes**: the class `ArenaEncode α` (a size, an encoder whose
  output has that length, and a decoder that reads a prefix), with instances
  for `Bool`, the fixed-width unsigned integers, `BitVec (8 * w)`, products,
  `Option` (tag byte then zero-padded payload) and `Sum`.
* **Tag inspection**: `tagOf` reads the first byte; `tag_option` shows that
  `Option.isSome` is decided by that byte alone.
* **Span view**: `encodeSpan` / `decodeSpan` for a list of at most `cap`
  cells behind a four-byte length, with the in-place primitives `spanLen`,
  `spanGet`, `spanSet`, `spanEq` and the substring test `spanSearch`, each
  specified against the list the span encodes.

The module imports only `Init`; every theorem depends on at most `propext`,
`Quot.sound` and `Classical.choice`.

## Main results

* `decodeWord_encodeWord`, `encodeWord_injective`: the little-endian word view round-trips and is injective.
* `ArenaEncode.encode_injective`: every fixed-size code is injective.
* `tag_option`: the first byte of an encoded option decides `isSome`.
* `decodeSpan_encodeSpan`, `spanGet_spanSet_self`, `spanGet_spanSet_ne`: the span view round-trips and its update is in place.
* `spanEq_iff`, `spanSearch_iff`: span equality and substring search meet their list specifications.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

/-- One arena byte. -/
abbrev Byte := BitVec 8

/-- A byte string. -/
abbrev Bytes := List Byte

/-! ## Word view -/

/-- The low `w` bytes of `k`, least significant first. -/
def natToBytes : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, k => BitVec.ofNat 8 k :: natToBytes w (k / 256)

/-- The natural number a little-endian byte string denotes. -/
def bytesToNat : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesToNat bs

/-- The `w` bytes of `x`, least significant first. -/
def encodeWord (w : Nat) (x : BitVec (8 * w)) : Bytes := natToBytes w x.toNat

/-- The word whose bytes are the first `w` bytes of `bs`; `none` when `bs` is
shorter than `w`. -/
def decodeWord (w : Nat) (bs : Bytes) : Option (BitVec (8 * w)) :=
  if w ≤ bs.length then some (BitVec.ofNat (8 * w) (bytesToNat (bs.take w))) else none

theorem natToBytes_length (w k : Nat) : (natToBytes w k).length = w := by
  induction w generalizing k with
  | zero => rfl
  | succ w ih => simp [natToBytes, ih]

/-- Byte splitting: the residue of `k` modulo `256 * m` is its low byte plus
`256` times the residue of `k / 256` modulo `m`. -/
theorem mod_split_byte (k m : Nat) : k % (256 * m) = k % 256 + 256 * (k / 256 % m) :=
  Nat.mod_mul

theorem two_pow_eight_mul_succ (w : Nat) : 2 ^ (8 * (w + 1)) = 256 * 2 ^ (8 * w) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

/-- The bytes of `k` denote `k` modulo `2 ^ (8 * w)`. -/
theorem bytesToNat_natToBytes (w k : Nat) : bytesToNat (natToBytes w k) = k % 2 ^ (8 * w) := by
  induction w generalizing k with
  | zero => simp [natToBytes, bytesToNat, Nat.mod_one]
  | succ w ih =>
    rw [natToBytes, bytesToNat, ih, two_pow_eight_mul_succ, mod_split_byte, BitVec.toNat_ofNat]

theorem encodeWord_length (w : Nat) (x : BitVec (8 * w)) : (encodeWord w x).length = w :=
  natToBytes_length w x.toNat

theorem decodeWord_encodeWord (w : Nat) (x : BitVec (8 * w)) (rest : Bytes) :
    decodeWord w (encodeWord w x ++ rest) = some x := by
  have hl : (encodeWord w x).length = w := encodeWord_length w x
  have h1 : w ≤ (encodeWord w x ++ rest).length := by simp [hl]
  have h2 : (encodeWord w x ++ rest).take w = encodeWord w x := List.take_left' hl
  rw [decodeWord, if_pos h1, h2, encodeWord, bytesToNat_natToBytes, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt x.isLt]

theorem encodeWord_injective (w : Nat) {x y : BitVec (8 * w)}
    (h : encodeWord w x = encodeWord w y) : x = y := by
  have hx := decodeWord_encodeWord w x []
  rw [h, decodeWord_encodeWord] at hx
  exact (Option.some.inj hx).symm

/-! ## Fixed-size codes -/

/-- A fixed-size byte code: every value encodes to exactly `size` bytes, and
the decoder reads a value back from any byte string that starts with its
encoding. -/
class ArenaEncode (α : Type) where
  /-- The number of bytes of every encoding. -/
  size : Nat
  /-- The encoder. -/
  encode : α → Bytes
  /-- The decoder; reads the first `size` bytes. -/
  decode : Bytes → Option α
  /-- Every encoding has length `size`. -/
  encode_length : ∀ a, (encode a).length = size
  /-- The decoder inverts the encoder on any extension. -/
  decode_encode : ∀ a rest, decode (encode a ++ rest) = some a

export ArenaEncode (encode decode encode_length decode_encode)

/-- The encoder of a fixed-size code is injective. -/
theorem ArenaEncode.encode_injective {α : Type} [ArenaEncode α] {a b : α}
    (h : encode a = encode b) : a = b := by
  have ha := decode_encode a ([] : Bytes)
  rw [h, decode_encode] at ha
  exact (Option.some.inj ha).symm

/-- The one-byte code of `Bool`: `false ↦ 0`, `true ↦ 1`. -/
instance : ArenaEncode Bool where
  size := 1
  encode b := [if b then 1 else 0]
  decode bs :=
    match bs with
    | [] => none
    | b :: _ => if b = 0 then some false else if b = 1 then some true else none
  encode_length b := by cases b <;> rfl
  decode_encode b rest := by cases b <;> simp

/-- The `w`-byte code of a type in bijection with `BitVec (8 * w)`. -/
@[instance_reducible] def wordCode {α : Type} (w : Nat) (toBV : α → BitVec (8 * w)) (ofBV : BitVec (8 * w) → α)
    (h : ∀ a, ofBV (toBV a) = a) : ArenaEncode α where
  size := w
  encode a := encodeWord w (toBV a)
  decode bs := (decodeWord w bs).map ofBV
  encode_length a := encodeWord_length w (toBV a)
  decode_encode a rest := by rw [decodeWord_encodeWord]; simp [h]

instance : ArenaEncode UInt8 := wordCode 1 UInt8.toBitVec UInt8.ofBitVec fun _ => rfl
instance : ArenaEncode UInt16 := wordCode 2 UInt16.toBitVec UInt16.ofBitVec fun _ => rfl
instance : ArenaEncode UInt32 := wordCode 4 UInt32.toBitVec UInt32.ofBitVec fun _ => rfl
instance : ArenaEncode UInt64 := wordCode 8 UInt64.toBitVec UInt64.ofBitVec fun _ => rfl
instance (w : Nat) : ArenaEncode (BitVec (8 * w)) := wordCode w id id fun _ => rfl

/-- The code of a pair: the first component's bytes followed by the second's. -/
instance {α β : Type} [ArenaEncode α] [ArenaEncode β] : ArenaEncode (α × β) where
  size := ArenaEncode.size α + ArenaEncode.size β
  encode p := encode p.1 ++ encode p.2
  decode bs :=
    (decode bs).bind fun a => (decode (bs.drop (ArenaEncode.size α))).map fun b => (a, b)
  encode_length p := by simp [encode_length]
  decode_encode p rest := by
    rw [List.append_assoc, decode_encode, List.drop_left' (encode_length _), decode_encode]
    rfl

/-- The tag view of `Option`: a tag byte (`0` for `none`, `1` for `some`)
followed by the payload, zero-padded to the payload size. -/
instance {α : Type} [ArenaEncode α] : ArenaEncode (Option α) where
  size := 1 + ArenaEncode.size α
  encode o :=
    match o with
    | none => 0 :: List.replicate (ArenaEncode.size α) 0
    | some a => 1 :: encode a
  decode bs :=
    match bs with
    | [] => none
    | t :: rest => if t = 0 then some none else if t = 1 then (decode rest).map some else none
  encode_length o := by cases o <;> simp [encode_length] <;> omega
  decode_encode o rest := by cases o <;> simp [decode_encode]

/-- The code of a sum: a tag byte (`0` for `inl`, `1` for `inr`) followed by
the payload, zero-padded to the larger payload size. -/
instance {α β : Type} [ArenaEncode α] [ArenaEncode β] : ArenaEncode (α ⊕ β) where
  size := 1 + max (ArenaEncode.size α) (ArenaEncode.size β)
  encode s :=
    match s with
    | .inl a => 0 :: (encode a ++
        List.replicate (max (ArenaEncode.size α) (ArenaEncode.size β) - ArenaEncode.size α) 0)
    | .inr b => 1 :: (encode b ++
        List.replicate (max (ArenaEncode.size α) (ArenaEncode.size β) - ArenaEncode.size β) 0)
  decode bs :=
    match bs with
    | [] => none
    | t :: rest =>
      if t = 0 then (decode rest).map Sum.inl
      else if t = 1 then (decode rest).map Sum.inr else none
  encode_length s := by
    cases s <;> simp [encode_length] <;> omega
  decode_encode s rest := by cases s <;> simp [decode_encode]

/-! ## Tag-only inspection -/

/-- The first byte of a byte string. -/
def tagOf : Bytes → Option Byte := List.head?

/-- The tag byte of an encoded `Option` decides `isSome` without the payload. -/
theorem tag_option {α : Type} [ArenaEncode α] (o : Option α) (rest : Bytes) :
    tagOf (encode o ++ rest) = some (if o.isSome then 1 else 0) := by
  cases o <;> rfl

/-! ## Span view -/

section Span

variable {α : Type} [ArenaEncode α]

/-- The four-byte little-endian length prefix of a span. -/
def spanHeader (n : Nat) : Bytes := encodeWord 4 (BitVec.ofNat (8 * 4) n)

/-- The concatenated encodings of a list of cells. -/
def encodeCells : List α → Bytes
  | [] => []
  | a :: l => encode a ++ encodeCells l

/-- The encoding of a span of capacity `cap`: the length prefix, the cells,
and zero padding to `cap` cells. -/
def encodeSpan (cap : Nat) (l : List α) (_h : l.length ≤ cap) : Bytes :=
  spanHeader l.length ++ encodeCells l ++
    List.replicate ((cap - l.length) * ArenaEncode.size α) 0

/-- The first `k` cells of a byte string. -/
def decodeCells : Nat → Bytes → Option (List α)
  | 0, _ => some []
  | k + 1, bs =>
    (decode bs).bind fun a => (decodeCells k (bs.drop (ArenaEncode.size α))).map (a :: ·)

/-- The length field of an encoded span. -/
def spanLen (bs : Bytes) : Option Nat := (decodeWord 4 bs).map BitVec.toNat

/-- The list an encoded span of capacity `cap` holds. -/
def decodeSpan (cap : Nat) (bs : Bytes) : Option (List α) :=
  (spanLen bs).bind fun n => if n ≤ cap then decodeCells n (bs.drop 4) else none

/-- The cell at index `i` of an encoded span. -/
def spanGet (i : Nat) (bs : Bytes) : Option α :=
  match spanLen bs with
  | some n => if i < n then decode (bs.drop (4 + i * ArenaEncode.size α)) else none
  | none => none

/-- The encoded span with the cell at index `i` replaced by `a`; unchanged when
`i` is out of range. -/
def spanSet (i : Nat) (a : α) (bs : Bytes) : Bytes :=
  match spanLen bs with
  | some n =>
    if i < n then
      bs.take (4 + i * ArenaEncode.size α) ++ encode a ++
        bs.drop (4 + (i + 1) * ArenaEncode.size α)
    else bs
  | none => bs

/-- Byte equality of two encoded spans. -/
def spanEq (x y : Bytes) : Bool := decide (x = y)

theorem spanHeader_length (n : Nat) : (spanHeader n).length = 4 := encodeWord_length 4 _

theorem spanLen_spanHeader (n : Nat) (hn : n < 2 ^ 32) (rest : Bytes) :
    spanLen (spanHeader n ++ rest) = some n := by
  rw [spanLen, spanHeader, decodeWord_encodeWord]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem encodeCells_length (l : List α) : (encodeCells l).length = l.length * ArenaEncode.size α := by
  induction l with
  | nil => simp [encodeCells]
  | cons a l ih =>
    simp only [encodeCells, List.length_append, encode_length, ih, List.length_cons, Nat.succ_mul]
    omega

theorem drop_encode_add (a : α) (t : Bytes) (k : Nat) :
    (encode a ++ t).drop (ArenaEncode.size α + k) = t.drop k := by
  rw [← encode_length a, List.drop_length_add_append]

theorem take_encode_add (a : α) (t : Bytes) (k : Nat) :
    (encode a ++ t).take (ArenaEncode.size α + k) = encode a ++ t.take k := by
  rw [← encode_length a, List.take_length_add_append]

theorem drop_spanHeader_add (n : Nat) (t : Bytes) (k : Nat) :
    (spanHeader n ++ t).drop (4 + k) = t.drop k := by
  rw [← spanHeader_length n, List.drop_length_add_append]

theorem take_spanHeader_add (n : Nat) (t : Bytes) (k : Nat) :
    (spanHeader n ++ t).take (4 + k) = spanHeader n ++ t.take k := by
  rw [← spanHeader_length n, List.take_length_add_append]

theorem decodeCells_encodeCells (l : List α) (rest : Bytes) :
    decodeCells l.length (encodeCells l ++ rest) = some l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hd : (encode a ++ (encodeCells l ++ rest)).drop (ArenaEncode.size α) =
        encodeCells l ++ rest := by
      simpa using drop_encode_add a (encodeCells l ++ rest) 0
    simp only [List.length_cons, decodeCells, encodeCells, List.append_assoc, decode_encode, hd, ih,
      Option.bind_some, Option.map_some]

/-- Dropping `i` cells' worth of bytes from encoded cells drops `i` cells. -/
theorem drop_encodeCells (l : List α) (rest : Bytes) (i : Nat) (hi : i ≤ l.length) :
    (encodeCells l ++ rest).drop (i * ArenaEncode.size α) = encodeCells (l.drop i) ++ rest := by
  induction l generalizing i with
  | nil =>
    have : i = 0 := Nat.le_zero.mp hi
    subst this
    simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ j =>
      have e : (j + 1) * ArenaEncode.size α = ArenaEncode.size α + j * ArenaEncode.size α := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [e, encodeCells, List.append_assoc, drop_encode_add, List.drop_succ_cons,
        ih j (Nat.le_of_succ_le_succ hi)]

/-- Splicing one cell's encoding into encoded cells encodes the updated list. -/
theorem encodeCells_set (l : List α) (rest : Bytes) (i : Nat) (a : α) (hi : i < l.length) :
    (encodeCells l ++ rest).take (i * ArenaEncode.size α) ++ encode a ++
        (encodeCells l ++ rest).drop ((i + 1) * ArenaEncode.size α) =
      encodeCells (l.set i a) ++ rest := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons b l ih =>
    cases i with
    | zero =>
      have hd := drop_encode_add b (encodeCells l ++ rest) 0
      simp only [Nat.add_zero, List.drop_zero] at hd
      simp only [encodeCells, List.append_assoc, Nat.zero_mul, List.take_zero, List.nil_append,
        Nat.zero_add, Nat.one_mul, hd, List.set_cons_zero]
    | succ j =>
      have e1 : (j + 1) * ArenaEncode.size α = ArenaEncode.size α + j * ArenaEncode.size α := by
        rw [Nat.succ_mul, Nat.add_comm]
      have e2 : (j + 1 + 1) * ArenaEncode.size α =
          ArenaEncode.size α + (j + 1) * ArenaEncode.size α := by
        rw [Nat.succ_mul (j + 1), Nat.add_comm]
      have hj : j < l.length := Nat.lt_of_succ_lt_succ hi
      simp only [encodeCells, List.append_assoc, List.set_cons_succ]
      rw [e1, e2, take_encode_add, drop_encode_add, ← ih j hj]
      simp only [List.append_assoc]

theorem spanLen_encodeSpan (cap : Nat) (l : List α) (h : l.length ≤ cap) (hlen : l.length < 2 ^ 32) :
    spanLen (encodeSpan cap l h) = some l.length := by
  rw [encodeSpan, List.append_assoc, spanLen_spanHeader _ hlen]

theorem encodeSpan_length (cap : Nat) (l : List α) (h : l.length ≤ cap) :
    (encodeSpan cap l h).length = 4 + cap * ArenaEncode.size α := by
  simp only [encodeSpan, List.length_append, spanHeader_length, encodeCells_length,
    List.length_replicate]
  rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' h]

theorem decodeSpan_encodeSpan (cap : Nat) (l : List α) (h : l.length ≤ cap) (hcap : cap < 2 ^ 32) :
    decodeSpan cap (encodeSpan cap l h) = some l := by
  have hlen : l.length < 2 ^ 32 := Nat.lt_of_le_of_lt h hcap
  have hd : (encodeSpan cap l h).drop 4 =
      encodeCells l ++ List.replicate ((cap - l.length) * ArenaEncode.size α) 0 := by
    have hd0 := drop_spanHeader_add l.length
      (encodeCells l ++ List.replicate ((cap - l.length) * ArenaEncode.size α) 0) 0
    rw [Nat.add_zero, List.drop_zero] at hd0
    rw [encodeSpan, List.append_assoc, hd0]
  rw [decodeSpan, spanLen_encodeSpan cap l h hlen, Option.bind_some, if_pos h, hd,
    decodeCells_encodeCells]

theorem encodeSpan_injective (cap : Nat) {l₁ l₂ : List α} (h₁ : l₁.length ≤ cap)
    (h₂ : l₂.length ≤ cap) (hcap : cap < 2 ^ 32)
    (e : encodeSpan cap l₁ h₁ = encodeSpan cap l₂ h₂) : l₁ = l₂ := by
  have d := decodeSpan_encodeSpan cap l₁ h₁ hcap
  rw [e, decodeSpan_encodeSpan cap l₂ h₂ hcap] at d
  exact (Option.some.inj d).symm

/-- `spanGet` reads the `i`-th cell of the encoded list. -/
theorem spanGet_encodeSpan (cap : Nat) (l : List α) (h : l.length ≤ cap)
    (hlen : l.length < 2 ^ 32) (i : Nat) : spanGet i (encodeSpan cap l h) = l[i]? := by
  rw [spanGet, spanLen_encodeSpan cap l h hlen]
  dsimp only
  by_cases hi : i < l.length
  · rw [if_pos hi, encodeSpan, List.append_assoc, drop_spanHeader_add,
      drop_encodeCells l _ i (Nat.le_of_lt hi), List.drop_eq_getElem_cons hi, encodeCells,
      List.append_assoc, decode_encode, List.getElem?_eq_getElem hi]
  · rw [if_neg hi, List.getElem?_eq_none (Nat.le_of_not_lt hi)]

/-- `spanSet` on an encoded span encodes the updated list. -/
theorem spanSet_encodeSpan (cap : Nat) (l : List α) (h : l.length ≤ cap)
    (hlen : l.length < 2 ^ 32) (i : Nat) (a : α) :
    spanSet i a (encodeSpan cap l h) =
      encodeSpan cap (l.set i a) (by rw [List.length_set]; exact h) := by
  rw [spanSet, spanLen_encodeSpan cap l h hlen]
  dsimp only
  by_cases hi : i < l.length
  · rw [if_pos hi]
    have hT := encodeCells_set l (List.replicate ((cap - l.length) * ArenaEncode.size α) 0) i a hi
    simp only [encodeSpan, List.append_assoc, List.length_set]
    rw [take_spanHeader_add, drop_spanHeader_add, ← hT]
    simp only [List.append_assoc]
  · rw [if_neg hi]
    simp only [encodeSpan, List.set_eq_of_length_le (Nat.le_of_not_lt hi)]

theorem spanLen_spanSet (cap : Nat) (l : List α) (h : l.length ≤ cap)
    (hlen : l.length < 2 ^ 32) (i : Nat) (a : α) :
    spanLen (spanSet i a (encodeSpan cap l h)) = some l.length := by
  rw [spanSet_encodeSpan cap l h hlen i a, spanLen_encodeSpan _ _ _ (by simpa using hlen),
    List.length_set]

theorem spanGet_spanSet_self (cap : Nat) (l : List α) (h : l.length ≤ cap)
    (hlen : l.length < 2 ^ 32) (i : Nat) (a : α) (hi : i < l.length) :
    spanGet i (spanSet i a (encodeSpan cap l h)) = some a := by
  rw [spanSet_encodeSpan cap l h hlen i a, spanGet_encodeSpan _ _ _ (by simpa using hlen),
    List.getElem?_set_self (by simpa using hi)]

theorem spanGet_spanSet_ne (cap : Nat) (l : List α) (h : l.length ≤ cap)
    (hlen : l.length < 2 ^ 32) (i j : Nat) (a : α) (hne : i ≠ j) :
    spanGet j (spanSet i a (encodeSpan cap l h)) = l[j]? := by
  rw [spanSet_encodeSpan cap l h hlen i a, spanGet_encodeSpan _ _ _ (by simpa using hlen),
    List.getElem?_set_ne hne]

/-- `spanEq` decides equality of the lists two spans of the same capacity encode. -/
theorem spanEq_iff (cap : Nat) {l₁ l₂ : List α} (h₁ : l₁.length ≤ cap) (h₂ : l₂.length ≤ cap)
    (hcap : cap < 2 ^ 32) :
    spanEq (encodeSpan cap l₁ h₁) (encodeSpan cap l₂ h₂) = true ↔ l₁ = l₂ := by
  rw [spanEq, decide_eq_true_iff]
  constructor
  · exact encodeSpan_injective cap h₁ h₂ hcap
  · intro e
    subst e
    rfl

end Span

/-! ## Substring search over byte spans -/

/-- Whether the first argument is a prefix of the second. -/
def isPrefixB : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: n, b :: h => decide (a = b) && isPrefixB n h

theorem isPrefixB_iff (n h : Bytes) : isPrefixB n h = true ↔ ∃ b, h = n ++ b := by
  induction n generalizing h with
  | nil => simp [isPrefixB]
  | cons a n ih =>
    cases h with
    | nil => simp [isPrefixB]
    | cons b h =>
      simp only [isPrefixB, Bool.and_eq_true, decide_eq_true_eq, ih, List.cons_append,
        List.cons.injEq]
      constructor
      · rintro ⟨e, t, ht⟩
        exact ⟨t, e.symm, ht⟩
      · rintro ⟨t, e, ht⟩
        exact ⟨e.symm, t, ht⟩

/-- Whether `needle` occurs as a contiguous substring of `hay`. -/
def spanSearch : Bytes → Bytes → Bool
  | [], needle => needle.isEmpty
  | b :: t, needle => isPrefixB needle (b :: t) || spanSearch t needle

/-- `spanSearch` decides contiguous-substring occurrence. -/
theorem spanSearch_iff (h n : Bytes) : spanSearch h n = true ↔ ∃ a b, h = a ++ n ++ b := by
  induction h with
  | nil =>
    simp only [spanSearch, List.isEmpty_iff]
    constructor
    · intro e
      exact ⟨[], [], by simp [e]⟩
    · rintro ⟨a, b, e⟩
      cases a <;> cases n <;> simp_all
  | cons b t ih =>
    simp only [spanSearch, Bool.or_eq_true, isPrefixB_iff, ih]
    constructor
    · rintro (⟨c, e⟩ | ⟨a, c, e⟩)
      · exact ⟨[], c, by simp [e]⟩
      · exact ⟨b :: a, c, by simp [e]⟩
    · rintro ⟨a, c, e⟩
      cases a with
      | nil => exact Or.inl ⟨c, by simpa using e⟩
      | cons a' a =>
        simp only [List.cons_append, List.cons.injEq] at e
        exact Or.inr ⟨a, c, e.2⟩

end VerifiedEval

end
