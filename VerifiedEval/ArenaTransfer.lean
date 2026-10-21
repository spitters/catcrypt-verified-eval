/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.Arena
public import Transfer.Base.Related
public import ReprTransfer

/-!
# Transfer from spec types to the byte arena

The transfer front of a verified evaluation route. A statement over spec types
(`List`, ASCII `String`, `Option`, bounded `Nat`) is rewritten to a statement
over the byte arena of `Arena` by instance resolution over registered
relations, with no lemma written per statement.

* **Embeddings**: `arenaEmbedding`, `spanEmbedding` and `wordEmbedding` package
  the fixed-size code, the span code and the word view as `ReprEmbedding`s.
* **Value squares**: `Related` instances, one per span primitive and for the
  option tag and the word view, each proved from the specification lemma of
  `Arena`. They compose through `Transfer.composeBinOp` and the leaf instances
  of `Transfer.Base.Related`.
* **Statement squares**: the class `StmtTransfer p q` (`p ↔ q`) with instances
  for equality of related values, span equality, the option tag, substring
  search over bytes and over ASCII strings, and the connectives `∧`, `∨`, `¬`.
  `Related` carries values of `Type u` only, so the statement layer is a
  separate class over `Prop` fed by the value squares.

The side condition of the span lemmas, `l.length < 2 ^ 32`, is discharged from
the class `SpanCap cap` (`cap < 2 ^ 32`) and the capacity bound of `Span`.

## Main definitions

* `arenaEmbedding`, `Span`, `SpanCap`, `spanEnc`, `spanEmbedding`, `Span.set`,
  `wordEnc`, `wordEmbedding`: the embeddings of spec values into bytes.
* `asciiByte`, `asciiBytes`, `IsAscii`, `Ascii`: the byte view of an ASCII string.
* `StmtTransfer`: a statement over spec values is equivalent to a statement
  over their encodings.

## Main results

* `relSpanLen`, `relSpanGet`, `relSpanSet`, `relSpanEq`, `relOptionTag`,
  `relWord`, `relAnd`, `relOr`: the registered value squares.
* `stmtOfRelated`, `stmtSpanEq`, `stmtOptionTag`, `stmtSearch`,
  `stmtStringSearch`, `stmtAnd`, `stmtOr`, `stmtNot`, `stmtRefl`: the
  registered statement squares.
* `asciiBytes_append`, `asciiByte_injOn`, `map_asciiByte_inj`,
  `substring_iff_spanSearch`: for
  ASCII strings, substring occurrence is decided by `spanSearch` on the byte
  views.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

open Transfer ReprTransfer

/-! ## Embeddings -/

/-- The fixed-size code of `α` as a representation embedding into bytes. -/
def arenaEmbedding (α : Type) [ArenaEncode α] : ReprEmbedding α Bytes where
  enc := encode
  enc_inj _ _ h := ArenaEncode.encode_injective h

/-- A list of at most `cap` cells. -/
abbrev Span (cap : Nat) (α : Type) := {l : List α // l.length ≤ cap}

/-- The capacity `cap` fits the four-byte length prefix of a span. -/
class SpanCap (cap : Nat) : Prop where
  /-- The capacity bound. -/
  lt : cap < 2 ^ 32

section SpanEmb

theorem Span.length_lt {α : Type} {cap : Nat} [SpanCap cap] (l : Span cap α) :
    l.1.length < 2 ^ 32 :=
  Nat.lt_of_le_of_lt l.2 SpanCap.lt

variable {α : Type} [ArenaEncode α]

/-- The span encoding of a bounded list. -/
def spanEnc (cap : Nat) (l : Span cap α) : Bytes := encodeSpan cap l.1 l.2

/-- The span code of capacity `cap` as a representation embedding into bytes. -/
def spanEmbedding (cap : Nat) [SpanCap cap] : ReprEmbedding (Span cap α) Bytes where
  enc := spanEnc cap
  enc_inj l₁ l₂ h := Subtype.ext (encodeSpan_injective cap l₁.2 l₂.2 SpanCap.lt h)

/-- The bounded list with the cell at index `i` replaced by `a`. -/
def Span.set {cap : Nat} (l : Span cap α) (i : Nat) (a : α) : Span cap α :=
  ⟨l.1.set i a, by rw [List.length_set]; exact l.2⟩

end SpanEmb

/-- The word view of a natural number below `2 ^ (8 * w)`: its `w` bytes,
least significant first. -/
def wordEnc (w : Nat) (n : Fin (2 ^ (8 * w))) : Bytes := encodeWord w (BitVec.ofFin n)

/-- The word view as a representation embedding into bytes. -/
def wordEmbedding (w : Nat) : ReprEmbedding (Fin (2 ^ (8 * w))) Bytes where
  enc := wordEnc w
  enc_inj x y h := by
    have e := encodeWord_injective w h
    exact congrArg BitVec.toFin e

/-! ## Value squares -/

section ValueSquares

variable {α : Type} [ArenaEncode α]

/-- `spanLen` reads the length of the list a span encodes. -/
instance relSpanLen (cap : Nat) [SpanCap cap] (l : Span cap α) (b : Bytes)
    [hb : Related (spanEnc cap) l b] :
    Related (id : Option Nat → Option Nat) (some l.1.length) (spanLen b) where
  rel := by
    rw [← hb.rel]
    exact (spanLen_encodeSpan cap l.1 l.2 l.length_lt).symm

/-- `spanGet i` reads the `i`-th cell of the list a span encodes. -/
instance relSpanGet (cap : Nat) [SpanCap cap] (i : Nat) (l : Span cap α) (b : Bytes)
    [hb : Related (spanEnc cap) l b] :
    Related (id : Option α → Option α) (l.1[i]?) (spanGet i b) where
  rel := by
    rw [← hb.rel]
    exact (spanGet_encodeSpan cap l.1 l.2 l.length_lt i).symm

/-- `spanSet i a` encodes the list with its `i`-th cell replaced by `a`. -/
instance relSpanSet (cap : Nat) [SpanCap cap] (i : Nat) (a : α) (l : Span cap α) (b : Bytes)
    [hb : Related (spanEnc cap) l b] :
    Related (spanEnc cap) (l.set i a) (spanSet i a b) where
  rel := by
    rw [← hb.rel]
    exact (spanSet_encodeSpan cap l.1 l.2 l.length_lt i a).symm

/-- `spanEq` decides equality of the lists two spans encode. -/
instance relSpanEq [DecidableEq α] (cap : Nat) [SpanCap cap] (l₁ l₂ : Span cap α)
    (b₁ b₂ : Bytes) [h₁ : Related (spanEnc cap) l₁ b₁] [h₂ : Related (spanEnc cap) l₂ b₂] :
    Related (id : Bool → Bool) (decide (l₁.1 = l₂.1)) (spanEq b₁ b₂) where
  rel := by
    rw [← h₁.rel, ← h₂.rel]
    exact Bool.eq_iff_iff.mpr
      (decide_eq_true_iff.trans (spanEq_iff cap l₁.2 l₂.2 SpanCap.lt).symm)

/-- The tag byte of an encoded option decides `isSome`. -/
instance relOptionTag (o : Option α) (b : Bytes) [hb : Related (encode : Option α → Bytes) o b] :
    Related (id : Bool → Bool) o.isSome (decide (tagOf b = some 1)) where
  rel := by
    rw [← hb.rel]
    have t := tag_option o []
    rw [List.append_nil] at t
    rw [t]
    cases o <;> rfl

/-- `decodeWord` reads back the number a word view encodes. -/
instance relWord (w : Nat) (n : Fin (2 ^ (8 * w))) (b : Bytes) [hb : Related (wordEnc w) n b] :
    Related (id : Option Nat → Option Nat) (some n.val) ((decodeWord w b).map BitVec.toNat) where
  rel := by
    rw [← hb.rel]
    have d := decodeWord_encodeWord w (BitVec.ofFin n) []
    rw [List.append_nil] at d
    rw [wordEnc, d]
    rfl

/-- Boolean conjunction realizes itself along the identity encoding. -/
instance relAnd : RelatedBinOp (id : Bool → Bool) (· && ·) (· && ·) where
  comm _ _ := rfl

/-- Boolean disjunction realizes itself along the identity encoding. -/
instance relOr : RelatedBinOp (id : Bool → Bool) (· || ·) (· || ·) where
  comm _ _ := rfl

end ValueSquares

/-! ## ASCII strings -/

/-- The byte of a character: its code point modulo `256`. -/
def asciiByte (c : Char) : Byte := BitVec.ofNat 8 c.toNat

/-- The bytes of a string, one per character. On an ASCII string this is its
UTF-8 encoding. -/
def asciiBytes (s : String) : Bytes := s.toList.map asciiByte

/-- Every character of `s` is below `128`. -/
def IsAscii (s : String) : Prop := ∀ c ∈ s.toList, c.toNat < 128

/-- The string `s` is ASCII. -/
class Ascii (s : String) : Prop where
  /-- Every character of `s` is below `128`. -/
  isAscii : IsAscii s

theorem asciiBytes_append (s t : String) : asciiBytes (s ++ t) = asciiBytes s ++ asciiBytes t := by
  simp only [asciiBytes, String.toList_append, List.map_append]

/-- `asciiByte` is injective on characters below `128`. -/
theorem asciiByte_injOn {c d : Char} (hc : c.toNat < 128) (hd : d.toNat < 128)
    (h : asciiByte c = asciiByte d) : c = d := by
  have e := congrArg BitVec.toNat h
  simp only [asciiByte, BitVec.toNat_ofNat] at e
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e
  exact Char.toNat_inj.mp e

/-- Mapping `asciiByte` over two lists of characters below `128` is injective. -/
theorem map_asciiByte_inj {l m : List Char} (hl : ∀ c ∈ l, c.toNat < 128)
    (hm : ∀ c ∈ m, c.toNat < 128) (h : l.map asciiByte = m.map asciiByte) : l = m := by
  induction l generalizing m with
  | nil => cases m <;> simp_all
  | cons c l ih =>
    cases m with
    | nil => simp at h
    | cons d m =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.mem_cons, forall_eq_or_imp] at hl hm
      rw [asciiByte_injOn hl.1 hm.1 h.1, ih hl.2 hm.2 h.2]

/-- For ASCII strings, `n` occurs as a substring of `s` exactly when
`spanSearch` finds the bytes of `n` in the bytes of `s`. -/
theorem substring_iff_spanSearch (s n : String) (hs : IsAscii s) (hn : IsAscii n) :
    (∃ a b : String, s = a ++ n ++ b) ↔ spanSearch (asciiBytes s) (asciiBytes n) = true := by
  rw [spanSearch_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨asciiBytes a, asciiBytes b, by rw [asciiBytes_append, asciiBytes_append]⟩
  · rintro ⟨A, B, e⟩
    rw [asciiBytes, List.append_assoc, List.map_eq_append_iff] at e
    obtain ⟨x, y, hxy, -, hy⟩ := e
    rw [List.map_eq_append_iff] at hy
    obtain ⟨m, z, hmz, hm, -⟩ := hy
    have hmn : m = n.toList := by
      refine map_asciiByte_inj (fun c hc => hs c ?_) hn hm
      rw [hxy, hmz]
      simp [hc]
    refine ⟨String.ofList x, String.ofList z, ?_⟩
    rw [← String.toList_inj, String.toList_append, String.toList_append, String.toList_ofList,
      String.toList_ofList, hxy, hmz, hmn, List.append_assoc]

/-! ## Statement squares -/

/-- The statement `p` over spec values is equivalent to the statement `q` over
their encodings. -/
class StmtTransfer (p q : Prop) : Prop where
  /-- The two statements are equivalent. -/
  iff : p ↔ q

section StmtSquares

variable {α : Type} [ArenaEncode α]

/-- An equation on a value transfers to the same equation on a related value. -/
instance stmtOfRelated {β : Type} (x y z : β) [h : Related (id : β → β) x y] :
    StmtTransfer (x = z) (y = z) where
  iff := by rw [← h.rel]; rfl

/-- Equality of two bounded lists transfers to `spanEq` on their spans. -/
instance stmtSpanEq (cap : Nat) [SpanCap cap] (l₁ l₂ : Span cap α) (b₁ b₂ : Bytes)
    [h₁ : Related (spanEnc cap) l₁ b₁] [h₂ : Related (spanEnc cap) l₂ b₂] :
    StmtTransfer (l₁.1 = l₂.1) (spanEq b₁ b₂ = true) where
  iff := by
    rw [← h₁.rel, ← h₂.rel]
    exact (spanEq_iff cap l₁.2 l₂.2 SpanCap.lt).symm

/-- `isSome` of an option transfers to its tag byte. -/
instance stmtOptionTag (o : Option α) (b : Bytes) [hb : Related (encode : Option α → Bytes) o b] :
    StmtTransfer (o.isSome = true) (tagOf b = some 1) where
  iff := by
    rw [show o.isSome = decide (tagOf b = some 1) from (relOptionTag o b).rel]
    exact decide_eq_true_iff

/-- Substring occurrence in bytes transfers to `spanSearch`. -/
instance stmtSearch (h n : Bytes) : StmtTransfer (∃ a b, h = a ++ n ++ b) (spanSearch h n = true) where
  iff := (spanSearch_iff h n).symm

/-- Substring occurrence in an ASCII string transfers to `spanSearch` on the
byte views. -/
instance stmtStringSearch (s n : String) [hs : Ascii s] [hn : Ascii n] (h m : Bytes)
    [rs : Related asciiBytes s h] [rn : Related asciiBytes n m] :
    StmtTransfer (∃ a b : String, s = a ++ n ++ b) (spanSearch h m = true) where
  iff := by
    rw [← rs.rel, ← rn.rel]
    exact substring_iff_spanSearch s n hs.isAscii hn.isAscii

/-- Conjunction transfers componentwise. -/
instance stmtAnd (p q p' q' : Prop) [hp : StmtTransfer p p'] [hq : StmtTransfer q q'] :
    StmtTransfer (p ∧ q) (p' ∧ q') where
  iff := and_congr hp.iff hq.iff

/-- Disjunction transfers componentwise. -/
instance stmtOr (p q p' q' : Prop) [hp : StmtTransfer p p'] [hq : StmtTransfer q q'] :
    StmtTransfer (p ∨ q) (p' ∨ q') where
  iff := or_congr hp.iff hq.iff

/-- Negation transfers. -/
instance stmtNot (p p' : Prop) [hp : StmtTransfer p p'] : StmtTransfer (¬p) (¬p') where
  iff := not_congr hp.iff

/-- A statement transfers to itself. -/
instance (priority := low) stmtRefl (p : Prop) : StmtTransfer p p where
  iff := Iff.rfl

end StmtSquares

/-! ## Demonstrations

Each statement below is closed by `StmtTransfer.iff` with the instance found
by resolution over the registered squares. -/

section Demo

instance : SpanCap 64 := ⟨by decide⟩

instance : Ascii "hello world" := ⟨by unfold IsAscii; decide⟩

instance : Ascii "lo w" := ⟨by unfold IsAscii; decide⟩

example (o : Option UInt32) : o.isSome = true ↔ tagOf (encode o) = some 1 :=
  StmtTransfer.iff

example (l₁ l₂ : Span 64 UInt8) : l₁.1 = l₂.1 ↔ spanEq (spanEnc 64 l₁) (spanEnc 64 l₂) = true :=
  StmtTransfer.iff

example : (∃ a b : String, "hello world" = a ++ "lo w" ++ b) ↔
    spanSearch (asciiBytes "hello world") (asciiBytes "lo w") = true :=
  StmtTransfer.iff

example (l : Span 64 UInt8) (i j : Nat) (a : UInt8) (v : Option UInt8) :
    (l.set i a).1[j]? = v ↔ spanGet j (spanSet i a (spanEnc 64 l)) = v :=
  StmtTransfer.iff

example (l₁ l₂ : Span 64 UInt8) (o : Option UInt8) :
    l₁.1 = l₂.1 ∧ o.isSome = true ↔
      spanEq (spanEnc 64 l₁) (spanEnc 64 l₂) = true ∧ tagOf (encode o) = some 1 :=
  StmtTransfer.iff

example (n : Fin (2 ^ (8 * 4))) : some n.val = some 7 ↔
    (decodeWord 4 (wordEnc 4 n)).map BitVec.toNat = some 7 :=
  StmtTransfer.iff

end Demo

end VerifiedEval

end
