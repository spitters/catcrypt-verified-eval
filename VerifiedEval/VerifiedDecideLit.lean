/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.VerifiedDecideHW
public meta import VerifiedEval.VerifiedDecide
public meta import VerifiedEval.VerifiedDecideHW
public import Lean

/-!
# Deciding a proposition by a machine run on literal data

`machineAcceptsNat code n regs regions res` is `machineAccepts` on the bytes of the
concatenated chunks `code.flatten`, the instruction count `n`, and the machine state `stateOfLit regs regions`: register `k` of the
sixteen general-purpose registers (SDM numbering, `%rsp` at index `4`) holds `regs[k]`, the
flags are clear, and the byte at address `a` is the byte of the region `(base, bytes)` of
`regions` that contains `a`, `0` outside every region. All five arguments are natural
numbers and lists of them, so a closed application can be written with raw literals only:
`Expr.lit (.natVal _)`, `List.cons`, `List.nil` and `Prod.mk`.

`regsOf L plan σ` and `regionsOf L plan σ` compute that data from a layout, a register plan
and a source state. `stateOfLit_eq` proves that `stateOfLit (regsOf L plan σ)
(regionsOf L plan σ)` is `initState L plan σ` for a well-formed plan and spans shorter than
`2 ^ 32` cells, and `machineAccepts_of_lit` transfers an accepting literal run to the
initial state.

The code is a list of chunks, which `nat_chunks%` emits with `16` bytes each: a closed
application to the chunks of a code of `N` bytes is compiled by the code generator and checked
by the kernel within their default recursion limits for `N` up to several tens of thousands,
where one flat list literal of a few thousand elements exceeds the code generator's limit.
`chunksMatch cs l` checks the chunks
against a byte list one chunk at a time, and `flatten_map_eq_of_chunksMatch` concludes that
they concatenate to it.

`machineAcceptsNatD code n h regs regions res` is `machineAcceptsNat` with a proof `h` of
`codeDecodes code n`, that the bytes decode into `n` instructions. `machineAcceptsNat` is
`false` on bytes that do not decode, while the processor runs any bytes, so the
machine-evaluation rule is sound on decodable bytes only; it evaluates applications of
`machineAcceptsNatD`, whose decoding argument the kernel has checked.

`DecisionProcLit` extends `DecisionProc` by the literal bytes, instruction count and result
register number of the compiled procedure, with their equations and the decoding fact
`decodes`, which `codeDecodes_of_eqs` derives from the equations and the byte round trip. The
tactic `verified_decide_lit d` closes `P x` by evaluating `regsOf` and `regionsOf` at `x` to
raw literals, proving each equation by `decide +kernel`, and asserting through
`Lean.ofReduceBool` an auxiliary definition whose value is one application of
`machineAcceptsNatD` to five raw literals and the decoding proof `d.decodes`.

The compiled implementation `machineAcceptsNatImpl` runs the bytes on the host processor
through the runner of `VerifiedDecideHW`.

## Main definitions

* `regionByte`, `stateOfLit`: the machine state of literal register and memory data.
* `machineAcceptsNat`, `machineAcceptsNatImpl`: the answer on literal data and its hardware
  implementation.
* `codeDecodes`, `machineAcceptsNatD`: the decoding fact and the answer on decodable literal
  data.
* `regsOf`, `regionsOf`: the literal data of the initial state of a source state.
* `DecisionProcLit`: a decision procedure with literal code.
* `chunksMatch`: chunked literal bytes against a byte list.
* `nat_lits%`: a closed natural-number datum as raw literals.
* `nat_chunks%`: a closed list of natural numbers as raw literal chunks of `16` elements.
* `verified_decide_lit`: the tactic.

## Main results

* `flatten_map_eq_of_chunksMatch`: matching chunks concatenate to the byte list.
* `stateOfLit_eq`: the literal state of `regsOf` and `regionsOf` is `initState`.
* `machineAccepts_of_lit`: an accepting `machineAcceptsNat` run on the literal data gives an
  accepting `machineAccepts` run on the initial state.
* `codeDecodes_of_eqs`: the literal code of a registered procedure decodes.
* `verifiedDecideLit_sound`: an accepting `machineAcceptsNatD` run of a registered procedure
  with literal code proves the proposition.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedEval

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip (decodeJStream6)

/-! ## The machine state of literal data -/

/-- The byte at address `a` of a list of regions `(base, bytes)`: byte `a - base` of the
first region with `base ≤ a < base + bytes.length`, and `0` outside every region. -/
def regionByte (a : Nat) : List (Nat × List Nat) → Nat
  | [] => 0
  | (b, bs) :: rs => if b ≤ a ∧ a < b + bs.length then bs.getD (a - b) 0 else regionByte a rs

/-- The machine state of literal data: the register of SDM number `k < 16` holds `regs[k]`
(`0` past the end of the list), every other register name holds `0`, the flags are clear,
and the byte at address `a` is `regionByte a regions`. -/
def stateOfLit (regs : List Nat) (regions : List (Nat × List Nat)) : AState where
  regs := fun r => match gpNum? r with
    | some k => BitVec.ofNat 64 (regs.getD k 0)
    | none => 0
  mem := fun a => BitVec.ofNat 8 (regionByte a.toNat regions)

/-! ## The runner on literal data -/

/-- The runner input for literal data: the code bytes, the sixteen registers, the result
register number and one `region` line per region. -/
def vrunInputLit (code regs : List Nat) (regions : List (Nat × List Nat)) (res : Nat) :
    String :=
  let rs := (List.range 16).map fun k => hexNat (regs.getD k 0 % 2 ^ 64)
  "VRUN1\n" ++ s!"code {code.length} {hexBytes code}\n" ++ "regs " ++ " ".intercalate rs ++
    "\n" ++ s!"res {res}\n" ++
    String.join (regions.map fun p => s!"region {hexNat p.1} {p.2.length} {hexBytes p.2}\n") ++
    "end\n"

/-- The hardware implementation of `machineAcceptsNat`: when `decodeJStream6 n` succeeds on
the bytes of `code.flatten` and `res < 16`, the answer of the runner on
`vrunInputLit code.flatten regs regions res`; `false` otherwise and on any runner failure. -/
unsafe def machineAcceptsNatImpl (code : List (List Nat)) (n : Nat) (regs : List Nat)
    (regions : List (Nat × List Nat)) (res : Nat) : Bool :=
  let bytes := code.flatten
  match decodeJStream6 n (bytes.map (BitVec.ofNat 8)) with
  | some _ =>
      if res < 16 then
        unsafeBaseIO do
          match ← (runVrun (vrunInputLit bytes regs regions res)).toBaseIO with
          | .ok b => pure b
          | .error _ => pure false
      else false
  | none => false

/-- The machine model's answer on literal data: `machineAccepts` on the bytes of the
concatenated chunks `code.flatten`, `n` instructions, the state `stateOfLit regs regions` and
the register of SDM number `res`. Compiled code runs the bytes on the host processor
through `machineAcceptsNatImpl`. -/
@[implemented_by machineAcceptsNatImpl]
def machineAcceptsNat (code : List (List Nat)) (n : Nat) (regs : List Nat)
    (regions : List (Nat × List Nat)) (res : Nat) : Bool :=
  machineAccepts (code.flatten.map (BitVec.ofNat 8)) n (stateOfLit regs regions) (regName res)

/-- The bytes of the concatenated chunks `code.flatten` decode into `n` instructions by
`decodeJStream6`. -/
def codeDecodes (code : List (List Nat)) (n : Nat) : Bool :=
  (decodeJStream6 n (code.flatten.map (BitVec.ofNat 8))).isSome

/-- The hardware implementation of `machineAcceptsNatD`: `machineAcceptsNatImpl` on the data
arguments. -/
unsafe def machineAcceptsNatDImpl (code : List (List Nat)) (n : Nat)
    (_h : codeDecodes code n = true) (regs : List Nat) (regions : List (Nat × List Nat))
    (res : Nat) : Bool :=
  machineAcceptsNatImpl code n regs regions res

/-- `machineAcceptsNat` on literal data whose bytes decode. The extended checker's
machine-evaluation rule evaluates applications of this function only. The argument `h`
records that the bytes of `code.flatten` decode into `n` instructions, which the rule relies
on because the processor runs the bytes without decoding them; the kernel has checked `h`,
since the auxiliary definition containing the application is type-checked before the rule
fires. Compiled code runs the bytes on the host processor through `machineAcceptsNatImpl`. -/
@[implemented_by machineAcceptsNatDImpl]
def machineAcceptsNatD (code : List (List Nat)) (n : Nat) (_h : codeDecodes code n = true)
    (regs : List Nat) (regions : List (Nat × List Nat)) (res : Nat) : Bool :=
  machineAcceptsNat code n regs regions res

theorem machineAcceptsNatD_eq (code : List (List Nat)) (n : Nat) (h : codeDecodes code n = true)
    (regs : List Nat) (regions : List (Nat × List Nat)) (res : Nat) :
    machineAcceptsNatD code n h regs regions res = machineAcceptsNat code n regs regions res :=
  rfl

/-- `codeDecodes` transported along equations of its arguments. -/
theorem codeDecodes_of_eq {code code' : List (List Nat)} {n n' : Nat} (hc : code = code')
    (hn : n = n') (h : codeDecodes code n = true) : codeDecodes code' n' = true :=
  hc ▸ hn ▸ h

/-! ## The literal data of the initial state -/

/-- The sixteen registers of `initState L plan σ` as natural numbers, in SDM order. -/
def regsOf (L : Layout) (plan : RegPlan) (σ : FState) : List Nat :=
  (List.range 16).map fun k => (initRegs L plan σ (regName k)).toNat

/-- The regions of the spans `ts` from position `k`: the span at position `k` is the region
at byte address `8 * (arenaCell + k * spanStride + 1)` holding its cells little-endian. -/
def spanRegions (σ : FState) : Nat → List String → List (Nat × List Nat)
  | _, [] => []
  | k, t :: ts =>
      (8 * (arenaCell + k * spanStride + 1), (σ.bufs t).flatMap wordBytes) ::
        spanRegions σ (k + 1) ts

/-- The memory regions of `initState L plan σ`: the zero sink cell at `8 * arenaCell`, then
the cells of every span of the layout at their addresses. -/
def regionsOf (L : Layout) (_plan : RegPlan) (σ : FState) : List (Nat × List Nat) :=
  (8 * arenaCell, wordBytes 0) :: spanRegions σ 0 L.spans

/-! ## The literal state is the initial state -/

theorem gpNum?_eq_some {r : String} {k : Nat} (h : gpNum? r = some k) :
    k < 16 ∧ regName k = r := by
  unfold gpNum? at h
  split at h <;> first | (cases h; exact ⟨by decide, rfl⟩) | cases h

theorem gpNum?_regName {k : Nat} (hk : k < 16) : gpNum? (regName k) = some k := by
  interval_cases k <;> rfl

theorem wordBytes_length (v : BitVec 64) : (wordBytes v).length = 8 := by
  simp [wordBytes]

theorem wordBytes_getD (v : BitVec 64) {j : Nat} (hj : j < 8) :
    (wordBytes v).getD j 0 = v.toNat / 2 ^ (8 * j) % 256 := by
  simp [wordBytes, List.getD_eq_getElem?_getD, hj]

theorem length_flatMap_wordBytes (l : List (BitVec 64)) :
    (l.flatMap wordBytes).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons v l ih => simp only [List.flatMap_cons, List.length_append, wordBytes_length, ih,
      List.length_cons]; ring

theorem flatMap_wordBytes_getD :
    ∀ (l : List (BitVec 64)) {i j : Nat} (hi : i < l.length), j < 8 →
      (l.flatMap wordBytes).getD (8 * i + j) 0 = l[i].toNat / 2 ^ (8 * j) % 256
  | [], _, _, hi, _ => absurd hi (by simp)
  | v :: l, 0, j, _, hj => by
      rw [List.flatMap_cons, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [wordBytes_length]; omega), ← List.getD_eq_getElem?_getD]
      simpa using wordBytes_getD v hj
  | v :: l, i + 1, j, hi, hj => by
      rw [List.flatMap_cons, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [wordBytes_length]; omega), ← List.getD_eq_getElem?_getD,
        wordBytes_length, show 8 * (i + 1) + j - 8 = 8 * i + j by omega]
      exact flatMap_wordBytes_getD l (by simpa using hi) hj

/-- The byte `j` of an optional cell, `0` for none. -/
def cellByteOf (o : Option (BitVec 64)) (j : Nat) : Nat :=
  match o with
  | some v => v.toNat / 2 ^ (8 * j) % 256
  | none => 0

theorem regionByte_spanRegions (σ : FState) :
    ∀ (ts : List String) (k n : Nat), (∀ t ∈ ts, (σ.bufs t).length < spanStride) →
      regionByte n (spanRegions σ k ts) =
        if n / 8 < arenaCell + 1 + k * spanStride then 0 else
          cellByteOf ((ts[(n / 8 - arenaCell - 1) / spanStride - k]?).bind
            fun t => (σ.bufs t)[(n / 8 - arenaCell - 1) % spanStride]?) (n % 8)
  | [], k, n, _ => by
      simp only [spanRegions, regionByte, List.getElem?_nil, Option.bind_none, cellByteOf]
      split <;> rfl
  | t :: ts, k, n, hl => by
      have ht := hl t List.mem_cons_self
      have ih := regionByte_spanRegions σ ts (k + 1) n
        (fun t' h => hl t' (List.mem_cons_of_mem _ h))
      simp only [spanRegions, regionByte, length_flatMap_wordBytes]
      rw [show spanStride = 4294967296 from rfl] at ht ih ⊢
      by_cases hin : 8 * (arenaCell + k * 4294967296 + 1) ≤ n ∧
          n < 8 * (arenaCell + k * 4294967296 + 1) + 8 * (σ.bufs t).length
      · rw [ite_eq_left hin, ite_eq_right (by omega)]
        have hq1 : (n / 8 - arenaCell - 1) / 4294967296 = k := by omega
        have hq2 : (n / 8 - arenaCell - 1) % 4294967296 =
            n / 8 - arenaCell - 1 - k * 4294967296 := by omega
        have hn : n - 8 * (arenaCell + k * 4294967296 + 1) =
            8 * (n / 8 - arenaCell - 1 - k * 4294967296) + n % 8 := by omega
        have hi : n / 8 - arenaCell - 1 - k * 4294967296 < (σ.bufs t).length := by omega
        rw [hq1, Nat.sub_self, List.getElem?_cons_zero, Option.bind_some, hq2,
          List.getElem?_eq_getElem hi, cellByteOf, hn,
          flatMap_wordBytes_getD _ hi (Nat.mod_lt _ (by decide))]
      · rw [ite_eq_right hin, ih]
        by_cases h1 : n / 8 < arenaCell + 1 + k * 4294967296
        · rw [ite_eq_left h1, ite_eq_left (Nat.lt_of_lt_of_le h1
            (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _))]
        · rw [ite_eq_right h1]
          by_cases h2 : n / 8 < arenaCell + 1 + (k + 1) * 4294967296
          · rw [ite_eq_left h2]
            have hq1 : (n / 8 - arenaCell - 1) / 4294967296 = k := by omega
            have hq2 : (σ.bufs t).length ≤ (n / 8 - arenaCell - 1) % 4294967296 := by omega
            rw [hq1, Nat.sub_self, List.getElem?_cons_zero, Option.bind_some,
              List.getElem?_eq_none hq2]
            rfl
          · rw [ite_eq_right h2, show (n / 8 - arenaCell - 1) / 4294967296 - k =
              ((n / 8 - arenaCell - 1) / 4294967296 - (k + 1)) + 1 by omega,
              List.getElem?_cons_succ]

section Lit

variable {L : Layout} {plan : RegPlan} {σ : FState}

theorem regionByte_regionsOf (hlen : ∀ t ∈ L.spans, (σ.bufs t).length < spanStride)
    (n : Nat) :
    regionByte n (regionsOf L plan σ) =
      if n / 8 < arenaCell + 1 then 0 else
        cellByteOf ((L.spans[(n / 8 - arenaCell - 1) / spanStride]?).bind
          fun t => (σ.bufs t)[(n / 8 - arenaCell - 1) % spanStride]?) (n % 8) := by
  have h := regionByte_spanRegions σ L.spans 0 n hlen
  simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero] at h
  simp only [regionsOf, regionByte, wordBytes_length]
  split
  · rename_i hin
    rw [ite_eq_left (by omega)]
    simp only [wordBytes, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_range (by omega)]
    simp
  · exact h

theorem write64_zero_cell (v a : BitVec 64) :
    write64 (fun _ => 0) (BitVec.ofNat 64 (8 * (a.toNat / 8))) v a =
      BitVec.ofNat 8 (v.toNat / 2 ^ (8 * (a.toNat % 8)) % 256) := by
  have ha := a.isLt
  have hs : (a - BitVec.ofNat 64 (8 * (a.toNat / 8))).toNat = a.toNat % 8 := by
    rw [BitVec.toNat_sub, toNat_ofNat_of_lt (by omega)]
    omega
  simp only [write64, InRange8, hs, ite_eq_left (Nat.mod_lt _ (by decide : 8 > 0))]
  apply BitVec.eq_of_toNat_eq
  simp

theorem initMem_eq (a : BitVec 64) :
    initMem L σ a = BitVec.ofNat 8
      (if a.toNat / 8 < arenaCell + 1 then 0 else
        cellByteOf ((L.spans[(a.toNat / 8 - arenaCell - 1) / spanStride]?).bind
          fun t => (σ.bufs t)[(a.toNat / 8 - arenaCell - 1) % spanStride]?) (a.toNat % 8)) := by
  unfold initMem cellAt
  by_cases h : a.toNat / 8 ≤ arenaCell
  · rw [ite_eq_left h, ite_eq_left (by omega)]; rfl
  · rw [ite_eq_right h, ite_eq_right (by omega)]
    cases hs : L.spans[(a.toNat / 8 - arenaCell - 1) / spanStride]? with
    | none => rfl
    | some t =>
      simp only [Option.bind_some]
      cases hv : (σ.bufs t)[(a.toNat / 8 - arenaCell - 1) % spanStride]? with
      | none => rfl
      | some v => exact write64_zero_cell v a

theorem initRegs_of_gpNum?_none (hw : plan.wellFormed = true) {r : String}
    (h : gpNum? r = none) : initRegs L plan σ r = 0 := by
  unfold initRegs
  split
  · rename_i rk hf
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [beq_iff_eq] at hp
    have hk := ((RegPlan.wellFormed_spec hw).2.2 _ hm).1
    rw [← hp, gpNum?_regName hk] at h
    cases h
  · rfl

/-- **The literal state of the initial state.** For a well-formed plan and every span shorter
than `2 ^ 32` cells, the machine state of `regsOf L plan σ` and `regionsOf L plan σ` is
`initState L plan σ`. -/
theorem stateOfLit_eq (hw : plan.wellFormed = true)
    (hlen : ∀ t ∈ L.spans, (σ.bufs t).length < spanStride) :
    stateOfLit (regsOf L plan σ) (regionsOf L plan σ) = initState L plan σ := by
  unfold stateOfLit initState
  congr 1
  · funext r
    cases h : gpNum? r with
    | some k =>
      obtain ⟨hk, rfl⟩ := gpNum?_eq_some h
      simp [regsOf, List.getD_eq_getElem?_getD, hk]
    | none => exact (initRegs_of_gpNum?_none hw h).symm
  · funext a
    rw [regionByte_regionsOf hlen, initMem_eq]

/-- **Transfer of an accepting literal run.** For a well-formed plan, every span shorter than
`2 ^ 32` cells, literal bytes `code` whose byte values are `bytes`, and a register number `r`
naming `res`, an accepting `machineAcceptsNat` run on `regsOf` and `regionsOf` is an
accepting `machineAccepts` run from `initState L plan σ`. -/
theorem machineAccepts_of_lit (hw : plan.wellFormed = true)
    (hlen : ∀ t ∈ L.spans, (σ.bufs t).length < spanStride) {code : List (List Nat)}
    {bytes : List (BitVec 8)} {n r : Nat} {res : String}
    (hb : code.flatten.map (BitVec.ofNat 8) = bytes) (hr : regName r = res)
    (h : machineAcceptsNat code n (regsOf L plan σ) (regionsOf L plan σ) r = true) :
    machineAccepts bytes n (initState L plan σ) res = true := by
  rw [← hb, ← hr, ← stateOfLit_eq hw hlen]
  exact h

end Lit

/-! ## Chunked byte literals -/

/-- `chunksMatch cs l` holds when the chunks `cs`, read as bytes, are consecutive segments of
`l` covering it: the first chunk is the prefix of `l` of its length, and the remaining chunks
match the rest. Each step compares one chunk, so its evaluation nests no deeper than the
longest chunk. -/
def chunksMatch : List (List Nat) → List (BitVec 8) → Bool
  | [], l => l.isEmpty
  | c :: cs, l => (c.map (BitVec.ofNat 8) == l.take c.length) && chunksMatch cs (l.drop c.length)

/-- Chunks matching a byte list concatenate to it. -/
theorem flatten_map_eq_of_chunksMatch :
    ∀ (cs : List (List Nat)) (l : List (BitVec 8)),
      chunksMatch cs l = true → cs.flatten.map (BitVec.ofNat 8) = l
  | [], l, h => by
      simp only [chunksMatch, List.isEmpty_iff] at h
      simp [h]
  | c :: cs, l, h => by
      simp only [chunksMatch, Bool.and_eq_true, beq_iff_eq] at h
      rw [List.flatten_cons, List.map_append, h.1, flatten_map_eq_of_chunksMatch cs _ h.2,
        List.take_append_drop]

/-! ## Decision procedures with literal code -/

/-- A registered decision procedure with the literal byte values `codeLit` of its shipped
bytes, in chunks, the literal instruction count `nLit` of its compiled code, and the literal
SDM number `resLit` of its result register. -/
structure DecisionProcLit (α : Type) (P : α → Prop) extends DecisionProc α P where
  /-- The byte values of the shipped bytes, in chunks. -/
  codeLit : List (List Nat)
  /-- The number of compiled instructions. -/
  nLit : Nat
  /-- The SDM number of the result register. -/
  resLit : Nat
  /-- The concatenated literal chunks are the shipped bytes. -/
  code_eq : codeLit.flatten.map (BitVec.ofNat 8) = toDecisionProc.bytes
  /-- The literal count is the number of compiled instructions. -/
  n_eq : toDecisionProc.code.length = nLit
  /-- The literal register number names the result register. -/
  res_eq : regName resLit = toDecisionProc.resReg
  /-- The literal chunks decode into `nLit` instructions. -/
  decodes : codeDecodes codeLit nLit = true

/-- **The shipped bytes decode.** Literal chunks concatenating to the shipped bytes of a
registered procedure, and a literal count equal to its number of compiled instructions,
satisfy `codeDecodes`, by the byte round trip `compileProgL_roundtrip`. -/
theorem codeDecodes_of_eqs {α : Type} {P : α → Prop} (d : DecisionProc α P)
    {codeLit : List (List Nat)} {nLit : Nat}
    (hc : codeLit.flatten.map (BitVec.ofNat 8) = d.bytes) (hn : d.code.length = nLit) :
    codeDecodes codeLit nLit = true := by
  rw [codeDecodes, hc, ← hn, DecisionProc.bytes, DecisionProc.code, DecisionProc.alloc,
    compileProgL_roundtrip (allocOK_of_planCheck d.layoutOK d.planOK) d.cap d.prog d.fitsL
      d.litsFitL]
  rfl

/-- **Soundness of the literal machine run.** For a registered procedure with literal code
and an admissible input, an accepting `machineAcceptsNatD` run on the literal code and on the
literal data of the input's initial state proves the proposition. -/
theorem verifiedDecideLit_sound {α : Type} {P : α → Prop} (d : DecisionProcLit α P) (x : α)
    (ha : d.admit x = true)
    (h : machineAcceptsNatD d.codeLit d.nLit d.decodes (regsOf d.layout d.plan (d.toState x))
      (regionsOf d.layout d.plan (d.toState x)) d.resLit = true) : P x := by
  have hw := (planCheck_spec d.planOK).1
  refine verifiedDecide_sound d.toDecisionProc x ha ?_
  rw [d.n_eq]
  exact machineAccepts_of_lit hw (d.admit_lenLt x ha) d.code_eq d.res_eq h

/-! ## Raw literals -/

open Lean Meta

/-- The type `Nat × List Nat`. -/
meta def natListPairTy : Expr :=
  mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkApp (mkConst ``List [0]) (mkConst ``Nat))

/-- A list of natural numbers as raw literals. -/
meta def mkRawNatList (l : List Nat) : Expr :=
  l.foldr (fun n acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) (mkRawNatLit n) acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))

/-- The type `List Nat`. -/
meta def natListTy : Expr :=
  mkApp (mkConst ``List [0]) (mkConst ``Nat)

/-- A list of lists of natural numbers as raw literals: `List.cons` at `List Nat` over
`mkRawNatList` of each element. -/
meta def mkRawNatLists (l : List (List Nat)) : Expr :=
  l.foldr (fun c acc => mkApp3 (mkConst ``List.cons [0]) natListTy (mkRawNatList c) acc)
    (mkApp (mkConst ``List.nil [0]) natListTy)

/-- The maximal length of a chunk emitted by `nat_chunks%`. -/
meta def litChunkLen : Nat := 16

/-- The consecutive chunks of `l` of length `litChunkLen`, the last one possibly shorter. -/
meta partial def splitLitChunks (l : List Nat) : List (List Nat) :=
  if l.isEmpty then [] else l.take litChunkLen :: splitLitChunks (l.drop litChunkLen)

/-- A list of regions as raw literals. -/
meta def mkRawRegions (l : List (Nat × List Nat)) : Expr :=
  l.foldr (fun p acc => mkApp3 (mkConst ``List.cons [0]) natListPairTy
      (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat)
        (mkApp (mkConst ``List [0]) (mkConst ``Nat)) (mkRawNatLit p.1) (mkRawNatList p.2)) acc)
    (mkApp (mkConst ``List.nil [0]) natListPairTy)

/-- The term is built from raw natural-number literals, `List.nil`, `List.cons` and
`Prod.mk` only. -/
meta partial def isRawData (e : Expr) : Bool :=
  match e with
  | .lit (.natVal _) => true
  | _ =>
    if e.isAppOfArity ``List.nil 1 then true
    else if e.isAppOfArity ``List.cons 3 || e.isAppOfArity ``Prod.mk 4 then
      isRawData e.appFn!.appArg! && isRawData e.appArg!
    else false

open Elab Term in
/-- Evaluate a closed term of type `ty` by adding, compiling and evaluating an auxiliary
definition. -/
meta unsafe def evalClosed (α : Type) (ty e : Expr) : TermElabM α := do
  let auxName ← mkAuxName `_verified_decide_lit_data
  let decl := Declaration.defnDecl {
    name := auxName
    levelParams := []
    type := ty
    value := e
    hints := .abbrev
    safety := .safe }
  modifyEnv (markMeta · auxName)
  withOptions (fun o => ((o.setBool `Elab.async false).setBool `compiler.postponeCompile false
      ).setBool `compiler.relaxedMetaCheck true) do
    addAndCompile decl
  evalConst α auxName

open Elab Term in
/-- The raw literal of a closed term of type `Nat`, `List Nat`, `List (List Nat)` or
`List (Nat × List Nat)`, computed by evaluating it. -/
meta def evalNatData (e : Expr) : TermElabM Expr := do
  if e.hasFVar || e.hasMVar then
    throwError "nat_lits: the term has free variables or metavariables{indentExpr e}"
  let ty ← inferType e
  let natTy := Lean.mkConst ``Nat
  let listLists := mkApp (Lean.mkConst ``List [0]) natListTy
  let listPair := mkApp (Lean.mkConst ``List [0]) natListPairTy
  if ← isDefEq ty natTy then
    return mkRawNatLit (← unsafe evalClosed Nat natTy e)
  else if ← isDefEq ty natListTy then
    return mkRawNatList (← unsafe evalClosed (List Nat) natListTy e)
  else if ← isDefEq ty listLists then
    return mkRawNatLists (← unsafe evalClosed (List (List Nat)) listLists e)
  else if ← isDefEq ty listPair then
    return mkRawRegions (← unsafe evalClosed (List (Nat × List Nat)) listPair e)
  else
    throwError "nat_lits: the type is not `Nat`, `List Nat`, `List (List Nat)` or \
      `List (Nat × List Nat)`{indentExpr ty}"

/-- `nat_lits% e` is the value of the closed term `e` of type `Nat`, `List Nat`,
`List (List Nat)` or `List (Nat × List Nat)`, written with raw literals. -/
syntax (name := natLitsElab) "nat_lits% " term:max : term

open Elab Term in
/-- The elaborator of `nat_lits%`. -/
@[term_elab natLitsElab] meta def elabNatLits : TermElab := fun stx _ => do
  let e ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  evalNatData (← instantiateMVars e)

/-- `nat_chunks% e` is the value of the closed term `e : List Nat`, split into consecutive
chunks of `16` elements (the last one possibly shorter) and written as a `List (List Nat)`
of raw literals. -/
syntax (name := natChunksElab) "nat_chunks% " term:max : term

open Elab Term in
/-- The elaborator of `nat_chunks%`. -/
@[term_elab natChunksElab] meta def elabNatChunks : TermElab := fun stx _ => do
  let e ← elabTerm stx[1] natListTy
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar then
    throwError "nat_chunks: the term has free variables or metavariables{indentExpr e}"
  let l ← unsafe evalClosed (List Nat) natListTy e
  return mkRawNatLists (splitLitChunks l)

/-! ## The tactic -/

open Elab Tactic in
/-- Close a goal `machineAcceptsNatD a₁ a₂ h a₄ a₅ a₆ = true` with closed arguments: a data
argument `aᵢ` whose weak head normal form `rᵢ` is raw literal data (a projection of a
registered procedure whose field is defined by `nat_lits%`) is related to it by `rfl`; every
other data argument is evaluated to raw literals `rᵢ` and `aᵢ = rᵢ` is proved by
`decide +kernel`. The decoding proof `h'` is `h` when `r₁` and `r₂` are the weak head normal
forms of `a₁` and `a₂`, and `codeDecodes_of_eq e₁ e₂ h` otherwise. Then add the auxiliary
definition `aux := machineAcceptsNatD r₁ r₂ h' r₄ r₅ r₆`, compile and evaluate it, and on
`true` close the goal from `Lean.ofReduceBool aux true rfl`, the equations and
`machineAcceptsNatD_eq`. Fails with the machine's answer when the evaluation returns
`false`. -/
meta def evalMachineAcceptsLit (g : MVarId) : TacticM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq?
    | throwError "verified_decide_lit: the goal is not an equation{indentExpr ty}"
  unless lhs.isAppOfArity ``machineAcceptsNatD 6 && rhs.isConstOf ``Bool.true do
    throwError "verified_decide_lit: the goal is not `machineAcceptsNatD … = true`{indentExpr ty}"
  let args := lhs.getAppArgs
  let data := #[args[0]!, args[1]!, args[3]!, args[4]!, args[5]!]
  let hDec := args[2]!
  let mut raws : Array Expr := #[]
  let mut eqs : Array Expr := #[]
  let mut isRfl : Array Bool := #[]
  for a in data do
    let aw ← whnfD a
    if isRawData aw then
      raws := raws.push aw
      eqs := eqs.push (← mkExpectedTypeHint (← mkEqRefl aw) (← mkEq a aw))
      isRfl := isRfl.push true
    else
      let r ← evalNatData a
      let m ← mkFreshExprMVar (← mkEq a r)
      let rest ← Tactic.run m.mvarId! (evalTactic (← `(tactic| decide +kernel)))
      unless rest.isEmpty do
        throwError
          "verified_decide_lit: the literal equation is not closed{indentExpr (← mkEq a r)}"
      raws := raws.push r
      eqs := eqs.push (← instantiateMVars m)
      isRfl := isRfl.push false
  let hDec' ← if isRfl[0]! && isRfl[1]! then pure hDec
    else mkAppM ``codeDecodes_of_eq #[eqs[0]!, eqs[1]!, hDec]
  let val := mkAppN (mkConst ``machineAcceptsNatD) #[raws[0]!, raws[1]!, hDec', raws[2]!,
    raws[3]!, raws[4]!]
  let mut heqNat ← mkEqRefl (mkConst ``machineAcceptsNat)
  for e in eqs do
    heqNat ← mkCongr heqNat e
  let heq ← mkEqTrans
    (mkAppN (mkConst ``machineAcceptsNatD_eq) #[args[0]!, args[1]!, hDec, args[3]!, args[4]!,
      args[5]!])
    (← mkEqTrans heqNat (← mkEqSymm (mkAppN (mkConst ``machineAcceptsNatD_eq)
      #[raws[0]!, raws[1]!, hDec', raws[2]!, raws[3]!, raws[4]!])))
  let auxName ← Term.mkAuxName `_verified_decide_lit
  let decl := Declaration.defnDecl {
    name := auxName
    levelParams := []
    type := mkConst ``Bool
    value := val
    hints := .abbrev
    safety := .safe }
  modifyEnv (markMeta · auxName)
  withOptions (fun o => ((o.setBool `Elab.async false).setBool `compiler.postponeCompile false
      ).setBool `compiler.relaxedMetaCheck true) do
    addAndCompile decl
  let r ← unsafe evalConst Bool auxName
  unless r do
    throwError "verified_decide_lit: the machine returned false on{indentExpr lhs}"
  let prf := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxName) (mkConst ``Bool.true)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  g.assign (mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Bool) lhs val (mkConst ``Bool.true) heq
    prf)

/-- `machine_accepts_lit` closes `machineAcceptsNatD code n h regs regions res = true` for
closed arguments by reducing the data arguments to raw literals and asserting the machine's answer on those
literals through `Lean.ofReduceBool`. -/
syntax (name := machineAcceptsLitTac) "machine_accepts_lit" : tactic

open Elab Tactic in
/-- The elaborator of `machine_accepts_lit`. -/
@[tactic machineAcceptsLitTac] meta def evalMachineAcceptsLitTac : Tactic := fun _ => do
  evalMachineAcceptsLit (← getMainGoal)
  replaceMainGoal []

/-- `verified_decide_lit d` closes a goal `P x`, for a registered `d : DecisionProcLit α P`
and a concrete input `x`: it applies `verifiedDecideLit_sound d x`, decides admissibility of
`x` by `decide`, and closes the literal run by `machine_accepts_lit`. -/
macro "verified_decide_lit " d:term : tactic =>
  `(tactic| (refine verifiedDecideLit_sound $d _ (by decide) ?_; machine_accepts_lit))


end VerifiedEval

end
