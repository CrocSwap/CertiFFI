import M1a.TcrBits
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a.PP
abbrev State := SequentialState Regs oracleChoiceSource
open S1OuterSetup S1LogicalReference ArmCert.Eval.M1a ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.WEv
open ArmCert.Eval.M1a.TB ArmCert.Eval.JointSAT

/- Page-level walk facts: one logical Path for va gives the walk fact for every
   va' in the same 4K page (va'[63:12] = va[63:12]), since the walk indices, the VA range and
   the root slot read only VA bits 12 and up. The leaf OA range check reads the page offset,
   so it stays a per-va' hypothesis. -/

theorem entryIndex_page {va va' : BitVec 64} (h : va'.toNat / 4096 = va.toNat / 4096)
    {level : Nat} (bits : Nat) (hl : level ≤ 3) : entryIndex va' level bits = entryIndex va level bits := by
  unfold entryIndex
  have e : 2 ^ (12 + 9 * (3 - level)) = 4096 * 2 ^ (9 * (3 - level)) := by
    rw [Nat.pow_add]
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

theorem entryAddress_page {va va' : BitVec 64} (h : va'.toNat / 4096 = va.toNat / 4096)
    (base : BitVec 48) {level : Nat} (bits : Nat) (hl : level ≤ 3) :
    entryAddress base va' level bits = entryAddress base va level bits := by
  unfold entryAddress; rw [entryIndex_page h bits hl]

/-- A logical Path for va is a Path for every va' in the same 4K page. -/
theorem path_page {observe : Observation} {paBits : Nat} {va va' : BitVec 64}
    (h : va'.toNat / 4096 = va.toNat / 4096) {level bits : Nat} {base : BitVec 48}
    {result : PathEnd} (p : Path observe paBits va level bits base result) :
    Path observe paBits va' level bits base result := by
  induction p with
  | invalid level bits base physical view hl aligned present kind =>
    rw [← entryAddress_page h base bits hl] at aligned present
    exact .invalid level bits base physical view hl aligned present kind
  | leaf level bits base physical view hl aligned present kind =>
    have e := entryAddress_page h base bits hl
    rw [← e] at aligned present
    rw [← e]
    exact .leaf level bits base physical view hl aligned present kind
  | range level bits base physical view hl aligned present kind outOfRange =>
    rw [← entryAddress_page h base bits (by omega)] at aligned present
    rw [← entryAddress_page h (childBase view) 9 (by omega)] at outOfRange
    exact .range level bits base physical view hl aligned present kind outOfRange
  | table level bits base physical view result hl aligned present kind inRange next ih =>
    rw [← entryAddress_page h base bits (by omega)] at aligned present
    rw [← entryAddress_page h (childBase view) 9 (by omega)] at inRange
    exact .table level bits base physical view result hl aligned present kind inRange ih

theorem testBit_page {va va' : BitVec 64} (h : va'.toNat / 4096 = va.toNat / 4096) (i : Nat)
    (hi : 12 ≤ i) : va'.getLsbD i = va.getLsbD i := by
  have key : ∀ x : Nat, x.testBit i = (x / 4096).testBit (i - 12) := by
    intro x
    rw [show (4096 : Nat) = 2 ^ 12 from rfl, Nat.testBit_div_two_pow]
    congr 1; omega
  simp only [BitVec.getLsbD]
  rw [key, key, h]

theorem varange_page {va va' : BitVec 64} (h : va'.toNat / 4096 = va.toNat / 4096) :
    AArch64_GetVARange va' = AArch64_GetVARange va := by
  have hb := testBit_page h 55 (by omega)
  have hb' : va'[55]! = va[55]! := by
    first | exact hb | (simp only [BitVec.getElem!_eq_getLsbD]; exact hb) | simpa using hb
  unfold AArch64_GetVARange
  simp only [BitVec.access]
  exact congrArg (fun b : Bool => if (BitVec.setWidth 1 (BitVec.join1 [BitVec.ofBool b]) == 0#1) = true
    then VARange.VARange_LOWER else VARange.VARange_UPPER) hb'

theorem rootSlot_page {va va' : BitVec 64} (h : va'.toNat / 4096 = va.toNat / 4096) (r : Regs) :
    rootSlot r va' = rootSlot r va := by
  have hr : AArch64_GetVARange va' = AArch64_GetVARange va := varange_page h
  have hx : va'.extractLsb' 39 9 = va.extractLsb' 39 9 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact testBit_page h (39 + i) (by omega)
  unfold rootSlot S1InitialEntryAddress.address rootOf S1EntryRoot.word
  simp only [hr, hx]

theorem translate_walk_path_evT_page (s : State) (h : Host20T s) (va : BitVec 64)
    (hvr : AArch64_GetVARange va = .VARange_LOWER)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (hRootIn : (!is_zero_subrange (rootSlot s.regs va).address 55 48) = false)
    (observe : Observation)
    (available : Available observe (fun p => S2TableRAM.OrdinaryRAM p.address))
    (realizes : Realizes observe false false true true (fun a => s.mem[a]?))
    (identity : S1EntryPathSlots.Identity observe)
    (htab : ∀ l p v d, observe l p v → BytesAt false (fun a => s.mem[a]?) p d →
      ∀ level : Nat, descriptorKind level v.stable = .ok .table → TablePermsZero d)
    (slotL : Nat) (physL : FullAddress) (vL : S1DescriptorPIE.View 64)
    (path : Path observe 48 va 0 9 ((rootOf s.regs va).setWidth 48) (.leaf 3 slotL physL vL))
    (D : BitVec 64) (hD : BytesAt false (fun a => s.mem[a]?) physL D)
    (hleaf : S1Contiguous.bit D = 0#1 ∧ BitVec.join1 [BitVec.access D 10] = 1#1 ∧
      ∀ v : TTWState, v.level = 3 → v.baseaddress.address = S1LeafBaseFrame.base D 3 →
        (!is_zero_subrange (S1StageOA.address va v).address 55 48) = false) :
    ∀ va' : BitVec 64, va'.toNat / 4096 = va.toNat / 4096 →
      (∀ v : TTWState, v.level = 3 → v.baseaddress.address = S1LeafBaseFrame.base D 3 →
        (!is_zero_subrange (S1StageOA.address va' v).address 55 48) = false) →
      WalkFactE s va' D  := by
  intro va' hpage hleaf'
  have hvr' : AArch64_GetVARange va' = .VARange_LOWER := by rw [varange_page hpage]; exact hvr
  have hRoot' : (!is_zero_subrange (rootSlot s.regs va').address 55 48) = false := by
    rw [rootSlot_page hpage]; exact hRootIn
  have hroot : rootOf s.regs va' = rootOf s.regs va := by
    unfold rootOf S1EntryRoot.word; simp only [varange_page hpage]
  exact translate_walk_path_evT s h va' hvr' hEPD0 hRoot' observe available realizes identity htab
    slotL physL vL (by rw [hroot]; exact path_page hpage path) D hD ⟨hleaf.1, hleaf.2.1, hleaf'⟩

theorem extractLsb_page {va va' : BitVec 64} (h : va'.toNat / 4096 = va.toNat / 4096)
    (hi lo : Nat) (hlo : 12 ≤ lo) :
    Sail.BitVec.extractLsb va' hi lo = Sail.BitVec.extractLsb va hi lo := by
  unfold Sail.BitVec.extractLsb
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [BitVec.getLsbD_extractLsb, hi', decide_true, Bool.true_and]
  exact testBit_page h (lo + i) (by omega)

theorem nextSlot_page {va va' : BitVec 64} (h : va'.toNat / 4096 = va.toNat / 4096)
    (level : Int) (hl : 0 ≤ level ∧ level ≤ 2) (d : BitVec 64) :
    S1ResourcePath.nextSlot va' level d = S1ResourcePath.nextSlot va level d := by
  unfold S1ResourcePath.nextSlot
  generalize ({address := S1NextTable10Facts.base d, paspace := .PAS_NonSecure} : FullAddress) = tb
  have hc : level = 0 ∨ level = 1 ∨ level = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · show S2NextEntryFrame.address (0 + 1) va' _ = S2NextEntryFrame.address (0 + 1) va _
    calc S2NextEntryFrame.address (0 + 1) va' tb
        = {tb with address := tb.address |||
            Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb va' 38 30) +++ (0#3)) 56} := rfl
      _ = {tb with address := tb.address |||
            Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb va 38 30) +++ (0#3)) 56} := by
          rw [extractLsb_page h 38 30 (by decide)]
      _ = S2NextEntryFrame.address (0 + 1) va tb := rfl
  · show S2NextEntryFrame.address (1 + 1) va' _ = S2NextEntryFrame.address (1 + 1) va _
    calc S2NextEntryFrame.address (1 + 1) va' tb
        = {tb with address := tb.address |||
            Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb va' 29 21) +++ (0#3)) 56} := rfl
      _ = {tb with address := tb.address |||
            Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb va 29 21) +++ (0#3)) 56} := by
          rw [extractLsb_page h 29 21 (by decide)]
      _ = S2NextEntryFrame.address (1 + 1) va tb := rfl
  · show S2NextEntryFrame.address (2 + 1) va' _ = S2NextEntryFrame.address (2 + 1) va _
    calc S2NextEntryFrame.address (2 + 1) va' tb
        = {tb with address := tb.address |||
            Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb va' 20 12) +++ (0#3)) 56} := rfl
      _ = {tb with address := tb.address |||
            Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb va 20 12) +++ (0#3)) 56} := by
          rw [extractLsb_page h 20 12 (by decide)]
      _ = S2NextEntryFrame.address (2 + 1) va tb := rfl

/-- A Walk20 exact-bytes path for va is one for every va' in the same 4K page. -/
theorem walk20_page {wp : S1TTWParams} {va va' : BitVec 64} {mem : S1ResourcePath.Memory}
    (h : va'.toNat / 4096 = va.toNat / 4096) {n : Nat} {level : Int} {slot : FullAddress}
    {L : Int} {S : FullAddress} {D : BitVec 64}
    (w : Walk20 wp va mem n level slot L S D) : Walk20 wp va' mem n level slot L S D := by
  induction w with
  | leaf bounds ram desc hleaf => exact .leaf bounds ram desc hleaf
  | @table n level slot data L S D bounds ram desc htable range hperm rest ih =>
    have hl3 := S1DecodeFacts.table_before_final _ level bounds.2 htable
    have e := nextSlot_page h level ⟨bounds.1, by omega⟩ (S2FetchFrame.decoded wp.ee data)
    rw [← e] at range ih
    exact .table bounds ram desc htable range hperm ih

#print axioms path_page
#print axioms walk20_page
#print axioms rootSlot_page
#print axioms translate_walk_path_evT_page
end ArmCert.Eval.M1a.PP
