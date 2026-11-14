import MemM1.WalkK2
import MemM1.ConsumerV3F
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
namespace MemM1.ConsumerB
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.Witness MemM1.WalkFactV MemM1.ConsumerV2 MemM1.ConsumerD
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2
open ArmCert.Premises.TranslationAgreesV3 (TTWReadsOK)
open ArmCert.Eval.M1a.WEv (WalkFactE)
open ArmCert.Eval.M1a.B2 (WalkFactE2)
open MemM1.WalkKE (walkK)
open MemM1.WalkK2 (walkK2)
open MemM1.LeafFactsL2 (blockBase blockBase_aligned)
open MemM1.LeafFactsG (leafBase leafBase_aligned)

/-! A consumer map with both 4 KB pages and 2 MB blocks. `P2` is keyed by the block number
`va >>> 21`, `P4` by the page number `va >>> 12`; a block entry takes precedence over pages in
its 2 MB range. The walk reads 3 slots for a block and 4 for a page. -/

def kmapB (P4 P2 : BitVec 64 → Option Page) : ConsumerMap where
  pa va := match P2 (va >>> 21) with
    | some b => MemM1.VA2.blockOA (blockBase b.leaf) va
    | none => (kmap P4).pa va
  permitted va acc _ size := va.toNat < 2^48 ∧ 0 < size ∧
    ((∃ b, P2 (va >>> 21) = some b ∧ (va.toNat % 2097152 : Int) + size ≤ 2097152 ∧
        (if b.code then MemM1.WitnessIF.AccIF acc else Acc0 acc)) ∨
     (P2 (va >>> 21) = none ∧ (va.toNat % 4096 : Int) + size ≤ 4096 ∧
        ∃ p, P4 (va >>> 12) = some p ∧ (if p.code then MemM1.WitnessIF.AccIF acc else Acc0 acc)))
  tableByte _ := False

/-- The walk's PA sequence: 3 slots in a block, 4 slots on a page. -/
def walkB (r : Regs) (mem : S1ResourcePath.Memory) (P2 : BitVec 64 → Option Page)
    (va : BitVec 64) : List Nat :=
  match P2 (va >>> 21) with
  | some _ => walkK2 r mem va
  | none => walkK r mem va

theorem ttw_congr {w1 w2 : BitVec 64 → List Nat} {va : BitVec 64} {W : Array Event}
    (h : w1 va = w2 va) (hW : TTWReadsOK w2 va W) : TTWReadsOK w1 va W := by
  unfold TTWReadsOK at hW ⊢
  rw [h]; exact hW

/-- **E17 v3 for a map with 4 KB pages and 2 MB blocks.** -/
theorem agreesV3_kmapB_full (s : State) (hR : Regs20 s.regs)
    (hC : _get_SCTLR_EL2_Type_C (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (hI : _get_SCTLR_EL2_Type_I (s.regs.bank_BitVec_64 .SCTLR_EL2) = 1#1)
    (P4 P2 : BitVec 64 → Option Page)
    (hP4 : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P2 (va >>> 21) = none →
      P4 (va >>> 12) = some p →
      WalkFactE s va p.leaf ∧ (if p.code then LeafBitsC p.leaf else LeafBitsD p.leaf))
    (hP2 : ∀ (va : BitVec 64) (b : Page), va.toNat < 2^48 → P2 (va >>> 21) = some b →
      WalkFactE2 s va b.leaf ∧ (if b.code then LeafBitsC b.leaf else LeafBitsD b.leaf)) :
    ArmCert.Premises.TranslationAgreesV3.TranslationAgrees (kmapB P4 P2)
      (walkB s.regs s.mem P2) s := by
  intro u hu hum va acc al size ⟨hva, _, hrest⟩
  rcases hrest with ⟨b, h2, _, hacc⟩ | ⟨h2, _, p, h4, hacc⟩
  · have hpa : (kmapB P4 P2).pa va = MemM1.VA2.blockOA (blockBase b.leaf) va := by
      simp only [kmapB, h2]
    have hw : walkB s.regs s.mem P2 va = walkK2 s.regs s.mem va := by simp only [walkB, h2]
    rcases hP2 va b hva h2 with ⟨hW, hD⟩
    rw [hpa]
    cases hc : b.code
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hacc hD
      rcases MemM1.WalkK2.tr_dataE2 s hR hC va hva b.leaf hW hD acc hacc al size u hu hum with
        ⟨ad, t, h, hf, hpa', hmt, hin, hout, hv, hif, hnd, hm, ti, W, he, hRW⟩
      exact ⟨ad, t, h, hf, hpa', hmt, hin, hout, hv, hif, hnd, hm, ti, W, he, ttw_congr hw hRW⟩
    · simp only [hc, ↓reduceIte] at hacc hD
      rcases MemM1.WalkK2.tr_ifE2 s hR hI va hva b.leaf hW hD acc hacc al size u hu hum with
        ⟨ad, t, h, hf, hpa', hmt, hin, hout, hv, hif, hnd, hm, ti, W, he, hRW⟩
      exact ⟨ad, t, h, hf, hpa', hmt, hin, hout, hv, hif, hnd, hm, ti, W, he, ttw_congr hw hRW⟩
  · have hpa : (kmapB P4 P2).pa va = MemM1.VA.pageOA (leafBase p.leaf) va := by
      simp only [kmapB, h2, kmap, h4]
    have hw : walkB s.regs s.mem P2 va = walkK s.regs s.mem va := by simp only [walkB, h2]
    rcases hP4 va p hva h2 h4 with ⟨hW, hD⟩
    rw [hpa]
    cases hc : p.code
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hacc hD
      rcases MemM1.WalkKE.tr_dataE s hR hC va hva p.leaf hW hD acc hacc al size u hu hum with
        ⟨ad, t, h, hf, hpa', hmt, hin, hout, hv, hif, hnd, hm, ti, W, he, hRW⟩
      exact ⟨ad, t, h, hf, hpa', hmt, hin, hout, hv, hif, hnd, hm, ti, W, he, ttw_congr hw hRW⟩
    · simp only [hc, ↓reduceIte] at hacc hD
      rcases MemM1.TrIFE.tr_ifE s hR hI va hva p.leaf hW hD acc hacc al size u hu hum with
        ⟨ad, t, h, hf, hpa', hmt, hin, hout, hv, _, hif, hnd, hm, ti, W, he, hRW⟩
      exact ⟨ad, t, h, hf, hpa', hmt, hin, hout, hv, hif, hnd, hm, ti, W, he, ttw_congr hw hRW⟩

/-! ### Arithmetic for blocks -/

theorem ushr21_toNat (v : BitVec 64) : (v >>> 21).toNat = v.toNat / 2097152 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem add_block (v : BitVec 64) (i : Nat) (hv : v.toNat < 2^48)
    (hi : v.toNat % 2097152 + i < 2097152) : (v + BitVec.ofNat 64 i) >>> 21 = v >>> 21 := by
  have ha : (v + BitVec.ofNat 64 i).toNat = v.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : i % 2^64 = i := Nat.mod_eq_of_lt (by omega)
    rw [h1]; exact Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [ushr21_toNat, ushr21_toNat, ha]
  omega

theorem blockOA_toNat (B : BitVec 56) (a : BitVec 64) (hB : B.toNat % 2097152 = 0) :
    (MemM1.VA2.blockOA B a).toNat = B.toNat + a.toNat % 2097152 := by
  have hB' : B &&& 0x1fffff#56 = 0#56 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x1fffff#56 : BitVec 56).toNat = 2 ^ 21 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, hB]
    rfl
  have hc : (a.setWidth 56 &&& 0x1fffff#56).toNat = a.toNat % 2097152 := by
    rw [BitVec.toNat_and, show (0x1fffff#56 : BitVec 56).toNat = 2 ^ 21 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth]
    exact Nat.mod_mod_of_dvd _ (by decide)
  have hand : B &&& (a.setWidth 56 &&& 0x1fffff#56) = 0#56 := by
    rw [BitVec.and_comm (a.setWidth 56), ← BitVec.and_assoc, hB', BitVec.zero_and]
  unfold MemM1.VA2.blockOA
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand, BitVec.toNat_add, hc]
  have := B.isLt
  exact Nat.mod_eq_of_lt (by omega)

theorem paB_block (P4 P2 : BitVec 64 → Option Page) (v : BitVec 64) (b : Page)
    (h : P2 (v >>> 21) = some b) :
    ((kmapB P4 P2).pa v).toNat = (blockBase b.leaf).toNat + v.toNat % 2097152 := by
  have : (kmapB P4 P2).pa v = MemM1.VA2.blockOA (blockBase b.leaf) v := by simp only [kmapB, h]
  rw [this, blockOA_toNat _ _ (blockBase_aligned _)]

theorem paB_page (P4 P2 : BitVec 64 → Option Page) (v : BitVec 64) (p : Page)
    (h2 : P2 (v >>> 21) = none) (h4 : P4 (v >>> 12) = some p) :
    ((kmapB P4 P2).pa v).toNat = (leafBase p.leaf).toNat + v.toNat % 4096 := by
  have : (kmapB P4 P2).pa v = (kmap P4).pa v := by simp only [kmapB, h2]
  rw [this, pa_toNat P4 v p h4]

theorem paB_none (P4 P2 : BitVec 64 → Option Page) (v : BitVec 64)
    (h2 : P2 (v >>> 21) = none) (h4 : P4 (v >>> 12) = none) : (kmapB P4 P2).pa v = 0#56 := by
  simp only [kmapB, kmap, h2, h4]

/-- A permitted byte is in a mapped block, or on a mapped page outside every block. -/
theorem permB_info (P4 P2 : BitVec 64 → Option Page) (a : BitVec 64) (h : PermVA (kmapB P4 P2) a) :
    a.toNat < 2^48 ∧ ((∃ b, P2 (a >>> 21) = some b) ∨
      (P2 (a >>> 21) = none ∧ ∃ p, P4 (a >>> 12) = some p)) := by
  rcases h with ⟨va, acc, al, size, i, ⟨hva, _, hr⟩, hi, rfl⟩
  rcases hr with ⟨b, h2, hsz, _⟩ | ⟨h2, hsz, p, h4, _⟩
  · have hi' : va.toNat % 2097152 + i < 2097152 := by omega
    have hb := add_block va i hva hi'
    have ht : (va + BitVec.ofNat 64 i).toNat = va.toNat + i := by
      have := congrArg BitVec.toNat hb
      rw [ushr21_toNat, ushr21_toNat] at this
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨by rw [ht]; omega, Or.inl ⟨b, by rw [hb]; exact h2⟩⟩
  · have hi' : va.toNat % 4096 + i < 4096 := by omega
    have hb : (va + BitVec.ofNat 64 i) >>> 21 = va >>> 21 := add_block va i hva (by omega)
    refine ⟨by rw [add_toNat va i hva hi']; omega, Or.inr ⟨by rw [hb]; exact h2, p, ?_⟩⟩
    rw [add_page va i hva hi']; exact h4

/-- **MapOK for the page + block map.** Frames: distinct page frames, distinct block frames, no
    page frame inside a block frame, and no frame at PA 0. -/
theorem mapOK_B (P4 P2 : BitVec 64 → Option Page)
    (hinj4 : ∀ n1 n2 p1 p2, P4 n1 = some p1 → P4 n2 = some p2 →
      leafBase p1.leaf = leafBase p2.leaf → n1 = n2)
    (hinj2 : ∀ n1 n2 b1 b2, P2 n1 = some b1 → P2 n2 = some b2 →
      blockBase b1.leaf = blockBase b2.leaf → n1 = n2)
    (hsep : ∀ n p m b, P4 n = some p → P2 m = some b →
      (leafBase p.leaf).toNat / 2097152 ≠ (blockBase b.leaf).toNat / 2097152)
    (hnz4 : ∀ n p, P4 n = some p → leafBase p.leaf ≠ 0#56)
    (hnz2 : ∀ n b, P2 n = some b → blockBase b.leaf ≠ 0#56) :
    MapOK (kmapB P4 P2) := by
  have injFP : ∀ a b, PermVA (kmapB P4 P2) a → (kmapB P4 P2).pa b = (kmapB P4 P2).pa a → b = a := by
    intro a b ha hab
    have he := congrArg BitVec.toNat hab
    rcases permB_info P4 P2 a ha with ⟨_, ⟨ba, h2a⟩ | ⟨h2a, pa', h4a⟩⟩
    · rw [paB_block P4 P2 a ba h2a] at he
      have hA := blockBase_aligned ba.leaf
      have hz : (blockBase ba.leaf).toNat ≠ 0 := fun h0 => hnz2 _ _ h2a (BitVec.eq_of_toNat_eq h0)
      cases h2b : P2 (b >>> 21) with
      | some bb =>
        rw [paB_block P4 P2 b bb h2b] at he
        have hB := blockBase_aligned bb.leaf
        have hbase : blockBase bb.leaf = blockBase ba.leaf := by
          apply BitVec.eq_of_toNat_eq; omega
        have hn := congrArg BitVec.toNat (hinj2 _ _ _ _ h2b h2a hbase)
        rw [ushr21_toNat, ushr21_toNat] at hn
        apply BitVec.eq_of_toNat_eq; omega
      | none =>
        cases h4b : P4 (b >>> 12) with
        | some pb =>
          rw [paB_page P4 P2 b pb h2b h4b] at he
          have hB := leafBase_aligned pb.leaf
          exact absurd (by omega) (hsep _ _ _ _ h4b h2a)
        | none =>
          rw [paB_none P4 P2 b h2b h4b] at he
          simp at he; omega
    · rw [paB_page P4 P2 a pa' h2a h4a] at he
      have hA := leafBase_aligned pa'.leaf
      have hz : (leafBase pa'.leaf).toNat ≠ 0 := fun h0 => hnz4 _ _ h4a (BitVec.eq_of_toNat_eq h0)
      cases h2b : P2 (b >>> 21) with
      | some bb =>
        rw [paB_block P4 P2 b bb h2b] at he
        have hB := blockBase_aligned bb.leaf
        exact absurd (by omega) (hsep _ _ _ _ h4a h2b)
      | none =>
        cases h4b : P4 (b >>> 12) with
        | some pb =>
          rw [paB_page P4 P2 b pb h2b h4b] at he
          have hB := leafBase_aligned pb.leaf
          have hbase : leafBase pb.leaf = leafBase pa'.leaf := by
            apply BitVec.eq_of_toNat_eq; omega
          have hn := congrArg BitVec.toNat (hinj4 _ _ _ _ h4b h4a hbase)
          rw [ushr12_toNat, ushr12_toNat] at hn
          apply BitVec.eq_of_toNat_eq; omega
        | none =>
          rw [paB_none P4 P2 b h2b h4b] at he
          simp at he; omega
  refine ⟨?_, fun _ _ h => h, fun a b _ hb hab => injFP b a hb hab, injFP⟩
  · intro va acc al size i ⟨hva, _, hr⟩ hi
    rcases hr with ⟨b, h2, hsz, _⟩ | ⟨h2, hsz, p, h4, _⟩
    · have hi' : va.toNat % 2097152 + i < 2097152 := by omega
      have hb := add_block va i hva hi'
      rw [paB_block P4 P2 _ b (by rw [hb]; exact h2), paB_block P4 P2 va b h2]
      have ht : (va + BitVec.ofNat 64 i).toNat = va.toNat + i := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      rw [ht]; omega
    · have hi' : va.toNat % 4096 + i < 4096 := by omega
      have hb : (va + BitVec.ofNat 64 i) >>> 21 = va >>> 21 := add_block va i hva (by omega)
      rw [paB_page P4 P2 _ p (by rw [hb]; exact h2) (by rw [add_page va i hva hi']; exact h4),
        paB_page P4 P2 va p h2 h4, add_toNat va i hva hi']
      omega

#print axioms agreesV3_kmapB_full
#print axioms blockOA_toNat
#print axioms permB_info
#print axioms mapOK_B
end MemM1.ConsumerB
