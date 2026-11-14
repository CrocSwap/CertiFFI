import MemM1.WalkFactV
import BridgeV2.ConsumerMap
import BridgeV2.BoundaryV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
open ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to MemM1.ConsumerV2LNSym.
namespace MemM1.ConsumerV2

abbrev State := SequentialState Regs oracleChoiceSource

/-! Page-keyed consumer map for eval's Boundary v2.

A page table `P` sends a VA page number (`va >>> 12`) to a stored level-3 leaf descriptor and a
code flag. Data pages permit EL0 NS GPR data accesses (`Witness.Acc0`), code pages permit EL0 NS
instruction fetches (`WitnessIF.AccIF`); every permitted access lies inside one 4K page below 2^48.
PA = leaf base ||| page offset; no table bytes. -/

/-- One mapped 4K page: its stored level-3 leaf descriptor and whether it is a code page. -/
structure Page where
  leaf : BitVec 64
  code : Bool

/-- The page-keyed consumer map. -/
def kmap (P : BitVec 64 → Option Page) : ConsumerMap where
  pa va := match P (va >>> 12) with
    | some p => MemM1.VA.pageOA (MemM1.LeafFactsG.leafBase p.leaf) va
    | none => 0#56
  permitted va acc _ size := va.toNat < 2^48 ∧ 0 < size ∧ (va.toNat % 4096 : Int) + size ≤ 4096 ∧
    ∃ p, P (va >>> 12) = some p ∧
      (if p.code then MemM1.WitnessIF.AccIF acc else MemM1.Witness.Acc0 acc)
  tableByte _ := False

theorem pa_eq (P : BitVec 64 → Option Page) (va : BitVec 64) (p : Page)
    (h : P (va >>> 12) = some p) :
    (kmap P).pa va = MemM1.VA.pageOA (MemM1.LeafFactsG.leafBase p.leaf) va := by
  simp only [kmap, h]

/-! ### Arithmetic -/

theorem ushr12_toNat (v : BitVec 64) : (v >>> 12).toNat = v.toNat / 4096 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- (L1) adding an in-page offset. -/
theorem add_toNat (v : BitVec 64) (i : Nat) (hv : v.toNat < 2^48) (hi : v.toNat % 4096 + i < 4096) :
    (v + BitVec.ofNat 64 i).toNat = v.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 : i % 2^64 = i := Nat.mod_eq_of_lt (by omega)
  rw [h1]; exact Nat.mod_eq_of_lt (by omega)

theorem add_page (v : BitVec 64) (i : Nat) (hv : v.toNat < 2^48) (hi : v.toNat % 4096 + i < 4096) :
    (v + BitVec.ofNat 64 i) >>> 12 = v >>> 12 := by
  apply BitVec.eq_of_toNat_eq
  rw [ushr12_toNat, ushr12_toNat, add_toNat v i hv hi]
  omega

theorem and_fff (B : BitVec 56) (hB : B.toNat % 4096 = 0) : B &&& 0xfff#56 = 0#56 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xfff#56 : BitVec 56).toNat = 2 ^ 12 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, hB]
  rfl

/-- (L2) the page output address as a sum. -/
theorem pageOA_toNat (B : BitVec 56) (a : BitVec 64) (hB : B.toNat % 4096 = 0) :
    (MemM1.VA.pageOA B a).toNat = B.toNat + a.toNat % 4096 := by
  have hc : (a.setWidth 56 &&& 0xfff#56).toNat = a.toNat % 4096 := by
    rw [BitVec.toNat_and, show (0xfff#56 : BitVec 56).toNat = 2 ^ 12 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth]
    exact Nat.mod_mod_of_dvd _ (by decide)
  have hand : B &&& (a.setWidth 56 &&& 0xfff#56) = 0#56 := by
    rw [BitVec.and_comm (a.setWidth 56), ← BitVec.and_assoc, and_fff B hB, BitVec.zero_and]
  unfold MemM1.VA.pageOA
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand, BitVec.toNat_add, hc]
  have := B.isLt
  exact Nat.mod_eq_of_lt (by omega)

theorem leafBase_and (D : BitVec 64) : MemM1.LeafFactsG.leafBase D &&& 0xfff#56 = 0#56 :=
  and_fff _ (MemM1.LeafFactsG.leafBase_aligned D)

theorem pa_toNat (P : BitVec 64 → Option Page) (va : BitVec 64) (p : Page)
    (h : P (va >>> 12) = some p) :
    ((kmap P).pa va).toNat = (MemM1.LeafFactsG.leafBase p.leaf).toNat + va.toNat % 4096 := by
  rw [pa_eq P va p h, pageOA_toNat _ _ (MemM1.LeafFactsG.leafBase_aligned _)]

/-! ### Registers: clrGP keeps the projected registers -/

theorem projRegsEq_clrGP (R : Regs) : ProjRegsEq R (MemM1.IF.clrGP R) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### TranslationAgrees -/

theorem agreesK (s : State) (hR : MemM1.Witness.Regs20 s.regs) (P : BitVec 64 → Option Page)
    (hP : ∀ (va : BitVec 64) (p : Page), va.toNat < 2^48 → P (va >>> 12) = some p →
      MemM1.WalkFactV.WalkFact s va p.leaf ∧
      (if p.code then MemM1.WalkFactV.LeafBitsC p.leaf else MemM1.WalkFactV.LeafBits p.leaf)) :
    TranslationAgrees (kmap P) s := by
  intro va acc aligned size ⟨hva, _, _, p, hp, hacc⟩
  rcases hP va p hva hp with ⟨hW, hD⟩
  rw [pa_eq P va p hp]
  cases hc : p.code
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hacc hD
    rcases MemM1.WitnessV.coreV va hva _ (leafBase_and p.leaf) acc aligned size s hR hacc
        (MemM1.WalkFactV.walkOKV_of s va p.leaf hW hD acc hacc) with
      ⟨ad, t, h, hf, hpa, hmt, hr, hm⟩
    refine ⟨ad, t, h, hf, hpa, hmt, ?_, fun a _ => by rw [hm]⟩
    rw [hr]; exact ProjRegsEq.refl _
  · simp only [hc, ↓reduceIte] at hacc hD
    rcases MemM1.WitnessIF.coreIF va hva _ (leafBase_and p.leaf) acc aligned size s hR hacc
        (MemM1.WalkFactV.walkOKIF_of s va p.leaf hW hD acc hacc) with
      ⟨ad, t, h, hf, hpa, hmt, hr, hm⟩
    refine ⟨ad, t, h, hf, hpa, hmt, ?_, fun a _ => by rw [hm]⟩
    rw [hr]; exact projRegsEq_clrGP _

/-! ### MapOK -/

/-- A permitted byte lies on a mapped page below 2^48. -/
theorem permVA_info (P : BitVec 64 → Option Page) (a : BitVec 64) (h : PermVA (kmap P) a) :
    a.toNat < 2^48 ∧ ∃ p, P (a >>> 12) = some p := by
  rcases h with ⟨va, acc, al, size, i, ⟨hva, _, hsz, p, hp, _⟩, hi, rfl⟩
  have hi' : va.toNat % 4096 + i < 4096 := by omega
  refine ⟨?_, p, ?_⟩
  · rw [add_toNat va i hva hi']; omega
  · rw [add_page va i hva hi']; exact hp

theorem mapOK (P : BitVec 64 → Option Page)
    (hinj : ∀ n1 n2 p1 p2, P n1 = some p1 → P n2 = some p2 →
      MemM1.LeafFactsG.leafBase p1.leaf = MemM1.LeafFactsG.leafBase p2.leaf → n1 = n2)
    (hnz : ∀ n p, P n = some p → MemM1.LeafFactsG.leafBase p.leaf ≠ 0#56) :
    MapOK (kmap P) where
  contiguous := by
    intro va acc al size i ⟨hva, _, hsz, p, hp, _⟩ hi
    have hi' : va.toNat % 4096 + i < 4096 := by omega
    have hp' : P ((va + BitVec.ofNat 64 i) >>> 12) = some p := by rw [add_page va i hva hi']; exact hp
    rw [pa_toNat P _ p hp', pa_toNat P va p hp, add_toNat va i hva hi']
    omega
  tableDisjoint := fun _ _ h => h
  injective := by
    intro a b ha hb hab
    rcases permVA_info P a ha with ⟨_, pa', hpa⟩
    rcases permVA_info P b hb with ⟨_, pb', hpb⟩
    have he := congrArg BitVec.toNat hab
    rw [pa_toNat P a pa' hpa, pa_toNat P b pb' hpb] at he
    have h1 := MemM1.LeafFactsG.leafBase_aligned pa'.leaf
    have h2 := MemM1.LeafFactsG.leafBase_aligned pb'.leaf
    have hbase : MemM1.LeafFactsG.leafBase pa'.leaf = MemM1.LeafFactsG.leafBase pb'.leaf := by
      apply BitVec.eq_of_toNat_eq; omega
    have hn := congrArg BitVec.toNat (hinj _ _ _ _ hpa hpb hbase)
    rw [ushr12_toNat, ushr12_toNat] at hn
    apply BitVec.eq_of_toNat_eq
    omega
  injectiveFromPermitted := by
    intro a b ha hab
    rcases permVA_info P a ha with ⟨_, pa', hpa⟩
    have ha' := pa_toNat P a pa' hpa
    have h1 := MemM1.LeafFactsG.leafBase_aligned pa'.leaf
    cases hpb : P (b >>> 12) with
    | none =>
      have hb0 : (kmap P).pa b = 0#56 := by simp only [kmap, hpb]
      have he := congrArg BitVec.toNat hab
      rw [hb0, ha'] at he
      exact absurd (BitVec.eq_of_toNat_eq (by simp at he ⊢; omega)) (hnz _ _ hpa)
    | some pb =>
      have he := congrArg BitVec.toNat hab
      rw [pa_toNat P b pb hpb, ha'] at he
      have h2 := MemM1.LeafFactsG.leafBase_aligned pb.leaf
      have hbase : MemM1.LeafFactsG.leafBase pb.leaf = MemM1.LeafFactsG.leafBase pa'.leaf := by
        apply BitVec.eq_of_toNat_eq; omega
      have hn := congrArg BitVec.toNat (hinj _ _ _ _ hpb hpa hbase)
      rw [ushr12_toNat, ushr12_toNat] at hn
      apply BitVec.eq_of_toNat_eq
      omega

/-! ### Sanity: the J3b data page and J3c code page -/

def pg0 : Page := ⟨0x4304000505000443#64, false⟩

def pg1 : Page := ⟨0x0020000606000fc3#64, true⟩

/-- Page 0 ↦ the J3b data leaf, page 1 ↦ the J3c code leaf. -/
def Pex (n : BitVec 64) : Option Page :=
  if n = 0#64 then some pg0 else if n = 1#64 then some pg1 else none

theorem Pex_some (n : BitVec 64) (p : Page) (h : Pex n = some p) :
    (n = 0#64 ∧ p = pg0) ∨ (n = 1#64 ∧ p = pg1) := by
  unfold Pex at h
  split at h
  · cases h; exact Or.inl ⟨by assumption, rfl⟩
  · split at h
    · cases h; exact Or.inr ⟨by assumption, rfl⟩
    · cases h

theorem leafBase_pg0 : MemM1.LeafFactsG.leafBase pg0.leaf = 0x505000000#56 := by decide

theorem leafBase_pg1 : MemM1.LeafFactsG.leafBase pg1.leaf = 0x606000000#56 := by decide

theorem hinj_ex : ∀ n1 n2 p1 p2, Pex n1 = some p1 → Pex n2 = some p2 →
    MemM1.LeafFactsG.leafBase p1.leaf = MemM1.LeafFactsG.leafBase p2.leaf → n1 = n2 := by
  intro n1 n2 p1 p2 h1 h2 hb
  rcases Pex_some n1 p1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases Pex_some n2 p2 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [leafBase_pg0, leafBase_pg1] at hb; exact absurd hb (by decide)
  · rw [leafBase_pg0, leafBase_pg1] at hb; exact absurd hb (by decide)
  · rfl

theorem hnz_ex : ∀ n p, Pex n = some p → MemM1.LeafFactsG.leafBase p.leaf ≠ 0#56 := by
  intro n p h
  rcases Pex_some n p h with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · rw [leafBase_pg0]; decide
  · rw [leafBase_pg1]; decide

theorem mapOK_ex : MapOK (kmap Pex) := mapOK Pex hinj_ex hnz_ex

theorem pa_ex : (kmap Pex).pa 0x1000#64 = 0x606000000#56 := by
  have hpg : Pex (0x1000#64 >>> 12) = some pg1 := by
    unfold Pex
    rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  rw [pa_eq Pex 0x1000#64 pg1 hpg]
  decide

end MemM1.ConsumerV2

