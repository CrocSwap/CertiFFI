import TranslateMem.RegionsInj
import Walk.S1LogicalDescriptor

/-! PageLinear from the stage-1 leaf arithmetic (, route 1). The deployment `mapping` is a free
function, tied to the walk only at translated VAs (`WalkResultAdmitted`: mapping va = outputAddress va level base
contig). `LeafTranslated` states that the deployment mapping IS that leaf translation, page by page: each 4 KiB VA
page has (at most) one leaf (level, output base, contiguous) and every VA maps to its leaf's output address. Then
`PageLinear` follows from `outputAddress` (PA = base rounded to 2^bits + va mod 2^bits, bits = leafBits level
(+4 when contiguous) ≥ 12), for every granule and block size. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateMem
open ArmFull

/-- A leaf: level, output base, contiguous bit. -/
abbrev Leaf := Nat × FullAddress × Bool

def leafSize (l : Leaf) : Nat := S1LogicalReference.leafBits l.1 + if l.2.2 then 4 else 0

def leafPA (va : BitVec 64) (l : Leaf) : Nat := (S1LogicalReference.outputAddress va l.1 l.2.1 l.2.2).address.toNat

/-- DEPLOYMENT: the mapping is the stage-1 leaf translation of each VA page (none = unmapped page). -/
def LeafTranslated (mapping : BitVec 64 → Option Nat) (leafOf : Nat → Option Leaf) : Prop :=
  ∀ va, mapping va = (leafOf (pageOf va)).map (leafPA va)

theorem leafSize_ge (l : Leaf) : 12 ≤ leafSize l := by
  unfold leafSize S1LogicalReference.leafBits; split <;> omega

theorem leafSize_le (l : Leaf) : leafSize l ≤ 43 := by
  unfold leafSize S1LogicalReference.leafBits; split <;> omega

/-- The leaf output address, unwrapped: the 2^bits-aligned block of the base plus the in-block offset. -/
theorem leafPA_eq (va : BitVec 64) (l : Leaf) :
    leafPA va l = l.2.1.address.toNat / 2 ^ leafSize l * 2 ^ leafSize l + va.toNat % 2 ^ leafSize l := by
  unfold leafPA S1LogicalReference.outputAddress
  simp only [BitVec.toNat_ofNat]
  have hs := leafSize_le l
  have hb : l.2.1.address.toNat < 2 ^ 56 := l.2.1.address.isLt
  have pos : 0 < 2 ^ leafSize l := Nat.two_pow_pos _
  -- 2^56 is a multiple of 2^bits, so the aligned block ends at or below 2^56
  obtain ⟨k, hk⟩ : 2 ^ leafSize l ∣ 2 ^ 56 := Nat.pow_dvd_pow 2 (by omega)
  have blk : l.2.1.address.toNat / 2 ^ leafSize l < k := by
    rw [Nat.div_lt_iff_lt_mul pos, Nat.mul_comm, ← hk]; exact hb
  have lt : l.2.1.address.toNat / 2 ^ leafSize l * 2 ^ leafSize l + va.toNat % 2 ^ leafSize l < 2 ^ 56 := by
    have hm := Nat.mod_lt va.toNat pos
    have : (l.2.1.address.toNat / 2 ^ leafSize l + 1) * 2 ^ leafSize l ≤ k * 2 ^ leafSize l :=
      Nat.mul_le_mul_right _ blk
    rw [Nat.succ_mul, Nat.mul_comm k, ← hk] at this
    omega
  exact Nat.mod_eq_of_lt (by unfold leafSize at lt; exact lt)

/-- Splitting the in-block offset at 4 KiB. -/
theorem mod_split (a s : Nat) (hs : 12 ≤ s) : a % 2 ^ s = a % 4096 + 4096 * (a / 4096 % 2 ^ (s - 12)) := by
  have e : 2 ^ s = 4096 * 2 ^ (s - 12) := by
    rw [show (4096 : Nat) = 2 ^ 12 from rfl, ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mod_mul]

/-- **PageLinear** from the leaf translation. -/
theorem pageLinear_of_leaf (mapping : BitVec 64 → Option Nat) (leafOf : Nat → Option Leaf)
    (h : LeafTranslated mapping leafOf) :
    PageLinear mapping (fun pg => (leafOf pg).map fun l => leafPA (BitVec.ofNat 64 (pg * 4096)) l / 4096) := by
  intro va
  rw [h va, Option.map_map]
  cases hl : leafOf (pageOf va) with
  | none => rfl
  | some l =>
    simp only [Option.map_some, Function.comp]
    congr 1
    have hs := leafSize_ge l
    have hva := va.isLt
    have hpg : (BitVec.ofNat 64 (pageOf va * 4096)).toNat = pageOf va * 4096 := by
      rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; unfold pageOf; omega
    rw [leafPA_eq, leafPA_eq, hpg, mod_split va.toNat _ hs, mod_split (pageOf va * 4096) _ hs]
    have m0 : pageOf va * 4096 % 4096 = 0 := Nat.mul_mod_left _ _
    have d0 : pageOf va * 4096 / 4096 = pageOf va := Nat.mul_div_cancel _ (by decide)
    rw [m0, d0]
    unfold pageOf
    -- the aligned block base is a multiple of 4096
    obtain ⟨K, hK⟩ : ∃ K, 2 ^ leafSize l = 4096 * K :=
      ⟨2 ^ (leafSize l - 12), by rw [show (4096 : Nat) = 2 ^ 12 from rfl, ← Nat.pow_add]; congr 1; omega⟩
    have hB : l.2.1.address.toNat / 2 ^ leafSize l * 2 ^ leafSize l =
        4096 * (l.2.1.address.toNat / 2 ^ leafSize l * K) := by rw [hK]; ac_rfl
    rw [hB]
    have hr := Nat.mod_lt va.toNat (by decide : 0 < 4096)
    have e1 : (4096 * (l.2.1.address.toNat / 2 ^ leafSize l * K) + (0 + 4096 * (va.toNat / 4096 % 2 ^ (leafSize l - 12)))) / 4096 =
        l.2.1.address.toNat / 2 ^ leafSize l * K + va.toNat / 4096 % 2 ^ (leafSize l - 12) := by omega
    rw [e1]; omega

/-- RegionsInjective with the mapping given as a leaf translation. -/
theorem regionsInjective_of_leaf (p : ArmCert.Translate.Model.HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat)
    (leafOf : Nat → Option Leaf) (hd : RegionsDisjoint p) (lt : LeafTranslated mapping leafOf)
    (nd : NoDoubleMapOn p (fun pg => (leafOf pg).map fun l => leafPA (BitVec.ofNat 64 (pg * 4096)) l / 4096)) :
    ArmCertValue.HeapV2Mem.RegionsInjective p mapping :=
  regionsInjective_of_pages p mapping _ hd (pageLinear_of_leaf mapping leafOf lt) nd

/-- DataBytesLinear with the mapping given as a leaf translation. -/
theorem dataBytesLinear_of_leaf (p : ArmCert.Translate.Model.HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat)
    (leafOf : Nat → Option Leaf) (lt : LeafTranslated mapping leafOf) (hd : RegionsDisjoint p)
    (aligned : p.sp % 16 = 0 ∧ p.x0 % 16 = 0 ∧ p.x1 % 16 = 0) :
    ArmCertValue.HeapV2Mem.DataBytesLinear p mapping :=
  dataBytesLinear_of_pages p mapping _ (pageLinear_of_leaf mapping leafOf lt) hd aligned

#print axioms pageLinear_of_leaf
#print axioms regionsInjective_of_leaf
#print axioms dataBytesLinear_of_leaf
end TranslateMem
