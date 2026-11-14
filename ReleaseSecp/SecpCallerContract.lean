import TranslateSpan.SecpDefaultEntry

open Sail ArmFull ArmCert.Translate.Model ArmBridge.Draft
open TranslateSpan.SecpRawDeployment
set_option autoImplicit false
set_option maxHeartbeats 100000

namespace ReleaseProfile.SecpCaller

-- predicate c8ccb5cc; addresses are the decoded VAs selected by the
-- routine's actual region interface. No alignment or non-alias premise.
def Contract (objects : List (BitVec 64 × Nat)) : Prop :=
  ∀ obj ∈ objects, obj.1.toNat + obj.2 ≤ 2 ^ 64 ∧
    ∀ i : Nat, i < obj.2 → (obj.1 + BitVec.ofNat 64 i).getLsbD 55 = false

def objects (plan : Plan) (entry : NativeState) : List (BitVec 64 × Nat) :=
  plan.buffers.map fun (region,length) => (regionVA entry region 0,length)

theorem lower_byte_of_end (base : BitVec 64) (length i : Nat)
    (endBound : base.toNat + length ≤ 2 ^ 55) (inside : i < length) :
    (base + BitVec.ofNat 64 i).getLsbD 55 = false := by
  have iBound : i < 2 ^ 64 := by omega
  have sumBound : base.toNat + i < 2 ^ 64 := by omega
  have small : (base + BitVec.ofNat 64 i).toNat < 2 ^ 55 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt iBound,
      Nat.mod_eq_of_lt sumBound]
    omega
  exact Nat.testBit_lt_two_pow small

theorem contract_of_ends (objects : List (BitVec 64 × Nat))
    (bounds : ∀ obj ∈ objects, obj.1.toNat + obj.2 ≤ 2 ^ 55) : Contract objects := by
  intro obj member
  have bound := bounds obj member
  exact ⟨by omega, fun i inside => lower_byte_of_end obj.1 obj.2 i bound inside⟩

theorem of_checkBuffers (plan : Plan) (raw : TranslateSpan.CheckedTopology.Raw)
    (entry : NativeState) (checked : checkBuffers plan raw entry = true) :
    Contract (objects plan entry) := by
  apply contract_of_ends
  intro obj member
  obtain ⟨⟨region,length⟩,inside,rfl⟩ := List.mem_map.mp member
  have bounds := bounds_of_check checked inside
  have power : 2 ^ min 55 raw.layout.inputBits ≤ 2 ^ 55 :=
    Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)
  let z : Int := (entryGPR entry region.pin).toNat + region.off
  have lower : 0 ≤ z := bounds.1
  have upper : z < (2 ^ 64 : Nat) := by omega
  have repr : regionVA entry region 0 = BitVec.ofInt 64 z := by
    simp only [regionVA, Int.ofNat_zero, Int.add_zero, BitVec.addInt, z,
      BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have address : (regionVA entry region 0).toNat = z.toNat := by
    rw [repr, BitVec.toNat_ofInt, Int.emod_eq_of_lt lower upper]
  change (regionVA entry region 0).toNat + length ≤ 2 ^ 55
  rw [address]
  omega

#print axioms lower_byte_of_end
#print axioms contract_of_ends
#print axioms of_checkBuffers
end ReleaseProfile.SecpCaller
