import Walk.S1LogicalDescriptor
import Walk.S1StablePath
open Sail ArmFull
set_option maxHeartbeats 150000
namespace S1ReferenceKind

def kind : S1LogicalReference.EntryKind → DescriptorType
  | .invalid => .DescriptorType_Invalid
  | .table => .DescriptorType_Table
  | .leaf => .DescriptorType_Leaf

theorem bit_bool (d : BitVec 64) (i : Nat) (hi : i < 64) :
    S1DecodeFacts.bit d i = BitVec.ofBool (d.getLsbD i) := by
  have hb : d[i]! = d.getLsbD i := by
    simp [getElem!_def, ← BitVec.getLsbD_eq_getElem, hi]
  unfold S1DecodeFacts.bit Sail.BitVec.access
  rw [hb]
  cases d.getLsbD i <;> rfl

theorem classify (d : BitVec 64) (level : Nat) (hl : level ≤ 3) :
    S1LogicalReference.descriptorKind level d =
      .ok (match S1DecodeFacts.classify d (level : Int) with
        | .DescriptorType_Table => .table
        | .DescriptorType_Leaf => .leaf
        | _ => .invalid) := by
  have hc : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    cases h0 : d.getLsbD 0 <;> cases h1 : d.getLsbD 1 <;>
    simp only [S1LogicalReference.descriptorKind, S1DecodeFacts.classify,
      bit_bool d 0 (by decide), bit_bool d 1 (by decide), h0, h1] <;> simp

#print axioms bit_bool
#print axioms classify
end S1ReferenceKind
namespace S1ReferenceKind

theorem stable_idempotent (d : BitVec 64) :
    S1Descriptor.stable (S1Descriptor.stable d) = S1Descriptor.stable d := by
  simp only [S1Descriptor.stable, BitVec.and_assoc, BitVec.and_self]

theorem classify_stable (d : BitVec 64) (level : Int) :
    S1DecodeFacts.classify (S1Descriptor.stable d) level = S1DecodeFacts.classify d level :=
  S1StablePath.classify_eq _ _ _ (stable_idempotent d)

theorem view_kind (pie ha hd : Bool) (d : BitVec 64) (v : S1DescriptorPIE.View 64)
    (hview : S1DescriptorPIE.view pie ha hd d = v) (level : Nat) (hl : level ≤ 3) :
    S1LogicalReference.descriptorKind level v.stable =
      .ok (match S1DecodeFacts.classify d (level : Int) with
        | .DescriptorType_Table => .table
        | .DescriptorType_Leaf => .leaf
        | _ => .invalid) := by
  have hv : S1Descriptor.stable d = v.stable := congrArg S1DescriptorPIE.View.stable hview
  rw [← hv, classify _ level hl, classify_stable]
#print axioms view_kind
end S1ReferenceKind
