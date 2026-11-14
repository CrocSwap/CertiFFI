import ArmCertWalk.NextEntryTotal
import ArmCertWalk.PathPermissionAnnotation

open Sail ArmFull
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem table_permissions_stable (controls : S1LogicalReference.Controls)
    (prior : S1LogicalReference.TablePermissions) (descriptor : BitVec 64) :
    S1LogicalReference.tablePermissions controls prior descriptor =
      S1LogicalReference.tablePermissions controls prior (S1Descriptor.stable descriptor) := by
  have bit59 := S1StablePath.bit_eq _ descriptor (S1ReferenceKind.stable_idempotent descriptor) 59
    (by decide) (by decide) (by decide)
  have bit60 := S1StablePath.bit_eq _ descriptor (S1ReferenceKind.stable_idempotent descriptor) 60
    (by decide) (by decide) (by decide)
  have bit62 := S1StablePath.bit_eq _ descriptor (S1ReferenceKind.stable_idempotent descriptor) 62
    (by decide) (by decide) (by decide)
  have ap : (S1Descriptor.stable descriptor).extractLsb' 61 2 = descriptor.extractLsb' 61 2 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact S1StablePath.bit_eq _ descriptor (S1ReferenceKind.stable_idempotent descriptor)
      (61 + i) (by omega) (by omega) (by omega)
  simp only [S1LogicalReference.tablePermissions, bit59, bit60, bit62, ap]

theorem table_permissions_view (controls : S1LogicalReference.Controls)
    (prior : S1LogicalReference.TablePermissions) (pie ha hd : Bool)
    (descriptor : BitVec 64) (view : S1DescriptorPIE.View 64)
    (current : S1DescriptorPIE.view pie ha hd descriptor = view) :
    S1LogicalReference.tablePermissions controls prior descriptor =
      S1LogicalReference.tablePermissions controls prior view.stable := by
  have stable : S1Descriptor.stable descriptor = view.stable := congrArg S1DescriptorPIE.View.stable current
  rw [← stable]
  exact table_permissions_stable controls prior descriptor

theorem descriptor_child_base (pie ha hd : Bool) (descriptor : BitVec 64)
    (view : S1DescriptorPIE.View 64) (current : S1DescriptorPIE.view pie ha hd descriptor = view) :
    S1LogicalReference.childBase view = (S1LogicalReference.pageBase descriptor).setWidth 48 := by
  have stable : S1Descriptor.stable descriptor = view.stable := congrArg S1DescriptorPIE.View.stable current
  simp only [S1LogicalReference.childBase, ← stable, S1EntryNextGeometry.stable_extract]
  change ((descriptor.extractLsb' 12 36).setWidth 48 <<< 12) =
    (((descriptor.extractLsb' 12 36).setWidth 56 <<< 12).setWidth 48)
  rw [BitVec.setWidth_shiftLeft_of_le (by decide), BitVec.setWidth_setWidth_of_le _ (by decide)]

theorem descriptor_leaf_kind (pie ha hd : Bool) (descriptor : BitVec 64)
    (view : S1DescriptorPIE.View 64) (current : S1DescriptorPIE.view pie ha hd descriptor = view)
    (level : Nat) (valid : level ≤ 3)
    (kind : S1LogicalReference.descriptorKind level view.stable = .ok .leaf) :
    S1DecodeFacts.classify descriptor (level : Int) = .DescriptorType_Leaf := by
  have interpreted := S1ReferenceKind.view_kind pie ha hd descriptor view current level valid
  cases raw : S1DecodeFacts.classify descriptor (level : Int) <;> simp_all

theorem descriptor_table_kind (pie ha hd : Bool) (descriptor : BitVec 64)
    (view : S1DescriptorPIE.View 64) (current : S1DescriptorPIE.view pie ha hd descriptor = view)
    (level : Nat) (valid : level ≤ 3)
    (kind : S1LogicalReference.descriptorKind level view.stable = .ok .table) :
    S1DecodeFacts.classify descriptor (level : Int) = .DescriptorType_Table := by
  have interpreted := S1ReferenceKind.view_kind pie ha hd descriptor view current level valid
  cases raw : S1DecodeFacts.classify descriptor (level : Int) <;> simp_all

#print axioms table_permissions_view
#print axioms descriptor_child_base
#print axioms descriptor_leaf_kind
#print axioms descriptor_table_kind
end ArmCertWalk
