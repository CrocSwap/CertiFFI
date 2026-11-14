import ArmCertTranslateModel.StructuralBridge
import Walk.S1LogicalDescriptor

open Sail ArmFull ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- Derive static field preservation from memory's actual authorized word
    relation. These are existing canonical pure interpretation functions. -/
theorem allowed_table_permissions (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after)
    (controls : S1LogicalReference.Controls) (prior : S1LogicalReference.TablePermissions) :
    S1LogicalReference.tablePermissions controls prior after =
      S1LogicalReference.tablePermissions controls prior before := by
  have h59 := allowedUpdate_other h 59 (by decide) (by decide)
  have h60 := allowedUpdate_other h 60 (by decide) (by decide)
  have h62 := allowedUpdate_other h 62 (by decide) (by decide)
  have hs := (allowed_delta params role before after h).slice_eq 61 2 (by decide) (by omega) (by omega)
  simp only [S1LogicalReference.tablePermissions, h59, h60, h62, hs]

theorem allowed_attribute_index (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after) (aie : Bool) :
    S1LogicalReference.attributeIndex aie after = S1LogicalReference.attributeIndex aie before := by
  have hb := allowedUpdate_other h 59 (by decide) (by decide)
  have hs := (allowed_delta params role before after h).slice_eq 2 3 (by decide) (by omega) (by omega)
  simp only [S1LogicalReference.attributeIndex, hb, hs]

theorem allowed_selected_byte (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after)
    (controls : S1LogicalReference.Controls) :
    S1LogicalReference.mairByte controls (S1LogicalReference.attributeIndex controls.aie after) =
      S1LogicalReference.mairByte controls (S1LogicalReference.attributeIndex controls.aie before) := by
  rw [allowed_attribute_index params role before after h]

theorem allowed_page_base (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after) :
    S1LogicalReference.pageBase after = S1LogicalReference.pageBase before := by
  have hs := (allowed_delta params role before after h).address_bits
  simp only [S1LogicalReference.pageBase, hs]

theorem allowed_leaf_base (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after) (level : Nat) :
    S1LogicalReference.leafBase level after = S1LogicalReference.leafBase level before := by
  simp only [S1LogicalReference.leafBase, allowed_page_base params role before after h]

theorem allowed_contiguous (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after)
    (controls : S1LogicalReference.Controls) (inheritedDisCH : Bool) :
    S1LogicalReference.contiguous controls inheritedDisCH after =
      S1LogicalReference.contiguous controls inheritedDisCH before := by
  have hb := allowedUpdate_other h 52 (by decide) (by decide)
  simp only [S1LogicalReference.contiguous, hb]

theorem allowed_output_address (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after)
    (controls : S1LogicalReference.Controls) (inheritedDisCH : Bool)
    (va : BitVec 64) (level : Nat) (space : PASpace) :
    S1LogicalReference.outputAddress va level
      {paspace := space, address := S1LogicalReference.leafBase level after}
      (S1LogicalReference.contiguous controls inheritedDisCH after) =
    S1LogicalReference.outputAddress va level
      {paspace := space, address := S1LogicalReference.leafBase level before}
      (S1LogicalReference.contiguous controls inheritedDisCH before) := by
  rw [allowed_leaf_base params role before after h,
    allowed_contiguous params role before after h]

/-- PIE selectors and selected PIR/PIRE0 fields stay equal. The raw notDirty
    field is intentionally excluded: it can change under authorized dirtying. -/
theorem allowed_permission_index (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after) :
    S1LogicalReference.permissionIndex after = S1LogicalReference.permissionIndex before := by
  have h51 := allowedUpdate_other h 51 (by decide) (by decide)
  have h6 := allowedUpdate_other h 6 (by decide) (by decide)
  have hs := (allowed_delta params role before after h).slice_eq 53 2 (by decide) (by omega) (by omega)
  simp only [S1LogicalReference.permissionIndex, h51, h6, hs]

theorem allowed_pie_permissions (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after)
    (controls : S1LogicalReference.Controls) :
    ((S1LogicalReference.indirectPermissions controls after).privileged,
      (S1LogicalReference.indirectPermissions controls after).unprivileged) =
    ((S1LogicalReference.indirectPermissions controls before).privileged,
      (S1LogicalReference.indirectPermissions controls before).unprivileged) := by
  simp only [S1LogicalReference.indirectPermissions, allowed_permission_index params role before after h]

private theorem ap_mask_congr (nv : Bool) (x y : BitVec 64) (h6 : y.getLsbD 6 = x.getLsbD 6) :
    ((if nv then (BitVec.ofBool (y.getLsbD 7)).setWidth 2 <<< 1 else y.extractLsb' 6 2) &&& 1#2) =
    ((if nv then (BitVec.ofBool (x.getLsbD 7)).setWidth 2 <<< 1 else x.extractLsb' 6 2) &&& 1#2) := by
  have h6' : y[6] = x[6] := by simpa using h6
  cases nv <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  all_goals
    have hc : i = 0 ∨ i = 1 := by omega
    rcases hc with rfl | rfl <;> simp [h6']

private theorem source_setAF_classic (controls : S1LogicalReference.Controls) (d : BitVec 64) :
    S1LogicalReference.classicPermissions controls (S1Descriptor.setAF d) =
      S1LogicalReference.classicPermissions controls d := by
  have h6 : (S1Descriptor.setAF d).extractLsb' 6 2 = d.extractLsb' 6 2 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact S1Descriptor.setAF_other d (6 + i) (by omega)
  have h7 := S1Descriptor.setAF_other d 7 (by decide)
  have h51 := S1Descriptor.setAF_other d 51 (by decide)
  have h53 := S1Descriptor.setAF_other d 53 (by decide)
  have h54 := S1Descriptor.setAF_other d 54 (by decide)
  simp at h7 h51 h53 h54
  cases hn : S1LogicalReference.nv1Mode controls <;>
    simp [S1LogicalReference.classicPermissions, hn, h6, h7, h51, h53, h54]

private theorem source_setDirty_classic (controls : S1LogicalReference.Controls) (d : BitVec 64)
    (hHA : controls.ha = true) (hHD : controls.hd = true) (hDBM : d.getLsbD 51 = true) :
    S1LogicalReference.classicPermissions controls (S1Descriptor.setDirty d) =
      S1LogicalReference.classicPermissions controls d := by
  have h51 := S1Descriptor.setDirty_other d 51 (by decide)
  have h53 := S1Descriptor.setDirty_other d 53 (by decide)
  have h54 := S1Descriptor.setDirty_other d 54 (by decide)
  have hm := ap_mask_congr (S1LogicalReference.nv1Mode controls) d (S1Descriptor.setDirty d)
    (S1Descriptor.setDirty_other d 6 (by decide))
  simp at h51 h53 h54 hDBM
  cases hn : S1LogicalReference.nv1Mode controls <;>
    simp [S1LogicalReference.classicPermissions, hn, hHA, hHD, hDBM, h51, h53, h54] at hm ⊢ <;>
    exact hm

/-- Active classic permission fields stay equal under an authorized update.
    HA/HD consistency is current control data, and PIE=0 selects this active
    branch; this theorem makes no feature-absence or zero-table-permission pin. -/
theorem allowed_classic_permissions (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after)
    (controls : S1LogicalReference.Controls) (hPie : params.pie = 0#1)
    (hHA : controls.ha = (params.ha == 1#1)) (hHD : controls.hd = (params.hd == 1#1)) :
    S1LogicalReference.classicPermissions controls after =
      S1LogicalReference.classicPermissions controls before := by
  obtain ⟨af, dirty, rfl, _, hd⟩ := h
  cases af <;> cases dirty
  · rfl
  · obtain ⟨_, hpa, hpd, hdbm⟩ := hd rfl
    exact source_setDirty_classic controls before
      (by rw [hHA, hpa]; rfl) (by rw [hHD, hpd]; rfl) (hdbm hPie)
  · exact source_setAF_classic controls before
  · obtain ⟨_, hpa, hpd, hdbm⟩ := hd rfl
    have hdbm' : (S1Descriptor.setAF before).getLsbD 51 = true := by
      rw [S1Descriptor.setAF_other before 51 (by decide)]
      exact hdbm hPie
    exact (source_setDirty_classic controls (S1Descriptor.setAF before)
      (by rw [hHA, hpa]; rfl) (by rw [hHD, hpd]; rfl) hdbm').trans
        (source_setAF_classic controls before)

#print axioms allowed_table_permissions
#print axioms allowed_selected_byte
#print axioms allowed_output_address
#print axioms allowed_pie_permissions
#print axioms allowed_classic_permissions
end ArmCert.Translate.Model
