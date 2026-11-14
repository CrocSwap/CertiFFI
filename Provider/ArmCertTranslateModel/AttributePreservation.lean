import ArmCertWalk.AttributeInputs
import ArmCertTranslateModel.TopologyImage

open Sail ArmFull ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

theorem allowed_selected_attribute (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after) (config : AttributeConfig) :
    selectedAttribute config after = selectedAttribute config before := by
  have hs := (allowed_delta params role before after h).slice_eq 2 3 (by decide) (by omega) (by omega)
  have hi : descriptorIndex after = descriptorIndex before := by
    apply Fin.ext
    change (after.extractLsb' 2 3).toNat = (before.extractLsb' 2 3).toNat
    rw [hs]
  simp only [selectedAttribute, hi]

theorem allowed_attribute_admissible (params : S1TTWParams) (role : DescriptorRole)
    (before after : BitVec 64) (h : AllowedUpdate params role before after) (config : AttributeConfig) :
    AttributeAdmissible config (selectedAttribute config after) ↔
      AttributeAdmissible config (selectedAttribute config before) := by
  rw [allowed_selected_attribute params role before after h]

/-- An inactive MAIR2 value is free in the ordinary AIE0 selection domain. -/
theorem selected_attribute_inactive_mair2 (config : AttributeConfig) (mair2 : BitVec 64) (d : BitVec 64) :
    selectedAttribute {config with mair2 := mair2} d = selectedAttribute config d := rfl

/-- Current-byte reserved-encoding validity at each actually used leaf. This
    is a pure check, not an assumed decoder/source-call success property. -/
def AttributeImage (observe : RoleObservation) (config : AttributeConfig) (mem : Mem) : Prop :=
  ∀ slot view, observe slot true view → ∀ d, S1ByteMemory.DescAt mem slot d →
    AttributeAdmissible config (selectedAttribute config d)

def checkAttributeImage (rows : List ImageRow) (config : AttributeConfig) : Bool :=
  rows.all (fun row => !row.leaf || decide (reservedAttribute config.xs config.mte2 (selectedAttribute config row.raw) = false))

theorem check_attribute_image_sound (rows : List ImageRow) (config : AttributeConfig)
    (params : S1TTWParams) (mem : Mem)
    (hbytes : checkImage rows (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) mem = true)
    (hattr : checkAttributeImage rows config = true) : AttributeImage (rowsObserve rows) config mem := by
  intro slot view ⟨row, hr, hs, hl, hv⟩ d hd
  have hc := (List.all_eq_true.mp hattr) row hr
  have hb := (List.all_eq_true.mp hbytes) row hr
  obtain ⟨hraw, _, _, _⟩ := row.check_sound _ _ _ _ hb
  have heq : d = row.raw := S1ByteMemory.descriptor_unique mem row.slot d row.raw (by simpa [hs] using hd) hraw
  rw [heq]
  have hleaf : row.leaf = true := hl.symm
  simpa only [AttributeAdmissible, hleaf, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hc

theorem AttributeImage.hardware_store (h : AttributeImage observe config mem)
    (params : S1TTWParams) (role : DescriptorRole) (slot : Nat) (before after : BitVec 64)
    (hu : AllowedUpdate params role before after) (hAlign : slot % 8 = 0)
    (hSlots : ImageAligned observe) (hb : S1ByteMemory.DescAt mem slot before) :
    AttributeImage observe config (S1ByteMemory.store mem slot after) := by
  intro b view ho d hd
  by_cases heq : slot = b
  · subst b
    have hnew : d = after := S1ByteMemory.descriptor_unique _ slot d after hd
      (S1ByteMemory.stored_descriptor _ _ _)
    rw [hnew]
    exact (allowed_attribute_admissible params role before after hu config).mpr (h slot view ho before hb)
  · have hpre := (S1ByteMemory.other_descriptor_iff mem slot b after d hAlign (hSlots b true view ho) heq).mp hd
    exact h b view ho d hpre

theorem AttributeImage.program_write (h : AttributeImage observe config mem)
    (f : Footprint) (hw : f.width = 8) (hc : ImageCovers observe f)
    (hf : WritesOnly writes (fun a => mem[a]?) (fun a => mem'[a]?))
    (hs : Separated f.byte writes) : AttributeImage observe config mem' := by
  intro slot view ho d hd
  apply h slot view ho d
  intro i hi
  have hi' : i < f.width := by simpa only [hw] using hi
  have heq := table_unchanged hf hs _ (f.covers slot (hc slot true view ho) ⟨i, hi'⟩)
  exact heq.symm.trans (hd i hi)

/-- Ordinary-slot admission does not pin an unused MAIR2 value across
    source parameter getters or their differing inactive oracle fields. -/
theorem attribute_image_inactive_mair2 (observe : RoleObservation) (config : AttributeConfig)
    (mair2 : BitVec 64) (mem : Mem) :
    AttributeImage observe {config with mair2 := mair2} mem ↔ AttributeImage observe config mem := Iff.rfl

#print axioms allowed_selected_attribute
#print axioms check_attribute_image_sound
#print axioms AttributeImage.hardware_store
#print axioms AttributeImage.program_write
end ArmCert.Translate.Model
