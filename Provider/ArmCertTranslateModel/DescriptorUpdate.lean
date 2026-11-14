import ArmCertTranslate.DescriptorDelta
import Pilot.S1DescriptorPIE

open Sail
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- The source descriptor operation sets AF without changing other bits. -/
theorem setAF_bit (d : BitVec 64) : (S1Descriptor.setAF d).getLsbD 10 = true := by
  simp [S1Descriptor.setAF, Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.zeroExtend]

theorem delta_setAF (d : BitVec 64) (hha : ha = true) :
    DescriptorDelta ha hd pie d (S1Descriptor.setAF d) := by
  refine ⟨fun i _ _ h10 => S1Descriptor.setAF_other d i h10,
    fun _ => setAF_bit d, fun _ => hha, ?_, ?_⟩
  · intro h
    rw [S1Descriptor.setAF_other d 7 (by decide)] at h
    exact h
  · intro h
    exact False.elim (h (S1Descriptor.setAF_other d 7 (by decide)).symm)

theorem delta_setDirty (d : BitVec 64)
    (hdirty : ha = true ∧ hd = true ∧ (pie = false → d.getLsbD 51 = true)) :
    DescriptorDelta ha hd pie d (S1Descriptor.setDirty d) := by
  refine ⟨fun i _ h7 _ => S1Descriptor.setDirty_other d i h7, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [S1Descriptor.setDirty_other d 10 (by decide)]
    exact h
  · intro h
    exact False.elim (h (S1Descriptor.setDirty_other d 10 (by decide)).symm)
  · intro h
    rw [S1Descriptor.setDirty_bit] at h
    cases h
  · intro _
    refine ⟨hdirty.1, hdirty.2.1, ?_⟩
    cases hp : pie
    · exact Or.inr (hdirty.2.2 hp)
    · exact Or.inl rfl

/-- Actual source hardwareUpdate satisfies the exact bit restriction. The
    hardware-authorization guards are structural inputs, not source-success
    assumptions; its caller must derive them from the effective walk controls. -/
theorem hardware_delta (ha hd pie af dirty : Bool) (d : BitVec 64)
    (haf : af = true → ha = true)
    (hdirty : dirty = true → ha = true ∧ hd = true ∧
      (pie = false → d.getLsbD 51 = true)) :
    DescriptorDelta ha hd pie d (S1Descriptor.hardwareUpdate af dirty d) := by
  cases af <;> cases dirty
  · exact DescriptorDelta.refl _ _ _ _
  · exact delta_setDirty d (hdirty rfl)
  · exact delta_setAF d (haf rfl)
  · apply (delta_setAF d (haf rfl)).trans
    apply delta_setDirty
    obtain ⟨hha, hhd, hdbm⟩ := hdirty rfl
    refine ⟨hha, hhd, ?_⟩
    intro hp
    rw [S1Descriptor.setAF_other d 51 (by decide)]
    exact hdbm hp

#print axioms hardware_delta
end ArmCert.Translate.Model
