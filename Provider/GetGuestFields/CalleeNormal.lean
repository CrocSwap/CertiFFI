import GetGuestFields.ControlFacts
import GetGuestFields.View
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 150000
namespace GetGuestFields.CalleeNormal
open S1Normality

theorem read {α : Type} (r : RegisterRef Regs α) : Normal (GetGuestReads.read r) := by
  intro s
  exact ⟨r.get s.regs, s, rfl, rfl, rfl, rfl⟩

theorem occurrence (n : Nat) : Normal (GetGuestReads.occurrence n) := by
  rw [← GetGuestReads.occurrence_function_eq]
  exact occ_normal n

theorem unknown (label : ChoiceLabel) : Normal (S1ParamsUnknown.native label) := by
  intro s
  exact ControlFacts.total_of_frame _ s (ControlFacts.unknown label s)

theorem tcr2 : Normal GetGuestTCR2.native := by
  intro s
  rcases ControlFacts.tcr2_total s with ⟨b, t, hr, hf, _⟩
  exact ⟨b, t, hr, hf⟩

theorem sctlr2 : Normal GetGuestSCTLR2.native := by
  intro s
  exact ControlFacts.total_of_frame _ s (ControlFacts.sctlr2 s)

theorem el2 : Normal S1EL2Enabled.native := by
  simpa only [GetGuestReads.el2_function_eq] using S1EL10PermsCallees.el2_normal

theorem Have128BitDescriptorExt : Normal GetGuestFeatures.Have128BitDescriptorExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveSVE : Normal GetGuestFeatures.HaveSVE.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveTME : Normal GetGuestFeatures.HaveTME.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HavePACExt : Normal GetGuestFeatures.HavePACExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveE0PDExt : Normal GetGuestFeatures.HaveE0PDExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem AArch64_HaveHPDExt : Normal GetGuestFeatures.AArch64_HaveHPDExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveMTE4Ext : Normal GetGuestFeatures.HaveMTE4Ext.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveAIEExt : Normal GetGuestFeatures.HaveAIEExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveRME : Normal GetGuestFeatures.HaveRME.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveSecureEL2Ext : Normal GetGuestFeatures.HaveSecureEL2Ext.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveMTE2Ext : Normal GetGuestFeatures.HaveMTE2Ext.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveTrapLoadStoreMultipleDeviceExt : Normal GetGuestFeatures.HaveTrapLoadStoreMultipleDeviceExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveFeatCMOW : Normal GetGuestFeatures.HaveFeatCMOW.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveAccessFlagUpdateExt : Normal GetGuestFeatures.HaveAccessFlagUpdateExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveDirtyBitModifierExt : Normal GetGuestFeatures.HaveDirtyBitModifierExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem Have52BitIPAAndPASpaceExt : Normal GetGuestFeatures.Have52BitIPAAndPASpaceExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveS1PIExt : Normal GetGuestFeatures.HaveS1PIExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HavePAN3Ext : Normal GetGuestFeatures.HavePAN3Ext.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveTHExt : Normal GetGuestFeatures.HaveTHExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveAccessFlagUpdateForTableExt : Normal GetGuestFeatures.HaveAccessFlagUpdateForTableExt.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem HaveFeatMEC : Normal GetGuestFeatures.HaveFeatMEC.native := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem TTBR0 : Normal GetGuestVirtualization.TTBR0.native := by
  intro s
  apply ControlFacts.total_of_frame _ s
  observe_simp [ControlFacts.FrameResult, Frame, GetGuestVirtualization.TTBR0.native]

theorem TTBR1 : Normal GetGuestVirtualization.TTBR1.native := by
  intro s
  apply ControlFacts.total_of_frame _ s
  observe_simp [ControlFacts.FrameResult, Frame, GetGuestVirtualization.TTBR1.native]

theorem Constraint : Normal GetGuestVirtualization.Constraint.native := by
  intro s
  apply ControlFacts.total_of_frame _ s
  observe_simp [ControlFacts.FrameResult, Frame, GetGuestVirtualization.Constraint.native]

#print axioms tcr2
#print axioms Constraint

theorem TG0 (tg : BitVec 2) : Normal (GetGuestVirtualization.TG0.native tg) := by
  intro s
  apply ControlFacts.total_of_frame _ s
  observe_simp [ControlFacts.FrameResult, Frame, GetGuestVirtualization.TG0.native]
#print axioms TG0

theorem TG1 (tg : BitVec 2) : Normal (GetGuestVirtualization.TG1.native tg) := by
  intro s
  apply ControlFacts.total_of_frame _ s
  observe_simp [ControlFacts.FrameResult, Frame, GetGuestVirtualization.TG1.native]
#print axioms TG1

end GetGuestFields.CalleeNormal
