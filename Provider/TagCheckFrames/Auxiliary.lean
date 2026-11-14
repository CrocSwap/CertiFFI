import TagCheckFrames.Translation
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open TagCheckFrames
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace TagCheckFrames
theorem bits_preserves (width : Nat) (label : ChoiceLabel) :
    Preserves (undefined_bitvector_at label width) := by oracle_frame
theorem bool_preserves (label : ChoiceLabel) :
    Preserves (undefined_bool_at label ()) := by oracle_frame
theorem enc_preserves (label : ChoiceLabel) :
    Preserves (undefined___InstrEnc label ()) := by oracle_frame
theorem create_ifetch_preserves : Preserves (CreateAccDescIFetch ()) := by oracle_frame
theorem css_preserves : Preserves (CheckSoftwareStep ()) := by oracle_frame
theorem cis_preserves : Preserves (AArch64_CheckIllegalState ()) := by oracle_frame
theorem constraint_preserves (label : ChoiceLabel) :
    Preserves (undefined_Constraint label ()) := by oracle_frame
theorem bigEndian_preserves (kind : AccessType) :
    Preserves (BigEndian kind) := by oracle_frame
theorem trace_of_normal {α : Type} (p : SailM α) (normal : S1Normality.Normal p)
    (preserves : Preserves p) (s : State) :
    ∃ a t, p s = .ok a t ∧ NativeMteTagCheck.StatusTrace.TraceFrame s t := by
  obtain ⟨a,t,run,frame⟩ := normal s
  exact ⟨a,t,run,frame.1,frame.2.1,frame.2.2,preserves s a t run⟩

#print axioms create_ifetch_preserves
#print axioms css_preserves
#print axioms cis_preserves
#print axioms constraint_preserves
#print axioms bigEndian_preserves
#print axioms trace_of_normal
end TagCheckFrames
