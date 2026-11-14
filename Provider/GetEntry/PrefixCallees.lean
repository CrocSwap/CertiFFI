import GetEntry.Tail
import Walk.S1EntryCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1EntryCalleesExtra
open S1Normality

drive_spec tlbrecord_native, tlbrecord_eq : fun (label : ChoiceLabel) (s : State) =>
  undefined_TLBRecord label () s
attribute [step_summary] tlbrecord_eq

drive_spec normalnc_native, normalnc_eq : fun (s : State) => NormalNCMemAttr () s
attribute [step_summary] normalnc_eq

theorem bool_normal (label : ChoiceLabel) : Normal (undefined_bool_at label ()) := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem descriptor_type_normal (label : ChoiceLabel) :
    Normal (undefined_DescriptorType label ()) := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩

theorem context_normal (label : ChoiceLabel) : Normal (undefined_TLBContext label ()) := by
  intro s
  rw [UndefSummaries.TLBContext_eq]
  delta UndefSummaries.TLBContext_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem record_normal (label : ChoiceLabel) : Normal (undefined_TLBRecord label ()) := by
  intro s
  rw [tlbrecord_eq]
  delta tlbrecord_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem normalnc_normal : Normal (NormalNCMemAttr ()) := by
  intro s
  rw [normalnc_eq]
  delta normalnc_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩
#print axioms record_normal
#print axioms normalnc_normal
#print axioms descriptor_type_normal
end S1EntryCalleesExtra
