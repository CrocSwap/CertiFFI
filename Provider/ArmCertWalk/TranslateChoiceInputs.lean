import ArmCertWalk.TranslateCacheAttrs
import Pilot.ObservationSimp

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

drive_spec undefined_attrs_native, undefined_attrs_eq : fun (label : ChoiceLabel) (state : State) =>
  undefined_MemoryAttributes label () state

drive_spec undefined_params_native, undefined_params_eq : fun (label : ChoiceLabel) (state : State) =>
  undefined_S1TTWParams label () state

drive_spec undefined_tlbline_native, undefined_tlbline_eq : fun (label : ChoiceLabel) (state : State) =>
  undefined_TLBLine label () state

theorem undefined_attrs_normal (label : ChoiceLabel) : S1Normality.Normal (undefined_MemoryAttributes label ()) := by
  intro state
  rw [undefined_attrs_eq]
  delta undefined_attrs_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem undefined_params_normal (label : ChoiceLabel) : S1Normality.Normal (undefined_S1TTWParams label ()) := by
  intro state
  rw [undefined_params_eq]
  delta undefined_params_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem undefined_tlbline_normal (label : ChoiceLabel) : S1Normality.Normal (undefined_TLBLine label ()) := by
  intro state
  rw [undefined_tlbline_eq]
  delta undefined_tlbline_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem undefined_access_normal (label : ChoiceLabel) : S1Normality.Normal (undefined_AccessDescriptor label ()) := by
  intro state
  rw [UndefSummaries.AccessDescriptor_eq]
  delta UndefSummaries.AccessDescriptor_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

#print axioms undefined_attrs_eq
#print axioms undefined_params_eq
#print axioms undefined_tlbline_eq
#print axioms undefined_attrs_normal
#print axioms undefined_params_normal
#print axioms undefined_tlbline_normal
#print axioms undefined_access_normal
end ArmCertWalk
