import Pilot.UndefSummaries
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1Unknowns
abbrev State := SequentialState Regs oracleChoiceSource
drive_spec walk_native, walk_eq : fun (label : ChoiceLabel) (s : State) =>
  undefined_TTWState label () s
attribute [step_summary] walk_eq
drive_spec address_native, address_eq : fun (s : State) => __UNKNOWN_AddressDescriptor () s
drive_spec walkstate_native, walkstate_eq : fun (s : State) => __UNKNOWN_TTWState () s
drive_spec bits_native, bits_eq : fun (s : State) => __UNKNOWN_bits 64 s

theorem address_total (s : State) :
    ∃ (a : AddressDescriptor) (t : State), __UNKNOWN_AddressDescriptor () s = .ok a t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rw [address_eq]
  delta address_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩
theorem walkstate_total (s : State) :
    ∃ (w : TTWState) (t : State), __UNKNOWN_TTWState () s = .ok w t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rw [walkstate_eq]
  delta walkstate_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩
theorem bits_total (s : State) :
    ∃ (d : BitVec 64) (t : State), __UNKNOWN_bits 64 s = .ok d t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rw [bits_eq]
  delta bits_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩
#print axioms address_total
#print axioms walkstate_total
#print axioms bits_total

theorem undefined_address_total (label : ChoiceLabel) (s : State) :
    ∃ (a : AddressDescriptor) (t : State), undefined_AddressDescriptor label () s = .ok a t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rw [UndefSummaries.AddressDescriptor_eq]
  delta UndefSummaries.AddressDescriptor_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩
#print axioms undefined_address_total

theorem undefined_walk_total (label : ChoiceLabel) (s : State) :
    ∃ (w : TTWState) (t : State), undefined_TTWState label () s = .ok w t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rw [walk_eq]
  delta walk_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩
theorem undefined_full_address_total (label : ChoiceLabel) (s : State) :
    ∃ (a : FullAddress) (t : State), undefined_FullAddress label () s = .ok a t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rw [UndefSummaries.FullAddress_eq]
  delta UndefSummaries.FullAddress_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩
theorem bits_at_total (n : Nat) (label : ChoiceLabel) (s : State) :
    ∃ d : BitVec n, undefined_bitvector_at label n s = .ok d s := by
  exact ⟨_, rfl⟩
#print axioms undefined_walk_total
#print axioms undefined_full_address_total
#print axioms bits_at_total
end S1Unknowns
