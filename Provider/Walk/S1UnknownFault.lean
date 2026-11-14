import Walk.S1Unknowns
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1UnknownFault
abbrev State := S1Unknowns.State

theorem total (label : ChoiceLabel) (s : State) :
    ∃ (f : FaultRecord) (t : State), undefined_FaultRecord label () s = .ok f t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rw [UndefSummaries.FaultRecord_eq]
  delta UndefSummaries.FaultRecord_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩
#print axioms total
end S1UnknownFault
