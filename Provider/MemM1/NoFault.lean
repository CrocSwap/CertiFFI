import Walk.S1UnknownFault
import Walk.S1Normality
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
namespace MemM1.NoFault
abbrev State := SequentialState Regs oracleChoiceSource

/-- GPCNoFault draws nothing that touches registers, memory or events. -/
theorem gpc (s : State) : ∃ g t, GPCNoFault () s = .ok g t ∧ S1Normality.Frame s t := by
  unfold GPCNoFault
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, UndefSummaries.GPCFRecord_eq]
  delta UndefSummaries.GPCFRecord_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- NoFault__1 returns a Fault_None record and only changes choice state. -/
theorem nofault (acc : AccessDescriptor) (s : State) :
    ∃ f t, NoFault__1 acc s = .ok f t ∧ f.statuscode = .Fault_None ∧ S1Normality.Frame s t := by
  unfold NoFault__1 GPCNoFault
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, UndefSummaries.GPCFRecord_eq,
    UndefSummaries.FaultRecord_eq]
  delta UndefSummaries.GPCFRecord_native UndefSummaries.FaultRecord_native
  exact ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩
/-- undefined_AddressDescriptor draws only change choice state. -/
theorem addr (label : ChoiceLabel) (s : State) :
    ∃ a t, undefined_AddressDescriptor label () s = .ok a t ∧ S1Normality.Frame s t := by
  rw [UndefSummaries.AddressDescriptor_eq]
  delta UndefSummaries.AddressDescriptor_native
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem frame_trans {s t u : State} (h1 : S1Normality.Frame s t) (h2 : S1Normality.Frame t u) :
    S1Normality.Frame s u :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

#print axioms addr
#print axioms gpc
#print axioms nofault
end MemM1.NoFault
