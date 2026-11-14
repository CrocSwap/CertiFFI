import Walk.S1AccDescFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1ReadAccDesc
abbrev State := S1AccDescFrame.State

def value (toplevel : Bool) (varange : VARange) (acc base : AccessDescriptor) : AccessDescriptor :=
  {base with
    el := acc.el
    ss := acc.ss
    read := true
    toplevel := toplevel
    varange := varange
    mpam := acc.mpam}

theorem total (toplevel : Bool) (varange : VARange) (acc : AccessDescriptor) (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) :
    ∃ (base : AccessDescriptor) (t : State),
      CreateAccDescS1TTW toplevel varange acc s = .ok (value toplevel varange acc base) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rcases S1AccDescFrame.new_total s hEL hNoRME hA64 hEL3A64 hNoEL3A32 with
    ⟨base, t, hr, hregs, hmem, hevents⟩
  refine ⟨base, t, ?_, hregs, hmem, hevents⟩
  simp [CreateAccDescS1TTW, value, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, hr]
#print axioms total
end S1ReadAccDesc
