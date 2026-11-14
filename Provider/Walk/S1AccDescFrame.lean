import Walk.S2AccDesc
import Walk.S2Frame
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
set_option pp.maxSteps 2000
namespace S1AccDescFrame
abbrev State := SequentialState Regs oracleChoiceSource
abbrev Result := EStateM.Result (Sail.Error exception) State AccessDescriptor
def Frame (s : State) : Result → Prop
  | .ok _ t => t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events ∧
      t.choiceState = s.choiceState ∧ t.tags = s.tags ∧
      t.cycleCount = s.cycleCount ∧ t.sailOutput = s.sailOutput
  | .error _ _ => False
theorem native_frame0 (s : State) (h : s.regs.PSTATE.EL = 0#2) :
    Frame s (S2AccDesc.new_native s) := by
  observe_simp [Frame, S2AccDesc.new_native]
theorem native_frame1 (s : State) (h : s.regs.PSTATE.EL = 1#2) :
    Frame s (S2AccDesc.new_native s) := by
  observe_simp [Frame, S2AccDesc.new_native]
#print axioms native_frame0
#print axioms native_frame1

theorem new_total (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) :
    ∃ (out : AccessDescriptor) (t : State), NewAccDesc .AccessType_TTW s = .ok out t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rw [S2AccDesc.new_eq s hNoRME hA64 hEL3A64 hNoEL3A32]
  have hf : Frame s (S2AccDesc.new_native s) := by
    rcases hEL with h | h
    · exact native_frame0 s h
    · exact native_frame1 s h
  cases hr : S2AccDesc.new_native s with
  | error err t => simp only [hr, Frame] at hf
  | ok out t =>
    simp only [hr, Frame] at hf
    exact ⟨out, t, rfl, hf.1, hf.2.1, hf.2.2.1⟩

def value : Result → AccessDescriptor
  | .ok a _ => a
  | .error _ _ => default
def occ : Result → Std.ExtHashMap Nat Nat
  | .ok _ t => t.choiceOcc
  | .error _ t => t.choiceOcc
noncomputable def normal (r : Result) (s : State) : Result :=
  .ok (value r) {s with choiceOcc := occ r}

theorem native_packed (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2) :
    S2AccDesc.new_native s = normal (S2AccDesc.new_native s) s := by
  have hf : Frame s (S2AccDesc.new_native s) := by
    rcases hEL with h | h
    · exact native_frame0 s h
    · exact native_frame1 s h
  cases hr : S2AccDesc.new_native s with
  | error err t => simp only [hr, Frame] at hf
  | ok out t =>
    simp only [hr, Frame] at hf
    have hs : t = {s with choiceOcc := t.choiceOcc} := by
      cases s
      cases t
      simp_all
    simpa only [normal, hr, value, occ] using congrArg (EStateM.Result.ok out) hs

def updated (acc base : AccessDescriptor) : AccessDescriptor :=
  {base with
    el := acc.el
    ss := acc.ss
    atomicop := true
    modop := .MemAtomicOp_CAS
    read := true
    write := true
    mpam := acc.mpam}

theorem update_total (acc : AccessDescriptor) (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) :
    ∃ (base : AccessDescriptor) (t : State),
      CreateAccDescTTEUpdate acc s = .ok (updated acc base) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rcases new_total s hEL hNoRME hA64 hEL3A64 hNoEL3A32 with
    ⟨base, t, hr, hregs, hmem, hevents⟩
  refine ⟨base, t, ?_, hregs, hmem, hevents⟩
  simp [CreateAccDescTTEUpdate, updated, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, hr]

#print axioms new_total
#print axioms update_total
#print axioms native_packed
end S1AccDescFrame
