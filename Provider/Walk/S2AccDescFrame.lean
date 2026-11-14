import Walk.S2AccDesc
import Walk.S1AccDescFrame
import Walk.S2MPAMPartid
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2AccDescFrame
open Lean Elab Tactic
private partial def packAcc : TacticM Unit := do
  let saved ← saveState
  try
    evalTactic (← `(tactic| first | rfl | contradiction |
      (solve | simp_all [EL0, EL1, EL2, EL3]) |
      exact S2MPAMRange.pack_state s _ _ _ | exact S2MPAMRange.pack_state_dep s _ _ _))
  catch _ =>
    saved.restore
    let goal ← getMainGoal
    let some (left, right) ← Lean.Meta.splitIfTarget? goal (useNewSemantics := true)
      | throwError "no conditional in access descriptor goal: {← goal.getType}"
    for branch in [left.mvarId, right.mvarId] do
      setGoals [branch]
      packAcc
    setGoals []
elab "s2_pack_acc" : tactic => packAcc
abbrev State := SequentialState Regs oracleChoiceSource
abbrev Result := EStateM.Result (Sail.Error exception) State AccessDescriptor
def value : Result → AccessDescriptor
  | .ok v _ => v
  | .error _ _ => default
def occ : Result → Std.ExtHashMap Nat Nat
  | .ok _ s => s.choiceOcc
  | .error _ s => s.choiceOcc
def GuestEL (s : State) : Prop := s.regs.PSTATE.EL = 0#2 ∨ s.regs.PSTATE.EL = 1#2
noncomputable def normal (r : Result) (s : State) : Result :=
  .ok (value r) {s with choiceOcc := occ r}

theorem normal_bridge (r : Result) (s : State) : normal r s = S1AccDescFrame.normal r s := by
  cases r <;> rfl

theorem new_packed0 (s : State) (h : s.regs.PSTATE.EL = 0#2) :
    S2AccDesc.new_native s = normal (S2AccDesc.new_native s) s := by
  rw [normal_bridge]
  exact S1AccDescFrame.native_packed s (Or.inl h)

theorem new_packed1 (s : State) (h : s.regs.PSTATE.EL = 1#2) :
    S2AccDesc.new_native s = normal (S2AccDesc.new_native s) s := by
  rw [normal_bridge]
  exact S1AccDescFrame.native_packed s (Or.inr h)

theorem new_packed (s : State) (hGuest : GuestEL s) :
    S2AccDesc.new_native s = normal (S2AccDesc.new_native s) s := by
  cases hGuest with
  | inl h => exact new_packed0 s h
  | inr h => exact new_packed1 s h

theorem new_total (s : State) (hGuest : GuestEL s)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) :
    ∃ (out : AccessDescriptor) (t : State),
      NewAccDesc .AccessType_TTW s = .ok out t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  refine ⟨value (S2AccDesc.new_native s),
    {s with choiceOcc := occ (S2AccDesc.new_native s)}, ?_, rfl, rfl, rfl⟩
  exact (S2AccDesc.new_eq s hNoRME hA64 hEL3A64 hNoEL3A32).trans (new_packed s hGuest)

def updated (acc base : AccessDescriptor) : AccessDescriptor :=
  {base with el := acc.el, ss := acc.ss, atomicop := true, modop := .MemAtomicOp_CAS, read := true, write := true, mpam := acc.mpam}
def reader (acc base : AccessDescriptor) : AccessDescriptor :=
  {base with el := acc.el, ss := acc.ss, read := true, mpam := acc.mpam}

theorem update_total (acc : AccessDescriptor) (s : State) (hGuest : GuestEL s)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) :
    ∃ (base : AccessDescriptor) (t : State),
      CreateAccDescTTEUpdate acc s = .ok (updated acc base) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rcases new_total s hGuest hNoRME hA64 hEL3A64 hNoEL3A32 with
    ⟨base, t, hr, hregs, hmem, hevents⟩
  refine ⟨base, t, ?_, hregs, hmem, hevents⟩
  simp [CreateAccDescTTEUpdate, updated, Bind.bind, Pure.pure,
    EStateM.bind, EStateM.pure, hr]

theorem read_total (acc : AccessDescriptor) (s : State) (hGuest : GuestEL s)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) :
    ∃ (base : AccessDescriptor) (t : State),
      CreateAccDescS2TTW acc s = .ok (reader acc base) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rcases new_total s hGuest hNoRME hA64 hEL3A64 hNoEL3A32 with
    ⟨base, t, hr, hregs, hmem, hevents⟩
  refine ⟨base, t, ?_, hregs, hmem, hevents⟩
  simp [CreateAccDescS2TTW, reader, Bind.bind, Pure.pure,
    EStateM.bind, EStateM.pure, hr]
#print axioms new_packed
#print axioms new_total
#print axioms update_total
#print axioms read_total
end S2AccDescFrame
