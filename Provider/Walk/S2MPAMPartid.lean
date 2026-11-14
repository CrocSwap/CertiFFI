import Walk.S2MPAMFields
import Walk.S2Finite
import Walk.S2MPAMRange
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2MPAMPartid
open Lean Elab Tactic
private partial def packPartid : TacticM Unit := do
  let saved ← saveState
  try
    evalTactic (← `(tactic| rfl))
  catch _ =>
    saved.restore
    let goal ← getMainGoal
    let some (left, right) ← Lean.Meta.splitIfTarget? goal (useNewSemantics := true)
      | throwError "no conditional in PARTID packing goal"
    let branches := [left.mvarId, right.mvarId]
    for branch in branches do
      setGoals [branch]
      packPartid
    setGoals []
elab "s2_pack_partid" : tactic => packPartid
abbrev State := SequentialState Regs oracleChoiceSource
abbrev Result := EStateM.Result (Sail.Error exception) State ((BitVec 16 × Bool))
def value : Result → (BitVec 16 × Bool)
  | .ok v _ => v
  | .error _ _ => (0#16, false)
def occ : Result → Std.ExtHashMap Nat Nat
  | .ok _ s => s.choiceOcc
  | .error _ s => s.choiceOcc
def choose {α : Type} (x : BitVec 2) (a b c d : α) : α :=
  if x = 0#2 then a else if x = 1#2 then b else if x = 2#2 then c else d
theorem packed0 (s : State) :
    S2MPAMFields.partid0 s = .ok (value (S2MPAMFields.partid0 s))
      {s with choiceOcc := occ (S2MPAMFields.partid0 s)} := by
  delta S2MPAMFields.partid0
  s2_pack_partid
theorem packed1 (s : State) :
    S2MPAMFields.partid1 s = .ok (value (S2MPAMFields.partid1 s))
      {s with choiceOcc := occ (S2MPAMFields.partid1 s)} := by
  delta S2MPAMFields.partid1
  s2_pack_partid
theorem packed2 (s : State) :
    S2MPAMFields.partid2 s = .ok (value (S2MPAMFields.partid2 s))
      {s with choiceOcc := occ (S2MPAMFields.partid2 s)} := by
  delta S2MPAMFields.partid2
  s2_pack_partid
theorem packed3 (s : State) :
    S2MPAMFields.partid3 s = .ok (value (S2MPAMFields.partid3 s))
      {s with choiceOcc := occ (S2MPAMFields.partid3 s)} := by
  delta S2MPAMFields.partid3
  s2_pack_partid
noncomputable def native (el : BitVec 2) (s : State) : Result :=
  .ok (choose el (value (S2MPAMFields.partid0 s)) (value (S2MPAMFields.partid1 s)) (value (S2MPAMFields.partid2 s)) (value (S2MPAMFields.partid3 s)))
    {s with choiceOcc := choose el (occ (S2MPAMFields.partid0 s)) (occ (S2MPAMFields.partid1 s)) (occ (S2MPAMFields.partid2 s)) (occ (S2MPAMFields.partid3 s))}

theorem complete (el : BitVec 2) (s : State) :
    genPARTID el false false s = native el s := by
  by_cases h0 : el = 0#2
  · subst el
    simpa [native, choose] using (S2MPAMFields.partidEq0 s).trans (packed0 s)
  by_cases h1 : el = 1#2
  · subst el
    simpa [native, choose] using (S2MPAMFields.partidEq1 s).trans (packed1 s)
  by_cases h2 : el = 2#2
  · subst el
    simpa [native, choose] using (S2MPAMFields.partidEq2 s).trans (packed2 s)
  have h3 : el = 3#2 := by
    have hb := el.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  subst el
  simpa [native, choose] using (S2MPAMFields.partidEq3 s).trans (packed3 s)
attribute [-step_summary] S2MPAMFields.partidComplete
attribute [step_summary] complete
#print axioms complete
end S2MPAMPartid


