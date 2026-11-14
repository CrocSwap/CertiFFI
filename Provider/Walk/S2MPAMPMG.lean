import Walk.S2MPAMFields
import Walk.S2Finite
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2MPAMPMG
abbrev State := SequentialState Regs oracleChoiceSource
abbrev Result := EStateM.Result (Sail.Error exception) State (BitVec 8)
def value : Result → BitVec 8
  | .ok v _ => v
  | .error _ _ => 0#8
def occ : Result → Std.ExtHashMap Nat Nat
  | .ok _ s => s.choiceOcc
  | .error _ s => s.choiceOcc
def choose {α : Type} (x : BitVec 2) (a b c d : α) : α :=
  if x = 0#2 then a else if x = 1#2 then b else if x = 2#2 then c else d
theorem packed0 (err : Bool) (s : State) :
    S2MPAMFields.pmg0 err s = .ok (value (S2MPAMFields.pmg0 err s))
      {s with choiceOcc := occ (S2MPAMFields.pmg0 err s)} := by
  delta S2MPAMFields.pmg0
  repeat (first | rfl | split)
theorem packed1 (err : Bool) (s : State) :
    S2MPAMFields.pmg1 err s = .ok (value (S2MPAMFields.pmg1 err s))
      {s with choiceOcc := occ (S2MPAMFields.pmg1 err s)} := by
  delta S2MPAMFields.pmg1
  repeat (first | rfl | split)
theorem packed2 (err : Bool) (s : State) :
    S2MPAMFields.pmg2 err s = .ok (value (S2MPAMFields.pmg2 err s))
      {s with choiceOcc := occ (S2MPAMFields.pmg2 err s)} := by
  delta S2MPAMFields.pmg2
  repeat (first | rfl | split)
theorem packed3 (err : Bool) (s : State) :
    S2MPAMFields.pmg3 err s = .ok (value (S2MPAMFields.pmg3 err s))
      {s with choiceOcc := occ (S2MPAMFields.pmg3 err s)} := by
  delta S2MPAMFields.pmg3
  repeat (first | rfl | split)
noncomputable def native (el : BitVec 2) (err : Bool) (s : State) : Result :=
  .ok (choose el (value (S2MPAMFields.pmg0 err s)) (value (S2MPAMFields.pmg1 err s)) (value (S2MPAMFields.pmg2 err s)) (value (S2MPAMFields.pmg3 err s)))
    {s with choiceOcc := choose el (occ (S2MPAMFields.pmg0 err s)) (occ (S2MPAMFields.pmg1 err s)) (occ (S2MPAMFields.pmg2 err s)) (occ (S2MPAMFields.pmg3 err s))}

theorem complete (el : BitVec 2) (err : Bool) (s : State) :
    genPMG el false false err s = native el err s := by
  by_cases h0 : el = 0#2
  · subst el
    simpa [native, choose] using (S2MPAMFields.pmgEq0 err s).trans (packed0 err s)
  by_cases h1 : el = 1#2
  · subst el
    simpa [native, choose] using (S2MPAMFields.pmgEq1 err s).trans (packed1 err s)
  by_cases h2 : el = 2#2
  · subst el
    simpa [native, choose] using (S2MPAMFields.pmgEq2 err s).trans (packed2 err s)
  have h3 : el = 3#2 := by
    have hb := el.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  subst el
  simpa [native, choose] using (S2MPAMFields.pmgEq3 err s).trans (packed3 err s)
attribute [-step_summary] S2MPAMFields.pmgComplete
attribute [step_summary] complete
#print axioms complete
end S2MPAMPMG

