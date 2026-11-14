import Pilot.Driver
import Walk.S2Finite
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2Shareability
drive_spec native0, eq0 : fun (s : SequentialState Regs oracleChoiceSource) =>
  DecodeShareability 0#2 s
drive_spec native1, eq1 : fun (s : SequentialState Regs oracleChoiceSource) =>
  DecodeShareability 1#2 s
drive_spec native2, eq2 : fun (s : SequentialState Regs oracleChoiceSource) =>
  DecodeShareability 2#2 s
drive_spec native3, eq3 : fun (s : SequentialState Regs oracleChoiceSource) =>
  DecodeShareability 3#2 s
abbrev State := SequentialState Regs oracleChoiceSource
abbrev Result := EStateM.Result (Sail.Error exception) State Shareability
def value : Result → Shareability
  | .ok x _ => x
  | .error _ _ => default
def occ : Result → Std.ExtHashMap Nat Nat
  | .ok _ s => s.choiceOcc
  | .error _ s => s.choiceOcc
def choose {α : Type} (x : BitVec 2) (a b c d : α) : α :=
  if x = 0#2 then a else if x = 1#2 then b else if x = 2#2 then c else d
noncomputable def native (x : BitVec 2) (s : State) : Result :=
  .ok (choose x (value (native0 s)) (value (native1 s)) (value (native2 s)) (value (native3 s)))
    {s with choiceOcc := (choose x (occ (native0 s)) (occ (native1 s)) (occ (native2 s)) (occ (native3 s)))}
theorem packed0 (s : State) :
    native0 s = .ok (value (native0 s)) {s with choiceOcc := occ (native0 s)} := by
  delta native0
  first | rfl | (s2_cases_constraint <;> rfl)
theorem packed1 (s : State) :
    native1 s = .ok (value (native1 s)) {s with choiceOcc := occ (native1 s)} := by
  delta native1
  first | rfl | (s2_cases_constraint <;> rfl)
theorem packed2 (s : State) :
    native2 s = .ok (value (native2 s)) {s with choiceOcc := occ (native2 s)} := by
  delta native2
  first | rfl | (s2_cases_constraint <;> rfl)
theorem packed3 (s : State) :
    native3 s = .ok (value (native3 s)) {s with choiceOcc := occ (native3 s)} := by
  delta native3
  first | rfl | (s2_cases_constraint <;> rfl)
theorem complete (x : BitVec 2) (s : State) : DecodeShareability x s = native x s := by
  by_cases h0 : x = 0#2
  · simpa [native, choose, h0] using (eq0 s).trans (packed0 s)
  by_cases h1 : x = 1#2
  · simpa [native, choose, h1] using (eq1 s).trans (packed1 s)
  by_cases h2 : x = 2#2
  · simpa [native, choose, h2] using (eq2 s).trans (packed2 s)
  have h3 : x = 3#2 := by
    have hb := x.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  simpa [native, choose, h3] using (eq3 s).trans (packed3 s)
attribute [step_summary] complete
#print axioms complete
end S2Shareability
