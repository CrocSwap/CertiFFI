import Pilot.Driver
import Walk.S2MPAMMap
import Walk.S2MPAMRange
import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2MPAMFields
attribute [-step_summary] S2MPAMMap.complete
abbrev State := SequentialState Regs oracleChoiceSource
drive_spec partid0, partidEq0 : fun (s : State)
    => genPARTID 0#2 false false s
drive_spec partid1, partidEq1 : fun (s : State)
    => genPARTID 1#2 false false s
drive_spec partid2, partidEq2 : fun (s : State)
    => genPARTID 2#2 false false s
drive_spec partid3, partidEq3 : fun (s : State)
    => genPARTID 3#2 false false s
noncomputable def partidNative (el : BitVec 2) (s : State) : EStateM.Result (Sail.Error exception) State (BitVec 16 × Bool) :=
  if el = 0#2 then partid0 s else
  if el = 1#2 then partid1 s else
  if el = 2#2 then partid2 s else partid3 s
theorem partidComplete (el : BitVec 2) (s : State) :
    genPARTID el false false s = partidNative el s := by
  by_cases h0 : el = 0#2
  · subst el
    simpa [partidNative] using partidEq0 s
  by_cases h1 : el = 1#2
  · subst el
    simpa [partidNative] using partidEq1 s
  by_cases h2 : el = 2#2
  · subst el
    simpa [partidNative] using partidEq2 s
  have h3 : el = 3#2 := by
    have hb := el.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  subst el
  simpa [partidNative] using partidEq3 s
attribute [step_summary] partidComplete
#print axioms partidComplete
drive_spec pmg0, pmgEq0 : fun (err : Bool) (s : State)
    => genPMG 0#2 false false err s
drive_spec pmg1, pmgEq1 : fun (err : Bool) (s : State)
    => genPMG 1#2 false false err s
drive_spec pmg2, pmgEq2 : fun (err : Bool) (s : State)
    => genPMG 2#2 false false err s
drive_spec pmg3, pmgEq3 : fun (err : Bool) (s : State)
    => genPMG 3#2 false false err s
noncomputable def pmgNative (el : BitVec 2) (err : Bool) (s : State) : EStateM.Result (Sail.Error exception) State (BitVec 8) :=
  if el = 0#2 then pmg0 err s else
  if el = 1#2 then pmg1 err s else
  if el = 2#2 then pmg2 err s else pmg3 err s
theorem pmgComplete (el : BitVec 2) (err : Bool) (s : State) :
    genPMG el false false err s = pmgNative el err s := by
  by_cases h0 : el = 0#2
  · subst el
    simpa [pmgNative] using pmgEq0 err s
  by_cases h1 : el = 1#2
  · subst el
    simpa [pmgNative] using pmgEq1 err s
  by_cases h2 : el = 2#2
  · subst el
    simpa [pmgNative] using pmgEq2 err s
  have h3 : el = 3#2 := by
    have hb := el.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  subst el
  simpa [pmgNative] using pmgEq3 err s
attribute [step_summary] pmgComplete
#print axioms pmgComplete
end S2MPAMFields

