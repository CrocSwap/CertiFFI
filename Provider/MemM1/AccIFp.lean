import Walk.S1EL2Enabled
import Walk.S1Normality
import Walk.S2MPAMCombinedFrame
import Walk.S2SecurityEL
import Walk.S2AccDescFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.AccIFp
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

drive_spec ss_native, ss_eq : fun (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false) (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1) =>
  SecurityStateAtEL 0#2 s

theorem ss0 (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false) (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1) :
    ∃ t, SecurityStateAtEL 0#2 s = .ok .SS_NonSecure t ∧ Frame s t := by
  rw [ss_eq s hNoRME hAA hNS]
  observe_simp [Frame, ss_native]
  exact ⟨_, ⟨hNS, rfl⟩, rfl, rfl, rfl⟩
#print axioms ss0

/-! ### MPAM for an instruction fetch (InD = true): the eval S2MPAM* chain, re-driven with InD = true.
`value`/`occ`/`choose` and the packing tactic are eval's (S2MPAMPartid / S2MPAMPMG /
S2MPAMCombinedFrame). -/
attribute [-step_summary] S2MPAMMap.complete
drive_spec pid0, pidEq0 : fun (s : State) => genPARTID 0#2 true false s
drive_spec pid1, pidEq1 : fun (s : State) => genPARTID 1#2 true false s
drive_spec pid2, pidEq2 : fun (s : State) => genPARTID 2#2 true false s
drive_spec pid3, pidEq3 : fun (s : State) => genPARTID 3#2 true false s
drive_spec pmg0, pmgEq0 : fun (err : Bool) (s : State) => genPMG 0#2 true false err s
drive_spec pmg1, pmgEq1 : fun (err : Bool) (s : State) => genPMG 1#2 true false err s
drive_spec pmg2, pmgEq2 : fun (err : Bool) (s : State) => genPMG 2#2 true false err s
drive_spec pmg3, pmgEq3 : fun (err : Bool) (s : State) => genPMG 3#2 true false err s

section
open S2MPAMPartid
theorem pidP0 (s : State) : pid0 s = .ok (value (pid0 s)) {s with choiceOcc := occ (pid0 s)} := by
  delta pid0; s2_pack_partid
theorem pidP1 (s : State) : pid1 s = .ok (value (pid1 s)) {s with choiceOcc := occ (pid1 s)} := by
  delta pid1; s2_pack_partid
theorem pidP2 (s : State) : pid2 s = .ok (value (pid2 s)) {s with choiceOcc := occ (pid2 s)} := by
  delta pid2; s2_pack_partid
theorem pidP3 (s : State) : pid3 s = .ok (value (pid3 s)) {s with choiceOcc := occ (pid3 s)} := by
  delta pid3; s2_pack_partid
noncomputable def pidNative (el : BitVec 2) (s : State) : S2MPAMPartid.Result :=
  .ok (choose el (value (pid0 s)) (value (pid1 s)) (value (pid2 s)) (value (pid3 s)))
    {s with choiceOcc := choose el (occ (pid0 s)) (occ (pid1 s)) (occ (pid2 s)) (occ (pid3 s))}
theorem pidComplete (el : BitVec 2) (s : State) : genPARTID el true false s = pidNative el s := by
  by_cases h0 : el = 0#2
  · subst el
    simpa [pidNative, choose] using (pidEq0 s).trans (pidP0 s)
  by_cases h1 : el = 1#2
  · subst el
    simpa [pidNative, choose] using (pidEq1 s).trans (pidP1 s)
  by_cases h2 : el = 2#2
  · subst el
    simpa [pidNative, choose] using (pidEq2 s).trans (pidP2 s)
  have h3 : el = 3#2 := by
    have hb := el.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  subst el
  simpa [pidNative, choose] using (pidEq3 s).trans (pidP3 s)
end
attribute [step_summary] pidComplete

section
open S2MPAMPMG
theorem pmgP0 (err : Bool) (s : State) :
    pmg0 err s = .ok (value (pmg0 err s)) {s with choiceOcc := occ (pmg0 err s)} := by
  delta pmg0; repeat (first | rfl | split)
theorem pmgP1 (err : Bool) (s : State) :
    pmg1 err s = .ok (value (pmg1 err s)) {s with choiceOcc := occ (pmg1 err s)} := by
  delta pmg1; repeat (first | rfl | split)
theorem pmgP2 (err : Bool) (s : State) :
    pmg2 err s = .ok (value (pmg2 err s)) {s with choiceOcc := occ (pmg2 err s)} := by
  delta pmg2; repeat (first | rfl | split)
theorem pmgP3 (err : Bool) (s : State) :
    pmg3 err s = .ok (value (pmg3 err s)) {s with choiceOcc := occ (pmg3 err s)} := by
  delta pmg3; repeat (first | rfl | split)
noncomputable def pmgNative (el : BitVec 2) (err : Bool) (s : State) : S2MPAMPMG.Result :=
  .ok (choose el (value (pmg0 err s)) (value (pmg1 err s)) (value (pmg2 err s)) (value (pmg3 err s)))
    {s with choiceOcc := choose el (occ (pmg0 err s)) (occ (pmg1 err s)) (occ (pmg2 err s)) (occ (pmg3 err s))}
theorem pmgComplete (el : BitVec 2) (err : Bool) (s : State) :
    genPMG el true false err s = pmgNative el err s := by
  by_cases h0 : el = 0#2
  · subst el
    simpa [pmgNative, choose] using (pmgEq0 err s).trans (pmgP0 err s)
  by_cases h1 : el = 1#2
  · subst el
    simpa [pmgNative, choose] using (pmgEq1 err s).trans (pmgP1 err s)
  by_cases h2 : el = 2#2
  · subst el
    simpa [pmgNative, choose] using (pmgEq2 err s).trans (pmgP2 err s)
  have h3 : el = 3#2 := by
    have hb := el.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  subst el
  simpa [pmgNative, choose] using (pmgEq3 err s).trans (pmgP3 err s)
end
attribute [step_summary] pmgComplete

drive_spec mpam_native, mpamEq : fun (el : BitVec 2) (pspace : PARTIDspaceType) (s : State) =>
  genMPAM el true false pspace s

noncomputable def mpamNormal (el : BitVec 2) (pspace : PARTIDspaceType) (s : State) :
    S2MPAMCombinedFrame.Result :=
  .ok (S2MPAMCombinedFrame.value (mpam_native el pspace s))
    {s with choiceOcc := S2MPAMCombinedFrame.occ (mpam_native el pspace s)}
theorem mpamPacked (el : BitVec 2) (pspace : PARTIDspaceType) (s : State) :
    mpam_native el pspace s = mpamNormal el pspace s := by
  delta mpamNormal mpam_native
  s2_pack_partid
theorem mpamComplete (el : BitVec 2) (pspace : PARTIDspaceType) (s : State) :
    genMPAM el true false pspace s = mpamNormal el pspace s :=
  (mpamEq el pspace s).trans (mpamPacked el pspace s)
attribute [step_summary] mpamComplete

#print axioms pidComplete
#print axioms pmgComplete
#print axioms mpamComplete

end MemM1.AccIFp
