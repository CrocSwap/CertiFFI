import NativeEntryCallerParts.Project
import NativeEntryCallerParts.ShellPrimitives
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeEntryCallerParts
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option Elab.async false

theorem address_regs (target : BitVec 64) (s : NativeState) :
    (addressState target s).regs = s.regs := by
  unfold addressState address_native
  simp only [no_a32_regime, Bool.false_eq_true, false_and, and_false, result_regs_ite, result_regs_dite, state_regs_ite, state_regs_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem address_mem (target : BitVec 64) (s : NativeState) :
    (addressState target s).mem = s.mem := by
  unfold addressState address_native
  simp only [no_a32_regime, Bool.false_eq_true, false_and, and_false, result_mem_ite, result_mem_dite, state_mem_ite, state_mem_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem address_events (target : BitVec 64) (s : NativeState) :
    (addressState target s).events = s.events := by
  unfold addressState address_native
  simp only [no_a32_regime, Bool.false_eq_true, false_and, and_false, result_events_ite, result_events_dite, state_events_ite, state_events_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem address_tags (target : BitVec 64) (s : NativeState) :
    (addressState target s).tags = s.tags := by
  unfold addressState address_native
  simp only [no_a32_regime, Bool.false_eq_true, false_and, and_false, result_tags_ite, result_tags_dite, state_tags_ite, state_tags_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem address_cycleCount (target : BitVec 64) (s : NativeState) :
    (addressState target s).cycleCount = s.cycleCount := by
  unfold addressState address_native
  simp only [no_a32_regime, Bool.false_eq_true, false_and, and_false, result_cycleCount_ite, result_cycleCount_dite, state_cycleCount_ite, state_cycleCount_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem address_sailOutput (target : BitVec 64) (s : NativeState) :
    (addressState target s).sailOutput = s.sailOutput := by
  unfold addressState address_native
  simp only [no_a32_regime, Bool.false_eq_true, false_and, and_false, result_sailOutput_ite, result_sailOutput_dite, state_sailOutput_ite, state_sailOutput_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem address_choiceState (target : BitVec 64) (s : NativeState) :
    (addressState target s).choiceState = s.choiceState := by
  unfold addressState address_native
  simp only [no_a32_regime, Bool.false_eq_true, false_and, and_false, result_choiceState_ite, result_choiceState_dite, state_choiceState_ite, state_choiceState_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem address_controls (target : BitVec 64) (s : NativeState) (hp : CallerControls s) :
    CallerControls (addressState target s) where
  f4 := by simpa only [address_regs] using hp.f4
  f2 := by simpa only [address_regs] using hp.f2
  f3 := by simpa only [address_regs] using hp.f3
  f6 := by simpa only [address_regs] using hp.f6
  f7 := by simpa only [address_regs] using hp.f7
  rme := by simpa only [address_regs] using hp.rme
  vhe := by simpa only [address_regs] using hp.vhe
  brbe := by simpa only [address_regs] using hp.brbe
  el := by simpa only [address_regs] using hp.el
  nrw := by simpa only [address_regs] using hp.nrw
  e2h := by simpa only [address_regs] using hp.e2h
  tge := by simpa only [address_regs] using hp.tge
  ns := by simpa only [address_regs] using hp.ns
  pmb := by simpa only [address_regs] using hp.pmb
  spe := by simpa only [address_regs] using hp.spe
  pmbs := by simpa only [address_regs] using hp.pmbs
  nspb := by simpa only [address_regs] using hp.nspb
  nspbe := by simpa only [address_regs] using hp.nspbe
  gcsEn := by simpa only [address_regs] using hp.gcsEn

theorem spe_regs (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).regs = SPESamplePreviousBranchAddressValid.set false s.regs := by
  unfold speState spe_native
  simp only [result_regs_ite, result_regs_dite, state_regs_ite, state_regs_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem spe_PSTATE (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).regs.PSTATE = s.regs.PSTATE := by
  rw [spe_regs]
  rfl

theorem spe_BTypeNext (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).regs.BTypeNext = s.regs.BTypeNext := by
  rw [spe_regs]
  rfl

theorem spe_Branchtypetaken (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).regs.Branchtypetaken = s.regs.Branchtypetaken := by
  rw [spe_regs]
  rfl

theorem spe_gpr (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).regs.gpr = s.regs.gpr := by
  rw [spe_regs]
  rfl

theorem spe__PC (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).regs._PC = s.regs._PC := by
  rw [spe_regs]
  rfl

theorem spe_FeatureImpl (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).regs.FeatureImpl = s.regs.FeatureImpl := by
  rw [spe_regs]
  rfl

theorem spe__Z (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).regs._Z = s.regs._Z := by
  rw [spe_regs]
  rfl

theorem spe_FPCR (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).regs.FPCR = s.regs.FPCR := by
  rw [spe_regs]
  rfl

theorem spe_FPSR (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).regs.FPSR = s.regs.FPSR := by
  rw [spe_regs]
  rfl

theorem spe_SP_EL0 (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).regs.SP_EL0 = s.regs.SP_EL0 := by
  rw [spe_regs]
  rfl

theorem spe_mem (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).mem = s.mem := by
  unfold speState spe_native
  simp only [result_mem_ite, result_mem_dite, state_mem_ite, state_mem_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem spe_events (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).events = s.events := by
  unfold speState spe_native
  simp only [result_events_ite, result_events_dite, state_events_ite, state_events_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem spe_tags (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).tags = s.tags := by
  unfold speState spe_native
  simp only [result_tags_ite, result_tags_dite, state_tags_ite, state_tags_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem spe_cycleCount (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).cycleCount = s.cycleCount := by
  unfold speState spe_native
  simp only [result_cycleCount_ite, result_cycleCount_dite, state_cycleCount_ite, state_cycleCount_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem spe_sailOutput (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).sailOutput = s.sailOutput := by
  unfold speState spe_native
  simp only [result_sailOutput_ite, result_sailOutput_dite, state_sailOutput_ite, state_sailOutput_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem spe_choiceState (target : BitVec 64) (branch : BranchType) (conditional : Bool) (s : NativeState) :
    (speState target branch conditional s).choiceState = s.choiceState := by
  unfold speState spe_native
  simp only [result_choiceState_ite, result_choiceState_dite, state_choiceState_ite, state_choiceState_dite, resultState_ok, resultState_error, dite_eq_ite, ite_self]

theorem spe_controls (target : BitVec 64) (branch : BranchType) (conditional : Bool)
    (s : NativeState) (hp : CallerControls s) : CallerControls (speState target branch conditional s) where
  f4 := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.f4
  f2 := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.f2
  f3 := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.f3
  f6 := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.f6
  f7 := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.f7
  rme := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.rme
  vhe := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.vhe
  brbe := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.brbe
  el := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.el
  nrw := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.nrw
  e2h := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.e2h
  tge := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.tge
  ns := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.ns
  pmb := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.pmb
  spe := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.spe
  pmbs := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.pmbs
  nspb := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.nspb
  nspbe := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.nspbe
  gcsEn := by simpa (disch := decide) only [spe_regs, SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] using hp.gcsEn

def hintState (branch : BranchType) (s : NativeState) : NativeState :=
  { s with regs := Branchtypetaken.set branch s.regs }

theorem hint_run (branch : BranchType) (s : NativeState) :
    (Hint_Branch branch : SailM Unit) s = .ok () (hintState branch s) := rfl

theorem hint_controls (branch : BranchType) (s : NativeState) (hp : CallerControls s) :
    CallerControls (hintState branch s) where
  f4 := hp.f4
  f2 := hp.f2
  f3 := hp.f3
  f6 := hp.f6
  f7 := hp.f7
  rme := hp.rme
  vhe := hp.vhe
  brbe := hp.brbe
  el := hp.el
  nrw := hp.nrw
  e2h := hp.e2h
  tge := hp.tge
  ns := hp.ns
  pmb := hp.pmb
  spe := hp.spe
  pmbs := hp.pmbs
  nspb := hp.nspb
  nspbe := hp.nspbe
  gcsEn := hp.gcsEn

theorem using32_run (s : NativeState) (hp : CallerControls s) :
    (UsingAArch32 () : SailM Bool) s = .ok false s := by
  simpa only [using32_native] using using32_complete s hp.f4 hp.nrw

theorem brbe_run (s : NativeState) (hp : CallerControls s) :
    (HaveBRBExt () : SailM Bool) s = .ok false s := by
  simpa only [brbe_native] using brbe_complete s hp.brbe

noncomputable def speFeature (s : NativeState) : Bool :=
  match haveSpe_native s with
  | .ok value _ => value
  | .error _ _ => false

theorem haveSpe_run (s : NativeState) :
    (HaveStatisticalProfiling () : SailM Bool) s = .ok (speFeature s) s := by
  rw [haveSpe_complete]
  rfl

theorem pure_run {α : Type} (value : α) (s : NativeState) :
    (pure value : SailM α) s = .ok value s := rfl

theorem assert_run (label : String) (s : NativeState) :
    (PreSail.assert true label : SailM Unit) s = .ok () s := rfl

theorem full_extract (target : BitVec 64) :
    Sail.BitVec.extractLsb target 63 0 = target := by
  exact BitVec.extractLsb'_eq_self

#print axioms address_regs
#print axioms address_mem
#print axioms address_events
#print axioms address_tags
#print axioms address_cycleCount
#print axioms address_sailOutput
#print axioms address_choiceState
#print axioms address_controls
#print axioms spe_regs
#print axioms spe_PSTATE
#print axioms spe_BTypeNext
#print axioms spe_Branchtypetaken
#print axioms spe_gpr
#print axioms spe__PC
#print axioms spe_FeatureImpl
#print axioms spe__Z
#print axioms spe_FPCR
#print axioms spe_FPSR
#print axioms spe_SP_EL0
#print axioms spe_mem
#print axioms spe_events
#print axioms spe_tags
#print axioms spe_cycleCount
#print axioms spe_sailOutput
#print axioms spe_choiceState
#print axioms spe_controls
#print axioms hint_run
#print axioms hint_controls
#print axioms using32_run
#print axioms brbe_run
#print axioms haveSpe_run
#print axioms pure_run
#print axioms assert_run
#print axioms full_extract
end NativeEntryCallerParts
