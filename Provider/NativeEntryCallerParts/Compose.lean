import NativeEntryCallerParts.AddrLow
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeEntryCallerParts
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def finishState (target : BitVec 64) (s : NativeState) : NativeState :=
  { s with regs := __BranchTaken.set true (_PC.set target s.regs) }

/- These expressions are actual intermediate states of the original function;
their choices, memory and history come from the primitive producer equations. -/
noncomputable def profileState (target : BitVec 64) (branch : BranchType) (s : NativeState) : NativeState :=
  let a := addressState target (hintState branch s)
  if speFeature a then speState target branch false a else a

noncomputable def branchState (target : BitVec 64) (branch : BranchType) (s : NativeState) : NativeState :=
  finishState (addressValue target (hintState branch s)) (profileState target branch s)

set_option backward.isDefEq.respectTransparency false in
theorem branch_run (target : BitVec 64) (branch : BranchType) (s : NativeState)
    (hp : CallerControls s) (bit55 : BitVec.access target 55 = 0#1) :
    (BranchTo target branch false : SailM Unit) s = .ok () (branchState target branch s) := by
  let h := hintState branch s
  let a := addressState target h
  have ph : CallerControls h := hint_controls branch s hp
  have pa : CallerControls a := address_controls target h ph
  change (BranchTo target branch false : SailM Unit) s =
    .ok () (finishState (addressValue target h) (if speFeature a then speState target branch false a else a))
  unfold BranchTo
  simp only [↓bind_app, hint_run, Sail.BitVec.length, Nat.reduceBEq,
    Bool.false_eq_true, Bool.cond_false, Bool.cond_true, ite_false, ite_true]
  rw [using32_run h ph]
  simp only [↓bind_app, Bool.not_false, ArmFull.assert, Bool.cond_true,
    pure_run, assert_run, PreSail.readReg_apply, PSTATE, full_extract]
  rw [ph.el, address_run target h ph bit55]
  simp only [↓bind_app]
  rw [brbe_run a pa]
  simp only [↓bind_app, pure_run, Bool.false_and, Bool.cond_false, Bool.false_eq_true, ite_false]
  rw [haveSpe_run a]
  simp only [↓bind_app]
  cases feature : speFeature a with
  | false =>
    simp only [feature, Bool.cond_false, Bool.false_eq_true, ite_false]
    rfl
  | true =>
    simp only [feature, Bool.cond_true, ite_true, ↓bind_app]
    rw [spe_run target branch false a pa]
    rfl


theorem finish_controls (target : BitVec 64) (s : NativeState) (hp : CallerControls s) :
    CallerControls (finishState target s) where
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

theorem branch_controls (target : BitVec 64) (branch : BranchType) (s : NativeState)
    (hp : CallerControls s) : CallerControls (branchState target branch s) := by
  unfold branchState profileState
  dsimp only []
  apply finish_controls
  split
  · exact spe_controls _ _ _ _ (address_controls _ _ (hint_controls _ _ hp))
  · exact address_controls _ _ (hint_controls _ _ hp)

theorem finish_BTypeNext (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.BTypeNext = s.regs.BTypeNext := rfl

theorem branch_BTypeNext (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.BTypeNext = s.regs.BTypeNext := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_BTypeNext, spe_BTypeNext, address_regs]
    rfl
  · rw [finish_BTypeNext, address_regs]
    rfl

theorem finish_PSTATE (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.PSTATE = s.regs.PSTATE := rfl

theorem branch_PSTATE (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.PSTATE = s.regs.PSTATE := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_PSTATE, spe_PSTATE, address_regs]
    rfl
  · rw [finish_PSTATE, address_regs]
    rfl

theorem finish_gpr (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.gpr = s.regs.gpr := rfl

theorem branch_gpr (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.gpr = s.regs.gpr := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_gpr, spe_gpr, address_regs]
    rfl
  · rw [finish_gpr, address_regs]
    rfl

theorem finish_FPCR (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.FPCR = s.regs.FPCR := rfl

theorem branch_FPCR (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.FPCR = s.regs.FPCR := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_FPCR, spe_FPCR, address_regs]
    rfl
  · rw [finish_FPCR, address_regs]
    rfl

theorem finish_FPSR (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.FPSR = s.regs.FPSR := rfl

theorem branch_FPSR (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.FPSR = s.regs.FPSR := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_FPSR, spe_FPSR, address_regs]
    rfl
  · rw [finish_FPSR, address_regs]
    rfl

theorem finish__Z (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs._Z = s.regs._Z := rfl

theorem branch__Z (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs._Z = s.regs._Z := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish__Z, spe__Z, address_regs]
    rfl
  · rw [finish__Z, address_regs]
    rfl

theorem finish_SP_EL0 (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.SP_EL0 = s.regs.SP_EL0 := rfl

theorem branch_SP_EL0 (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.SP_EL0 = s.regs.SP_EL0 := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_SP_EL0, spe_SP_EL0, address_regs]
    rfl
  · rw [finish_SP_EL0, address_regs]
    rfl

theorem branch_mem (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).mem = s.mem := by
  simp only [branchState, profileState, finishState, state_mem_ite,
    spe_mem, address_mem, hintState, ite_self]

theorem branch_events (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).events = s.events := by
  simp only [branchState, profileState, finishState, state_events_ite,
    spe_events, address_events, hintState, ite_self]

theorem branch_tags (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).tags = s.tags := by
  simp only [branchState, profileState, finishState, state_tags_ite,
    spe_tags, address_tags, hintState, ite_self]

theorem branch_cycleCount (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).cycleCount = s.cycleCount := by
  simp only [branchState, profileState, finishState, state_cycleCount_ite,
    spe_cycleCount, address_cycleCount, hintState, ite_self]

theorem branch_sailOutput (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).sailOutput = s.sailOutput := by
  simp only [branchState, profileState, finishState, state_sailOutput_ite,
    spe_sailOutput, address_sailOutput, hintState, ite_self]

theorem branch_choiceState (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).choiceState = s.choiceState := by
  simp only [branchState, profileState, finishState, state_choiceState_ite,
    spe_choiceState, address_choiceState, hintState, ite_self]

theorem branch_taken (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.__BranchTaken = true := rfl

theorem branch_pc (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs._PC = addressValue target (hintState branch s) := rfl

theorem branch_type (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.Branchtypetaken = branch := by
  unfold branchState profileState
  dsimp only []
  split
  · have finish_type (pc : BitVec 64) (u : NativeState) :
        (finishState pc u).regs.Branchtypetaken = u.regs.Branchtypetaken := rfl
    rw [finish_type, spe_Branchtypetaken, address_regs]
    rfl
  · have finish_type (pc : BitVec 64) (u : NativeState) :
        (finishState pc u).regs.Branchtypetaken = u.regs.Branchtypetaken := rfl
    rw [finish_type, address_regs]
    rfl


#print axioms branch_run
#print axioms finish_controls
#print axioms branch_controls
#print axioms finish_BTypeNext
#print axioms branch_BTypeNext
#print axioms finish_PSTATE
#print axioms branch_PSTATE
#print axioms finish_gpr
#print axioms branch_gpr
#print axioms finish_FPCR
#print axioms branch_FPCR
#print axioms finish_FPSR
#print axioms branch_FPSR
#print axioms finish__Z
#print axioms branch__Z
#print axioms finish_SP_EL0
#print axioms branch_SP_EL0
#print axioms branch_mem
#print axioms branch_events
#print axioms branch_tags
#print axioms branch_cycleCount
#print axioms branch_sailOutput
#print axioms branch_choiceState
#print axioms branch_taken
#print axioms branch_pc
#print axioms branch_type
end NativeEntryCallerParts
