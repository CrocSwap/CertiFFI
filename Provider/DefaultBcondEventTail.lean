-- Actual B.cond fetched action with the signed target/fall-through rule.
import Bridge.CruxGenGuarded.EntryBodyBcond
import DefaultBranchEvent
import DefaultBranchChoice
import BcondAction
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ReleaseProfile.DefaultBcondEventTail
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.BcondDec Crypto.BcondCore
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000
attribute [local instance 10] Classical.propDecidable

abbrev W (cond : BitVec 4) (imm19 : BitVec 19) : BitVec 32 := NativeEntryBodyDispatch.Bcond.selected cond imm19
abbrev A (cond : BitVec 4) (imm19 : BitVec 19) : SailM Unit :=
  decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19

#check "CURRENT_DECL Bcond.tail_at"
theorem tail_at (real : Type) [Sail.SailReal real]
    (source : NativeState) (cond : BitVec 4) (imm19 : BitVec 19)
    (noEret : (Sail.BitVec.extractLsb (W cond imm19) 31 12 == 879088#20) = false)
    (hlow : (source.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (nextPC : BitVec 64)
    (hnext : (if Crypto.BcondCore.bcondC cond source.regs then
      source.regs._PC + sign_extend (imm19 ++ 0#2) 64 else source.regs._PC + 4#64) = nextPC) :
    ReleaseProfile.DefaultBranchEvent.BranchTailEvent real (W cond imm19) 69 source nextPC := by
  intro fetched enc0 budget pins bp input guard quiet it ss
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (W cond imm19) 69
  have metadataQuiet := actionState_quiet (W cond imm19) sp 69 (budget + 1) post.quiet
  have metaPins := entryPins_at_metadata sp (W cond imm19) 69
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have btypeT : (actionState (W cond imm19) sp 69).regs.PSTATE.BTYPE = 0#2 := by
    show sp.regs.PSTATE.BTYPE = 0#2
    rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have btnT : (actionState (W cond imm19) sp 69).regs.BTypeNext = 0#2 := by
    show sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have pinsT : StepPins (actionState (W cond imm19) sp 69) := scalar_pins _ metaPins btypeT btnT
  have bpT := TranslateSpan.BranchMTE2.pins_step fetched (actionState (W cond imm19) sp 69) bp
    (sysEq2_trans _ _ _ input.sys (EntryBranchPins.sysEq2_symm _ _ metadataInput.sys)) pinsT
    (EntryBranchPins.brSysEq_trans _ _ _ (EntryBranchPins.brSysEq_e20 _ _ post.frame)
      (EntryBranchPins.brSysEq_action (W cond imm19) sp 69))
  have hlowT : ((actionState (W cond imm19) sp 69).regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [metadataInput.pc]; exact hlow
  obtain ⟨a, action, actFrame, memRun, _eventsRun, btnRun, pcRun, btRun, physRun, _npRun, gicRun, bttA, gprA, spA, psA⟩ :=
    ReleaseProfile.BcondAction.run real cond imm19 (actionState (W cond imm19) sp 69) bpT.base bpT.vhe hlowT metaPins.btt
  have dispatch : DispatchAt real (W cond imm19) (A cond imm19) 69 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Bcond.dispatch_at real pc cond imm19 t (by simpa using see)
  have boundary := metadata_boundary_at real source (W cond imm19) (A cond imm19) enc0 sp currentGuard 69
    (by decide) dispatch
  have prefixEq : nativeTail real source (W cond imm19) enc0 fetched =
      nativeAfterAction real source (W cond imm19) enc0 a := by
    calc
      nativeTail real source (W cond imm19) enc0 fetched =
          afterSpecPmu real source (W cond imm19) enc0 sp :=
        spec_pmu_boundary real source (W cond imm19) enc0 fetched sp hook
      _ = nativeAtAction real source (W cond imm19) (A cond imm19) enc0 (actionState (W cond imm19) sp 69) := boundary
      _ = nativeAfterAction real source (W cond imm19) enc0 a :=
        action_boundary real source (W cond imm19) (A cond imm19) enc0 (actionState (W cond imm19) sp 69) a action
  have actionPinsStep : StepPins a :=
    actbr_pins (actionState (W cond imm19) sp 69) a pinsT actFrame bttA
  have actionPins := NativeEntryTail.EntryPins.of_scalar a actionPinsStep
  have next : a.regs.BTypeNext = 0#2 := btnRun.trans btnT
  have enc : a.regs.__ThisInstrEnc = .__A64 := actFrame.enc.trans (by rfl)
  have eret : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [actFrame.b32]
    simpa (disch := decide) only [actionState, RegMap.set_ne, RegMap.set_same] using noEret
  have actionIT : a.regs.ShouldAdvanceIT = false :=
    actFrame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : a.regs.ShouldAdvanceSS = true :=
    actFrame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  have fields : GuardFieldsEq (actionState (W cond imm19) sp 69) a :=
    ⟨actFrame.feat, by simpa using congrArg ProcState.EL actFrame.pse,
     by simpa using congrArg ProcState.nRW actFrame.pse, actFrame.bbool _ (by decide),
     congrFun actFrame.bint _, congrFun actFrame.b32 _, physRun, fun k _ => congrFun actFrame.b64 k⟩
  have aQuiet : HookQuiet (budget + 1) a := quiet_of_fields (budget + 1) _ a metadataQuiet fields
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, branch, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source (W cond imm19) enc0 a budget aQuiet actionPins next enc eret
      actionIT actionSS
  have ps := (PMUFrame.of_E20 post.frame).pstate
  have gprF : fin.regs.gpr = fetched.regs.gpr := by
    rw [output.gpr, gprA]
    show sp.regs.gpr = _
    exact frame_pres_E20 (fun x => x.gpr) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  have spF : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := by
    rw [output.sp, spA]
    show sp.regs.SP_EL0 = _
    exact frame_pres_E20 (fun x => x.SP_EL0) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  have gicF : fin.regs.bank_Option_InterruptID .__GIC_Pending = fetched.regs.bank_Option_InterruptID .__GIC_Pending := by
    rw [gic, gicRun]
    show sp.regs.bank_Option_InterruptID .__GIC_Pending = _
    exact post.gic
  have pcF : fin.regs._PC = nextPC := by
    rw [← hnext]
    have hbtT : (actionState (W cond imm19) sp 69).regs.__BranchTaken = false := by
      simp only [actionState] <;> (split <;> rfl)
    have agreeT : Crypto.BcondCore.bcondC cond (actionState (W cond imm19) sp 69).regs ↔ Crypto.BcondCore.bcondC cond source.regs := by
      unfold Crypto.BcondCore.bcondC; rw [← metadataInput.ps]
    have actionPC := metadataInput.pc
    rw [pc, pcRun, btRun, NativeEntryBodyBranch.Decide.bcond_fBT_eq cond imm19 _ hbtT, NativeEntryBodyBranch.Decide.bcond_fPC_eq cond imm19, actionPC]
    by_cases hc : Crypto.BcondCore.bcondC cond source.regs
    · simp [agreeT.mpr hc, hc]
    · have hT : ¬ Crypto.BcondCore.bcondC cond (actionState (W cond imm19) sp 69).regs := fun h => hc (agreeT.mp h)
      simp [hT, hc]

  have vz : fin.regs._Z = fetched.regs._Z := by
    rw [output.z]
    have zAction := congrArg (fun r : Regs => r._Z) _npRun
    change a.regs._Z = fetched.regs._Z
    rw [show a.regs._Z = sp.regs._Z from zAction]
    exact frame_pres_E20 (fun r => r._Z)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  have actionChoice := (DefaultBranchChoice.bcond cond imm19) (actionState (W cond imm19) sp 69) () a action
  have finalChoice := NativeTagCheck.native_tail_choice_of_delta real source fetched sp a fin
    (W cond imm19) enc0 69 budget 0 quiet hook actionChoice prefixEq aQuiet actionPins
    enc eret actionIT actionSS (prefixEq.trans tail)
  exact ⟨sp, a, fin, hook, prefixEq.trans tail, actFrame, finalQuiet, finalPins, sys, branch,
    output.mem.trans (memRun.trans ((actionState_mem _ sp 69).trans post.mem)), gicF, pcF, nonProj, gprF, spF,
    (output.n.trans (congrArg ProcState.N psA)).trans (congrArg ProcState.N ps),
    (output.zf.trans (congrArg ProcState.Z psA)).trans (congrArg ProcState.Z ps),
    (output.c.trans (congrArg ProcState.C psA)).trans (congrArg ProcState.C ps),
    (output.v.trans (congrArg ProcState.V psA)).trans (congrArg ProcState.V ps),
    vz, events.trans (_eventsRun.trans ((actionState_events _ sp 69).trans post.events)), finalChoice⟩

#print axioms tail_at
end ReleaseProfile.DefaultBcondEventTail
