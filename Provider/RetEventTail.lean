-- Actual RET and its fetched epilogue under the current branch pins.
import Bridge.CruxGenGuarded.EntryBodyRet
import BranchEvent

namespace ReleaseProfile.RuntimeBranch.RichRet
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.BcondCore
open ArmBridge.CruxGenGuarded.EntryBodyRet
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

#check "CURRENT_DECL Ret.tail_at"
theorem tail_at (real : Type) [Sail.SailReal real] (source : NativeState) (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (W Rn) 31 12 == 879088#20) = false)
    (hlow : (source.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55) (next : BitVec 64)
    (hnext : source.regs.gpr[(GPRSummary.key Rn.toNat).val] = next) :
    ReleaseProfile.BranchEvent.BranchTailEvent real (W Rn) 94 source next := by
  intro fetched enc0 budget pins bp input guard quiet it ss
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (W Rn) 94
  have metadataQuiet := actionState_quiet (W Rn) sp 94 (budget + 1) post.quiet
  have metaPins := entryPins_at_metadata sp (W Rn) 94
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have btypeT : (actionState (W Rn) sp 94).regs.PSTATE.BTYPE = 0#2 := by
    show sp.regs.PSTATE.BTYPE = 0#2
    rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have btnT : (actionState (W Rn) sp 94).regs.BTypeNext = 0#2 := by
    show sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have pinsT : StepPins (actionState (W Rn) sp 94) := scalar_pins _ metaPins btypeT btnT
  have bpT := TranslateSpan.BranchMTE2.pins_step fetched (actionState (W Rn) sp 94) bp
    (sysEq2_trans _ _ _ input.sys (EntryBranchPins.sysEq2_symm _ _ metadataInput.sys)) pinsT
    (EntryBranchPins.brSysEq_trans _ _ _ (EntryBranchPins.brSysEq_e20 _ _ post.frame)
      (EntryBranchPins.brSysEq_action (W Rn) sp 94))
  have hlowT : ((actionState (W Rn) sp 94).regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55 := by
    rw [← metadataInput.gpr]; exact hlow
  obtain ⟨a, action, actFrame, memRun, _eventsRun, btnRun, _pcRun, _btRun, physRun, _npRun, gicRun, bttA,gprA,spA,psA⟩ :=
    TranslateSpan.BranchMTE2.run Rn hRn (actionState (W Rn) sp 94) bpT btnT hlowT
  have dispatch : DispatchAt real (W Rn) (A Rn) 94 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Ret.dispatch_at real pc Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (W Rn) (A Rn) enc0 sp currentGuard 94
    (by decide) dispatch
  have prefixEq : nativeTail real source (W Rn) enc0 fetched =
      nativeAfterAction real source (W Rn) enc0 a := by
    calc
      nativeTail real source (W Rn) enc0 fetched =
          afterSpecPmu real source (W Rn) enc0 sp :=
        spec_pmu_boundary real source (W Rn) enc0 fetched sp hook
      _ = nativeAtAction real source (W Rn) (A Rn) enc0 (actionState (W Rn) sp 94) := boundary
      _ = nativeAfterAction real source (W Rn) enc0 a :=
        action_boundary real source (W Rn) (A Rn) enc0 (actionState (W Rn) sp 94) a action
  have actionPinsStep : StepPins a :=
    actbr_pins (actionState (W Rn) sp 94) a pinsT actFrame bttA
  have actionPins := NativeEntryTail.EntryPins.of_scalar a actionPinsStep
  have nextB : a.regs.BTypeNext = 0#2 := btnRun.trans btnT
  have enc : a.regs.__ThisInstrEnc = .__A64 := actFrame.enc.trans (by rfl)
  have eret : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [actFrame.b32]
    simpa (disch := decide) only [actionState, RegMap.set_ne, RegMap.set_same] using noEret
  have actionIT : a.regs.ShouldAdvanceIT = false :=
    actFrame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : a.regs.ShouldAdvanceSS = true :=
    actFrame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  have fields : GuardFieldsEq (actionState (W Rn) sp 94) a :=
    ⟨actFrame.feat, by simpa using congrArg ProcState.EL actFrame.pse,
     by simpa using congrArg ProcState.nRW actFrame.pse, actFrame.bbool _ (by decide),
     congrFun actFrame.bint _, congrFun actFrame.b32 _, physRun, fun k _ => congrFun actFrame.b64 k⟩
  have aQuiet : HookQuiet (budget + 1) a := quiet_of_fields (budget + 1) _ a metadataQuiet fields
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, branch, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source (W Rn) enc0 a budget aQuiet actionPins nextB enc eret
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
  have pcF : fin.regs._PC = next := by
    rw [pc, _btRun, NativeEntryBodyBranch.Decide.ret_fBT_eq, if_pos rfl, _pcRun,
      NativeEntryBodyBranch.Decide.ret_fPC_eq, ← metadataInput.gpr, hnext]
  have vz : fin.regs._Z = fetched.regs._Z := by
    rw [output.z]
    have zAction := congrArg (fun r : Regs => r._Z) _npRun
    change a.regs._Z = fetched.regs._Z
    rw [show a.regs._Z = sp.regs._Z from zAction]
    exact frame_pres_E20 (fun r => r._Z)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  exact ⟨sp, a, fin, hook, prefixEq.trans tail, actFrame, finalQuiet, finalPins, sys, branch,
    output.mem.trans (memRun.trans ((actionState_mem _ sp 94).trans post.mem)), gicF, pcF, nonProj, gprF, spF,
    (output.n.trans (congrArg ProcState.N psA)).trans (congrArg ProcState.N ps),
    (output.zf.trans (congrArg ProcState.Z psA)).trans (congrArg ProcState.Z ps),
    (output.c.trans (congrArg ProcState.C psA)).trans (congrArg ProcState.C ps),
    (output.v.trans (congrArg ProcState.V psA)).trans (congrArg ProcState.V ps),
    vz, events.trans (_eventsRun.trans ((actionState_events _ sp 94).trans post.events))⟩

#print axioms tail_at
end ReleaseProfile.RuntimeBranch.RichRet
