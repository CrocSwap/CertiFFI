-- Current-profile fetched CBZ X with its exact event and register frames.
import Bridge.CruxGenGuarded.EntryBodyCbz
import HeapCbzAction
import BranchEvent

namespace ReleaseProfile.HeapCbzTail
open ArmBridge.CruxGenGuarded.EntryBodyCbz
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.CbzDec Crypto.BcondCore
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000
attribute [local instance 10] Classical.propDecidable

#check "CURRENT_DECL CBZ X tail_at"
theorem tail_at (real : Type) [Sail.SailReal real] (source : NativeState) (Rt : BitVec 5) (imm19 : BitVec 19)
    (noEret : (Sail.BitVec.extractLsb (W Rt imm19) 31 12 == 879088#20) = false)
    (hlow : (source.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (nextPC : BitVec 64)
    (hnext : (if Crypto.CruxCbz.cbzC 1#1 Rt source then
      source.regs._PC + sign_extend (imm19 ++ 0#2) 64 else source.regs._PC + 4#64) = nextPC) :
    ReleaseProfile.BranchEvent.BranchTailEvent real (W Rt imm19) 118 source nextPC := by
  intro fetched enc0 budget pins bp input guard quiet it ss
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (W Rt imm19) 118
  have metadataQuiet := actionState_quiet (W Rt imm19) sp 118 (budget + 1) post.quiet
  have metaPins := entryPins_at_metadata sp (W Rt imm19) 118
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have btypeT : (actionState (W Rt imm19) sp 118).regs.PSTATE.BTYPE = 0#2 := by
    show sp.regs.PSTATE.BTYPE = 0#2
    rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have btnT : (actionState (W Rt imm19) sp 118).regs.BTypeNext = 0#2 := by
    show sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have pinsT : StepPins (actionState (W Rt imm19) sp 118) := scalar_pins _ metaPins btypeT btnT
  have bpT := TranslateSpan.BranchMTE2.pins_step fetched (actionState (W Rt imm19) sp 118) bp
    (sysEq2_trans _ _ _ input.sys (EntryBranchPins.sysEq2_symm _ _ metadataInput.sys)) pinsT
    (EntryBranchPins.brSysEq_trans _ _ _ (EntryBranchPins.brSysEq_e20 _ _ post.frame)
      (EntryBranchPins.brSysEq_action (W Rt imm19) sp 118))
  have hlowT : ((actionState (W Rt imm19) sp 118).regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [metadataInput.pc]; exact hlow
  obtain ⟨a, action, actFrame, memRun, eventsRun, btnRun, pcRun, btRun, physRun, npRun, gicRun, bttA, gprA, spA, psA⟩ :=
    ReleaseProfile.HeapCbzAction.run real imm19 Rt (actionState (W Rt imm19) sp 118) bpT.base bpT.vhe hlowT metaPins.btt
  have dispatch : DispatchAt real (W Rt imm19) (A Rt imm19) 118 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Cbz.dispatch_at real pc Rt imm19 t (by simpa using see)
  have boundary := metadata_boundary_at real source (W Rt imm19) (A Rt imm19) enc0 sp currentGuard 118
    (by decide) dispatch
  have prefixEq : nativeTail real source (W Rt imm19) enc0 fetched =
      nativeAfterAction real source (W Rt imm19) enc0 a := by
    calc
      nativeTail real source (W Rt imm19) enc0 fetched =
          afterSpecPmu real source (W Rt imm19) enc0 sp :=
        spec_pmu_boundary real source (W Rt imm19) enc0 fetched sp hook
      _ = nativeAtAction real source (W Rt imm19) (A Rt imm19) enc0 (actionState (W Rt imm19) sp 118) := boundary
      _ = nativeAfterAction real source (W Rt imm19) enc0 a :=
        action_boundary real source (W Rt imm19) (A Rt imm19) enc0 (actionState (W Rt imm19) sp 118) a action
  have actionPinsStep : StepPins a :=
    actbr_pins (actionState (W Rt imm19) sp 118) a pinsT actFrame bttA
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
  have fields : GuardFieldsEq (actionState (W Rt imm19) sp 118) a :=
    ⟨actFrame.feat, by simpa using congrArg ProcState.EL actFrame.pse,
     by simpa using congrArg ProcState.nRW actFrame.pse, actFrame.bbool _ (by decide),
     congrFun actFrame.bint _, congrFun actFrame.b32 _, physRun, fun k _ => congrFun actFrame.b64 k⟩
  have aQuiet : HookQuiet (budget + 1) a := quiet_of_fields (budget + 1) _ a metadataQuiet fields
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, branch, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source (W Rt imm19) enc0 a budget aQuiet actionPins next enc eret
      actionIT actionSS
  have actionPC : (actionState (W Rt imm19) sp 118).regs._PC = source.regs._PC := metadataInput.pc
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
    have hbtT : (actionState (W Rt imm19) sp 118).regs.__BranchTaken = false := by
      simp only [actionState] <;> (split <;> rfl)
    have agreeT : Crypto.CruxCbz.cbzC 1#1 Rt (actionState (W Rt imm19) sp 118) ↔ Crypto.CruxCbz.cbzC 1#1 Rt source := by
      unfold Crypto.CruxCbz.cbzC; rw [← metadataInput.gpr]
    rw [pc, pcRun, btRun, NativeEntryBodyBranch.Decide.cbz_fBT_eq imm19 Rt _ hbtT, NativeEntryBodyBranch.Decide.cbz_fPC_eq imm19 Rt, actionPC]
    by_cases hc : Crypto.CruxCbz.cbzC 1#1 Rt source
    · simp [agreeT.mpr hc, hc]
    · have hT : ¬ Crypto.CruxCbz.cbzC 1#1 Rt (actionState (W Rt imm19) sp 118) := fun h => hc (agreeT.mp h)
      simp [hT, hc]
  have ps := (PMUFrame.of_E20 post.frame).pstate
  have z : fin.regs._Z = fetched.regs._Z := by
    rw [output.z]
    have zAction := congrArg (fun r : Regs => r._Z) npRun
    change a.regs._Z = fetched.regs._Z
    rw [show a.regs._Z = sp.regs._Z from zAction]
    exact frame_pres_E20 (fun r => r._Z)
      (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  exact ⟨sp, a, fin, hook, prefixEq.trans tail, actFrame, finalQuiet, finalPins, sys, branch,
    output.mem.trans (memRun.trans ((actionState_mem _ sp 118).trans post.mem)), gicF, pcF, nonProj, gprF, spF,
    (output.n.trans (congrArg ProcState.N psA)).trans (congrArg ProcState.N ps),
    (output.zf.trans (congrArg ProcState.Z psA)).trans (congrArg ProcState.Z ps),
    (output.c.trans (congrArg ProcState.C psA)).trans (congrArg ProcState.C ps),
    (output.v.trans (congrArg ProcState.V psA)).trans (congrArg ProcState.V ps),
    z, events.trans (eventsRun.trans ((actionState_events _ sp 118).trans post.events))⟩

#print axioms tail_at
end ReleaseProfile.HeapCbzTail
