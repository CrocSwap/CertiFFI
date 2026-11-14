-- (r14 CT): NativeR14Ret.TailZ.Ret (RetNZ.tail_nz + _Z) as BranchTailNZZE: plus fin.events = fetched.events
-- (CongOut events, the RET run, actionState_events, the spec-PMU post). 
import Bridge.CruxGenGuarded.EntryBodyRet
import HeapV2StepCerts.BranchFrame
import TranslateStepV.BranchX
import RtBr.RetDecode
import TranslateStepV.BranchXE
import NativeR14Ret.ActZ

namespace NativeR14Ret.TailE.Ret
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.BcondCore
open ArmBridge.CruxGenGuarded.EntryBodyRet
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

theorem tail_e (real : Type) [Sail.SailReal real] (source : NativeState) (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (W Rn) 31 12 == 879088#20) = false)
    (hlow : (source.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55) (next : BitVec 64) :
    TranslateStepV.BranchX.BranchTailNZZE real (W Rn) 94 source next := by
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
  have bpT := EntryBranchPins.branch_pins_action source fetched sp (W Rn) 94 input metadataInput
    post.frame pinsT bp
  have hlowT : ((actionState (W Rn) sp 94).regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55 := by
    rw [← metadataInput.gpr]; exact hlow
  obtain ⟨a, action, actFrame, memRun, eventsRun, btnRun, _pcRun, _btRun, physRun, _npRun, _gicRun, bttA⟩ :=
    NativeEntryBodyBranch.Ret.run Rn hRn (actionState (W Rn) sp 94) bpT btnT hlowT
  have zA : a.regs._Z = (actionState (W Rn) sp 94).regs._Z := NativeR14Ret.Z.ret_z Rn hRn _ a bpT btnT hlowT action
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
  have next : a.regs.BTypeNext = 0#2 := btnRun.trans btnT
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
  obtain ⟨fin, tail, _finalQuiet, _finalPins, _sys, _branch, output, evF, _gic, _, _pc, _nonProj⟩ :=
    guarded_after_action_entry real source (W Rn) enc0 a budget aQuiet actionPins next enc eret
      actionIT actionSS
  have bf := Crypto.CruxRet.ret_regs real (actionState (W Rn) sp 94) a Rn hRn action bpT hlowT btnT
  have nzA := RtBr.RetDecode.decode_nzcv Rn hRn _ a bpT.base bpT.vhe bpT.gcs hlowT action
  have ps := (PMUFrame.of_E20 post.frame).pstate
  refine ⟨sp, fin, hook, prefixEq.trans tail, ?_, ?_, ?_, ?_, ?_, ?_,
    output.mem.trans (memRun.trans ((actionState_mem _ sp 94).trans post.mem)), ?_, ?_⟩
  · rw [output.gpr, bf.1]
    show sp.regs.gpr = _
    exact frame_pres_E20 (fun x => x.gpr) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  · rw [output.sp, bf.2]
    show sp.regs.SP_EL0 = _
    exact frame_pres_E20 (fun x => x.SP_EL0) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  · rw [output.n, nzA.1]; show sp.regs.PSTATE.N = _; rw [ps]
  · rw [output.zf, nzA.2.1]; show sp.regs.PSTATE.Z = _; rw [ps]
  · rw [output.c, nzA.2.2.1]; show sp.regs.PSTATE.C = _; rw [ps]
  · rw [output.v, nzA.2.2.2]; show sp.regs.PSTATE.V = _; rw [ps]
  · rw [output.z, zA]
    show sp.regs._Z = _
    exact frame_pres_E20 (fun x => x._Z) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  · exact evF.trans (eventsRun.trans ((actionState_events _ sp 94).trans post.events))

#print axioms tail_e
end NativeR14Ret.TailE.Ret
