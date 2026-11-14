-- runtime14 CT: BcondNZ.tail_z plus silent events (fin.events = fetched.events, as in RtB6.BranchTailsZ).
import TranslateStepV.BcondNZZ
import TranslateStepV.BranchXE
import RtB6.BranchFrameZ
namespace TranslateStepV.BcondNZ
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.BcondDec Crypto.BcondCore
open ArmBridge.CruxGenGuarded.EntryBodyBcond
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
attribute [local instance 10] Classical.propDecidable

theorem tail_e (real : Type) [Sail.SailReal real] (source : NativeState) (cond : BitVec 4) (imm19 : BitVec 19)
    (noEret : (Sail.BitVec.extractLsb (W cond imm19) 31 12 == 879088#20) = false)
    (hlow : (source.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (actNZ : ActNZ cond imm19) (next : BitVec 64) :
    TranslateStepV.BranchX.BranchTailNZZE real (W cond imm19) 69 source next := by
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
  have bpT := EntryBranchPins.branch_pins_action source fetched sp (W cond imm19) 69 input metadataInput
    post.frame pinsT bp
  have hlowT : ((actionState (W cond imm19) sp 69).regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [metadataInput.pc]; exact hlow
  obtain ⟨a, action, actFrame, memRun, eventsRun, btnRun, pcRun, btRun, physRun, npRun, gicRun, bttA⟩ :=
    NativeEntryBodyBranch.Bcond.run real cond imm19 (actionState (W cond imm19) sp 69) bpT.base bpT.vhe hlowT metaPins.btt
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
  have actionPC : (actionState (W cond imm19) sp 69).regs._PC = source.regs._PC := metadataInput.pc
  have bf := Crypto.CruxBcond.bcond_regsZ real (actionState (W cond imm19) sp 69) a cond imm19 action bpT hlowT
  have gprF : fin.regs.gpr = fetched.regs.gpr := by
    rw [output.gpr, bf.1]
    show sp.regs.gpr = _
    exact frame_pres_E20 (fun x => x.gpr) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  have spF : fin.regs.SP_EL0 = fetched.regs.SP_EL0 := by
    rw [output.sp, bf.2.1]
    show sp.regs.SP_EL0 = _
    exact frame_pres_E20 (fun x => x.SP_EL0) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  have gicF : fin.regs.bank_Option_InterruptID .__GIC_Pending = fetched.regs.bank_Option_InterruptID .__GIC_Pending := by
    rw [gic, gicRun]
    show sp.regs.bank_Option_InterruptID .__GIC_Pending = _
    exact post.gic
  have zF : fin.regs._Z = fetched.regs._Z := by
    rw [output.z, bf.2.2]
    show sp.regs._Z = _
    exact frame_pres_E20 (fun x => x._Z) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  have nzA := actNZ _ a bpT.base bpT.vhe hlowT action
  have ps := (PMUFrame.of_E20 post.frame).pstate
  refine ⟨sp, fin, hook, prefixEq.trans tail, gprF, spF, ?_, ?_, ?_, ?_,
    output.mem.trans (memRun.trans ((actionState_mem _ sp 69).trans post.mem)), zF,
    events.trans (eventsRun.trans ((actionState_events _ sp 69).trans post.events))⟩
  · rw [output.n, nzA.1]; show sp.regs.PSTATE.N = _; rw [ps]
  · rw [output.zf, nzA.2.1]; show sp.regs.PSTATE.Z = _; rw [ps]
  · rw [output.c, nzA.2.2.1]; show sp.regs.PSTATE.C = _; rw [ps]
  · rw [output.v, nzA.2.2.2]; show sp.regs.PSTATE.V = _; rw [ps]


#print axioms tail_e
end TranslateStepV.BcondNZ
