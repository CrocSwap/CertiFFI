-- GEN (gen/tails_p.py; r14 CT): runtime14 TbnzTaken as NativeR14Ret.Pc.BranchTailP (landing PC).
-- RetNZ.tail_nz composition with the action NativeR14B.tbnz_run_taken and the GEN dispatch NativeEntryBodyDispatch.Tbnz32.
import Bridge.CruxGenGuarded.EntryBodyRet
import TranslateStepV.BranchX
import NativeR14B.Run
import NativeEntryBodyDispatch.Tbnz32
import TranslateStepV.BranchXE
import NativeR14Ret.PcX
import NativeR14Ret.ActZ

namespace NativeR14Ret.TailP.TbnzTaken
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenBr Crypto.BcondCore
open ArmBridge.CruxGenGuarded.EntryBodyRet
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

abbrev W (Rt : BitVec 5) (imm14 : BitVec 14) : BitVec 32 := NativeEntryBodyDispatch.Tbnz32.selected Rt imm14
abbrev A (Rt : BitVec 5) (imm14 : BitVec 14) : SailM Unit := decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 0#5 1#1 0#1

theorem tail_p (real : Type) [Sail.SailReal real] (source : NativeState) (Rt : BitVec 5) (imm14 : BitVec 14) (hrt : Rt.toNat < 31)
    (hc : NativeR14B.tbnzBit Rt source = 1#1)
    (hlow : (NativeR14B.tbnzTarget imm14 source).toNat < 2 ^ 55)
    (noEret : (Sail.BitVec.extractLsb (W Rt imm14) 31 12 == 879088#20) = false) :
    NativeR14Ret.Pc.BranchTailP real (W Rt imm14) 1009 source (NativeR14B.tbnzTarget imm14 source) := by
  intro fetched enc0 budget pins bp input guard quiet it ss
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (W Rt imm14) 1009
  have metadataQuiet := actionState_quiet (W Rt imm14) sp 1009 (budget + 1) post.quiet
  have metaPins := entryPins_at_metadata sp (W Rt imm14) 1009
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have btypeT : (actionState (W Rt imm14) sp 1009).regs.PSTATE.BTYPE = 0#2 := by
    show sp.regs.PSTATE.BTYPE = 0#2
    rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have btnT : (actionState (W Rt imm14) sp 1009).regs.BTypeNext = 0#2 := by
    show sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have pinsT : StepPins (actionState (W Rt imm14) sp 1009) := scalar_pins _ metaPins btypeT btnT
  have bpT := EntryBranchPins.branch_pins_action source fetched sp (W Rt imm14) 1009 input metadataInput
    post.frame pinsT bp
  have hcT : NativeR14B.tbnzBit Rt (actionState (W Rt imm14) sp 1009) = 1#1 := by
    unfold NativeR14B.tbnzBit at hc ⊢
    rw [← metadataInput.gpr]; exact hc
  have hlowT : (NativeR14B.tbnzTarget imm14 (actionState (W Rt imm14) sp 1009)).toNat < 2 ^ 55 := by
    unfold NativeR14B.tbnzTarget at hlow ⊢
    rw [metadataInput.pc]; exact hlow
  obtain ⟨a, action, actFrame, memRun, _eventsRun, btnRun, pcRun, btRun, physRun, _npRun, _gicRun, bttA,
      gprA, spA, psA⟩ := NativeR14B.tbnz_run_taken Rt imm14 (actionState (W Rt imm14) sp 1009) bpT hrt hcT hlowT
  have zA : a.regs._Z = (actionState (W Rt imm14) sp 1009).regs._Z := NativeR14Ret.Z.tbnz_taken_z Rt imm14 (actionState (W Rt imm14) sp 1009) a bpT hrt hcT hlowT action
  have dispatch : DispatchAt real (W Rt imm14) (A Rt imm14) 1009 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Tbnz32.dispatch_at real pc Rt imm14 t (by simpa using see)
  have boundary := metadata_boundary_at real source (W Rt imm14) (A Rt imm14) enc0 sp currentGuard 1009
    (by decide) dispatch
  have prefixEq : nativeTail real source (W Rt imm14) enc0 fetched =
      nativeAfterAction real source (W Rt imm14) enc0 a := by
    calc
      nativeTail real source (W Rt imm14) enc0 fetched =
          afterSpecPmu real source (W Rt imm14) enc0 sp :=
        spec_pmu_boundary real source (W Rt imm14) enc0 fetched sp hook
      _ = nativeAtAction real source (W Rt imm14) (A Rt imm14) enc0 (actionState (W Rt imm14) sp 1009) := boundary
      _ = nativeAfterAction real source (W Rt imm14) enc0 a :=
        action_boundary real source (W Rt imm14) (A Rt imm14) enc0 (actionState (W Rt imm14) sp 1009) a action
  have actionPinsStep : StepPins a :=
    actbr_pins (actionState (W Rt imm14) sp 1009) a pinsT actFrame bttA
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
  have fields : GuardFieldsEq (actionState (W Rt imm14) sp 1009) a :=
    ⟨actFrame.feat, by simpa using congrArg ProcState.EL actFrame.pse,
     by simpa using congrArg ProcState.nRW actFrame.pse, actFrame.bbool _ (by decide),
     congrFun actFrame.bint _, congrFun actFrame.b32 _, physRun, fun k _ => congrFun actFrame.b64 k⟩
  have aQuiet : HookQuiet (budget + 1) a := quiet_of_fields (budget + 1) _ a metadataQuiet fields
  obtain ⟨fin, tail, _finalQuiet, _finalPins, _sys, _branch, _output, _evF, _gic, _, pcF, _nonProj⟩ :=
    guarded_after_action_entry real source (W Rt imm14) enc0 a budget aQuiet actionPins nextB enc eret
      actionIT actionSS
  refine ⟨sp, fin, hook, prefixEq.trans tail, ?_⟩
  have hbt : a.regs.__BranchTaken = true := btRun
  rw [pcF, hbt, if_pos (rfl : true = true), pcRun]
  unfold NativeR14B.tbnzTarget
  rw [metadataInput.pc]

#print axioms tail_p
end NativeR14Ret.TailP.TbnzTaken
