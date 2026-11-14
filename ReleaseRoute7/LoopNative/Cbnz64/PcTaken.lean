-- GEN (gen/tails_p.py; r14 CT): runtime14 CbzTaken as NativeR14Ret.Pc.BranchTailP (landing PC).
-- RetNZ.tail_nz composition with the action LoopNative.Cbnz64.run_taken and the GEN dispatch LoopNative.Cbnz64.Dispatch.
import Bridge.CruxGenGuarded.EntryBodyRet
import TranslateStepV.BranchX
import LoopNative.Cbnz64.Action
import LoopNative.Cbnz64.Dispatch
import NativeR14Ret.PcX

namespace LoopNative.Cbnz64.PcTaken
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenBr Crypto.BcondCore
open ArmBridge.CruxGenGuarded.EntryBodyRet
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

abbrev W (Rt : BitVec 5) (imm19 : BitVec 19) : BitVec 32 := LoopNative.Cbnz64.Dispatch.selected Rt imm19
abbrev A (Rt : BitVec 5) (imm19 : BitVec 19) : SailM Unit := decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 1#1 1#1

theorem tail_p (real : Type) [Sail.SailReal real] (source : NativeState) (Rt : BitVec 5) (imm19 : BitVec 19) (hrt : Rt.toNat < 31)
    (hc : LoopNative.Cbnz64.condition Rt source)
    (hlow : (LoopNative.Cbnz64.target imm19 source).toNat < 2 ^ 55)
    (noEret : (Sail.BitVec.extractLsb (W Rt imm19) 31 12 == 879088#20) = false) :
    NativeR14Ret.Pc.BranchTailP real (W Rt imm19) 117 source (LoopNative.Cbnz64.target imm19 source) := by
  intro fetched enc0 budget pins bp input guard quiet it ss
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (W Rt imm19) 117
  have metadataQuiet := actionState_quiet (W Rt imm19) sp 117 (budget + 1) post.quiet
  have metaPins := entryPins_at_metadata sp (W Rt imm19) 117
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have btypeT : (actionState (W Rt imm19) sp 117).regs.PSTATE.BTYPE = 0#2 := by
    show sp.regs.PSTATE.BTYPE = 0#2
    rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have btnT : (actionState (W Rt imm19) sp 117).regs.BTypeNext = 0#2 := by
    show sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have pinsT : StepPins (actionState (W Rt imm19) sp 117) := scalar_pins _ metaPins btypeT btnT
  have bpT := EntryBranchPins.branch_pins_action source fetched sp (W Rt imm19) 117 input metadataInput
    post.frame pinsT bp
  have hcT : LoopNative.Cbnz64.condition Rt (actionState (W Rt imm19) sp 117) := by
    unfold LoopNative.Cbnz64.condition at hc ⊢
    rw [← metadataInput.gpr]; exact hc
  have hlowT : (LoopNative.Cbnz64.target imm19 (actionState (W Rt imm19) sp 117)).toNat < 2 ^ 55 := by
    unfold LoopNative.Cbnz64.target at hlow ⊢
    rw [metadataInput.pc]; exact hlow
  obtain ⟨a, action, actFrame, memRun, _eventsRun, btnRun, pcRun, btRun, physRun, _npRun, _gicRun, bttA,
      gprA, spA, psA⟩ := LoopNative.Cbnz64.run_taken Rt imm19 (actionState (W Rt imm19) sp 117) bpT hrt hcT hlowT
  have zA : a.regs._Z = (actionState (W Rt imm19) sp 117).regs._Z := LoopNative.Cbnz64.taken_z Rt imm19 (actionState (W Rt imm19) sp 117) a bpT hrt hcT hlowT action
  have dispatch : DispatchAt real (W Rt imm19) (A Rt imm19) 117 := by
    intro pc t see
    exact LoopNative.Cbnz64.Dispatch.dispatch_at real pc Rt imm19 t (by simpa using see)
  have boundary := metadata_boundary_at real source (W Rt imm19) (A Rt imm19) enc0 sp currentGuard 117
    (by decide) dispatch
  have prefixEq : nativeTail real source (W Rt imm19) enc0 fetched =
      nativeAfterAction real source (W Rt imm19) enc0 a := by
    calc
      nativeTail real source (W Rt imm19) enc0 fetched =
          afterSpecPmu real source (W Rt imm19) enc0 sp :=
        spec_pmu_boundary real source (W Rt imm19) enc0 fetched sp hook
      _ = nativeAtAction real source (W Rt imm19) (A Rt imm19) enc0 (actionState (W Rt imm19) sp 117) := boundary
      _ = nativeAfterAction real source (W Rt imm19) enc0 a :=
        action_boundary real source (W Rt imm19) (A Rt imm19) enc0 (actionState (W Rt imm19) sp 117) a action
  have actionPinsStep : StepPins a :=
    actbr_pins (actionState (W Rt imm19) sp 117) a pinsT actFrame bttA
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
  have fields : GuardFieldsEq (actionState (W Rt imm19) sp 117) a :=
    ⟨actFrame.feat, by simpa using congrArg ProcState.EL actFrame.pse,
     by simpa using congrArg ProcState.nRW actFrame.pse, actFrame.bbool _ (by decide),
     congrFun actFrame.bint _, congrFun actFrame.b32 _, physRun, fun k _ => congrFun actFrame.b64 k⟩
  have aQuiet : HookQuiet (budget + 1) a := quiet_of_fields (budget + 1) _ a metadataQuiet fields
  obtain ⟨fin, tail, _finalQuiet, _finalPins, _sys, _branch, _output, _evF, _gic, _, pcF, _nonProj⟩ :=
    guarded_after_action_entry real source (W Rt imm19) enc0 a budget aQuiet actionPins nextB enc eret
      actionIT actionSS
  refine ⟨sp, fin, hook, prefixEq.trans tail, ?_⟩
  have hbt : a.regs.__BranchTaken = true := btRun
  rw [pcF, hbt, if_pos (rfl : true = true), pcRun]
  unfold LoopNative.Cbnz64.target
  rw [metadataInput.pc]

#print axioms tail_p
end LoopNative.Cbnz64.PcTaken
