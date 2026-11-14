-- GEN (gen/tails.py; d200, split 3ac5): runtime14 CbzNot as TranslateStepV.BranchX.BranchTailNZ.
-- RetNZ.tail_nz composition with the action NativeR14B.cbz32_run_not_taken and the GEN dispatch NativeEntryBodyDispatch.Cbz32.
import Bridge.CruxGenGuarded.EntryBodyRet
import TranslateStepV.BranchX
import NativeR14B.Cbz
import NativeEntryBodyDispatch.Cbz32
import TranslateStepV.BranchXZ
import NativeR14Ret.ActZ

namespace NativeR14Ret.TailZ.CbzNot
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenBr Crypto.BcondCore
open ArmBridge.CruxGenGuarded.EntryBodyRet
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

abbrev W (Rt : BitVec 5) (imm19 : BitVec 19) : BitVec 32 := NativeEntryBodyDispatch.Cbz32.selected Rt imm19
abbrev A (Rt : BitVec 5) (imm19 : BitVec 19) : SailM Unit := decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 0#1

theorem tail_z (real : Type) [Sail.SailReal real] (source : NativeState) (Rt : BitVec 5) (imm19 : BitVec 19) (hrt : Rt.toNat < 31)
    (hc : ¬ NativeR14B.cbz32Cond Rt source)
    (noEret : (Sail.BitVec.extractLsb (W Rt imm19) 31 12 == 879088#20) = false) (next : BitVec 64) :
    TranslateStepV.BranchX.BranchTailNZZ real (W Rt imm19) 118 source next := by
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
  have bpT := EntryBranchPins.branch_pins_action source fetched sp (W Rt imm19) 118 input metadataInput
    post.frame pinsT bp
  have hcT : ¬ NativeR14B.cbz32Cond Rt (actionState (W Rt imm19) sp 118) := by
    unfold NativeR14B.cbz32Cond at hc ⊢
    rw [← metadataInput.gpr]; exact hc
  obtain ⟨a, action, actFrame, memRun, _eventsRun, hregs, _npRun⟩ := NativeR14B.cbz32_run_not_taken Rt imm19 (actionState (W Rt imm19) sp 118) bpT hrt hcT
  have btnRun : a.regs.BTypeNext = (actionState (W Rt imm19) sp 118).regs.BTypeNext := by rw [hregs]
  have physRun : a.regs.PhysicalCount = (actionState (W Rt imm19) sp 118).regs.PhysicalCount := by rw [hregs]
  have bttA : a.regs.Branchtypetaken ≠ BranchType.BranchType_RESET := by rw [hregs]; exact metaPins.btt
  have gprA : a.regs.gpr = (actionState (W Rt imm19) sp 118).regs.gpr := by rw [hregs]
  have spA : a.regs.SP_EL0 = (actionState (W Rt imm19) sp 118).regs.SP_EL0 := by rw [hregs]
  have psA : a.regs.PSTATE = (actionState (W Rt imm19) sp 118).regs.PSTATE := by rw [hregs]
  have zA : a.regs._Z = (actionState (W Rt imm19) sp 118).regs._Z := by rw [hregs]
  have dispatch : DispatchAt real (W Rt imm19) (A Rt imm19) 118 := by
    intro pc t see
    exact NativeEntryBodyDispatch.Cbz32.dispatch_at real pc Rt imm19 t (by simpa using see)
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
  have nextB : a.regs.BTypeNext = 0#2 := btnRun.trans btnT
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
  obtain ⟨fin, tail, _finalQuiet, _finalPins, _sys, _branch, output, _events, _gic, _, _pc, _nonProj⟩ :=
    guarded_after_action_entry real source (W Rt imm19) enc0 a budget aQuiet actionPins nextB enc eret
      actionIT actionSS
  have ps := (PMUFrame.of_E20 post.frame).pstate
  refine ⟨sp, fin, hook, prefixEq.trans tail, ?_, ?_, ?_, ?_, ?_, ?_,
    output.mem.trans (memRun.trans ((actionState_mem _ sp 118).trans post.mem)), ?_⟩
  · rw [output.gpr, gprA]
    show sp.regs.gpr = _
    exact frame_pres_E20 (fun x => x.gpr) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  · rw [output.sp, spA]
    show sp.regs.SP_EL0 = _
    exact frame_pres_E20 (fun x => x.SP_EL0) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  · rw [output.n, congrArg ProcState.N psA]; show sp.regs.PSTATE.N = _; rw [ps]
  · rw [output.zf, congrArg ProcState.Z psA]; show sp.regs.PSTATE.Z = _; rw [ps]
  · rw [output.c, congrArg ProcState.C psA]; show sp.regs.PSTATE.C = _; rw [ps]
  · rw [output.v, congrArg ProcState.V psA]; show sp.regs.PSTATE.V = _; rw [ps]
  · rw [output.z, zA]
    show sp.regs._Z = _
    exact frame_pres_E20 (fun x => x._Z) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame

#print axioms tail_z
end NativeR14Ret.TailZ.CbzNot
