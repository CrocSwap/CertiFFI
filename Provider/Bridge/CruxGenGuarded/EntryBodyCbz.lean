import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import Bridge.CruxGenGuarded.EntryBranchPins
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BranchTransport
import NativeEntryInput.Input
import NativeEntryBodyBranch.Cbz
import NativeEntryBodyBranch.Decide
import NativeEntryBodyDispatch.Cbz
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
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.CruxGenGuarded.EntryBodyCbzLNSym.
namespace ArmBridge.CruxGenGuarded.EntryBodyCbz

attribute [local instance 10] Classical.propDecidable

/-! CBZ X (64b5ceb, INPUT 75faeda1) action + tail on the actual native step from the
post-fetch state. BranchPinsV2 is carried at the fetched state and moved to the
action state (EntryBranchPins). The final PC is the epilogue's
`if BT then PC else PC+4` over the action result, whose PC/BT are the actual spec's;
path decisions resolve them. -/

abbrev W (Rt : BitVec 5) (imm19 : BitVec 19) : BitVec 32 := NativeEntryBodyDispatch.Cbz.selected Rt imm19

abbrev A (Rt : BitVec 5) (imm19 : BitVec 19) : SailM Unit :=
  decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 1#1

run_cmd do
  IO.eprintln "CURRENT_DECL EntryBodyCbz.native_tail"
  (← IO.getStderr).flush

theorem native_tail (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc) (Rt : BitVec 5) (imm19 : BitVec 19)
    (noEret : (Sail.BitVec.extractLsb (W Rt imm19) 31 12 == 879088#20) = false)
    (pins : StepPins fetched) (bp : Crypto.BranchV2.BranchPinsV2PA fetched)
    (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (hlow : (source.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∃ sp a fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source (W Rt imm19) enc0 fetched = .ok () fin ∧
      ActFrameBr (actionState (W Rt imm19) sp 118) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧ BrSysEq a.regs fin.regs ∧
      fin.mem = fetched.mem ∧ fin.events = fetched.events ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = (if a.regs.__BranchTaken then a.regs._PC else a.regs._PC + 4#64) ∧
      a.regs._PC = (Crypto.CruxCbz.spec 1#1 imm19 Rt).fPC (actionState (W Rt imm19) sp 118) ∧
      a.regs.__BranchTaken = (Crypto.CruxCbz.spec 1#1 imm19 Rt).fBT (actionState (W Rt imm19) sp 118) ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs ∧
      Crypto.BranchV2.BranchPinsV2PA (actionState (W Rt imm19) sp 118) ∧
      fin.regs._PC = (if Crypto.CruxCbz.cbzC 1#1 Rt source then source.regs._PC + sign_extend (imm19 ++ 0#2) 64 else source.regs._PC + 4#64) := by
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
  have hlowT : ((actionState (W Rt imm19) sp 118).regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [metadataInput.pc]; exact hlow
  obtain ⟨a, action, actFrame, memRun, eventsRun, btnRun, pcRun, btRun, physRun, npRun, gicRun, bttA⟩ :=
    NativeEntryBodyBranch.Cbz.run real imm19 Rt (actionState (W Rt imm19) sp 118) bpT.base bpT.vhe hlowT metaPins.btt
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
  refine ⟨sp, a, fin, hook, prefixEq.trans tail, actFrame, finalQuiet, finalPins, sys, branch,
    output.mem.trans (memRun.trans ((actionState_mem _ sp 118).trans post.mem)),
    events.trans (eventsRun.trans ((actionState_events _ sp 118).trans post.events)),
    gic, pc, pcRun, btRun, nonProj, bpT, ?_⟩
  have hbtT : (actionState (W Rt imm19) sp 118).regs.__BranchTaken = false := by
    simp only [actionState] <;> (split <;> rfl)
  have agreeT : Crypto.CruxCbz.cbzC 1#1 Rt (actionState (W Rt imm19) sp 118) ↔ Crypto.CruxCbz.cbzC 1#1 Rt source := by
    unfold Crypto.CruxCbz.cbzC; rw [← metadataInput.gpr]
  rw [pc, pcRun, btRun, NativeEntryBodyBranch.Decide.cbz_fBT_eq imm19 Rt _ hbtT, NativeEntryBodyBranch.Decide.cbz_fPC_eq imm19 Rt, actionPC]
  by_cases hc : Crypto.CruxCbz.cbzC 1#1 Rt source
  · simp [agreeT.mpr hc, hc]
  · have hT : ¬ Crypto.CruxCbz.cbzC 1#1 Rt (actionState (W Rt imm19) sp 118) := fun h => hc (agreeT.mp h)
    simp [hT, hc]

end ArmBridge.CruxGenGuarded.EntryBodyCbz

