-- Memory (B1b): FlagTails' AndsImm0_2 action/native tails over FlagRoots.TstF4 (TST #7: N = C = V = 0).
import HeapV2StepCerts.RegRootsB
import HeapV2StepCerts.FlagRoots
import HeapV2StepCerts.FlagRootsNZCV
import HeapV2StepCerts.ValueTailDef
import Bridge.CruxGenGuarded.EntryBodyTails
import Bridge.CruxGenGuarded.EntryFlagTails
import Bridge.CruxGenGuarded.EntryUmulhTails
import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import Bridge.CruxGenGuarded.EntryControls
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false

namespace HeapV2StepCerts.FlagVN.AndsImm0_2
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryBodyAndsImm0_2
open HeapV2StepCerts

theorem action_prefixV (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rn : BitVec 5) (rn : Rn.toNat < 31)
    (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) ∧
      (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).mem = fetched.mem ∧
      (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).events = fetched.events ∧
      nativeTail real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) enc0 fetched =
        nativeAfterAction real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) enc0 fin ∧
      fin.regs.BTypeNext = (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).regs.BTypeNext ∧
      NativeEntryContract.Frame NativeEntryBodyFlag.AndsImm0_2.writes
        (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) fin ∧
      HookQuiet ticks fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events ∧
      fin.regs.gpr = (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).regs.gpr ∧ fin.regs.SP_EL0 = (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).regs.SP_EL0 ∧ (fin.regs.PSTATE.Z = 1#1 ↔ (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).regs.gpr[(GPRSummary.key Rn.toNat).val] &&& 7#64 = 0#64) ∧
      fin.regs.PSTATE.N = 0#1 ∧ fin.regs.PSTATE.C = 0#1 ∧ fin.regs.PSTATE.V = 0#1 := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) 41
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41 ticks post.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) 41
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have classGuard : NativeEntryBodyFlag.AndsImm0_2.Guard (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) Rn := by
    constructor <;> first | assumption | exact metaPins.el | exact metaPins.nrw | exact metaPins.f4 | exact metaPins.spe | (show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype) | (show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn)
  obtain ⟨fin, action, memRun, eventsRun, actFrame, _, frame, finalQuiet⟩ :=
    NativeEntryBodyFlag.AndsImm0_2.run (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) Rn classGuard ticks metadataQuiet
  obtain ⟨ok2, hg2, hs2, hz2, hn2, hc2, hv2⟩ := HeapV2StepCerts.FlagRoots.TstF4.flags (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) Rn classGuard.rn classGuard.el classGuard.a64 classGuard.aa64 classGuard.btype classGuard.btn (by have := classGuard.rn; omega)
  have e2 : ArmBridge.CruxCore.resSt (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1 : SailM Unit) (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41)) = fin := by
    have h := ok2.symm.trans action
    injection h with _ h2
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.AndsImm0_2.selected Rn)
      (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1) 41 := by
    intro pc t see
    exact NativeEntryBodyDispatch.AndsImm0_2.dispatch_at real pc Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn)
    (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1) enc0 sp currentGuard 41 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).mem := by
    exact memRun
  have events : fin.events = (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).events := by
    exact eventsRun
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).trans post.mem,
    (actionState_events (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).trans post.events,
    ?_, actFrame.btn, frame, finalQuiet,
    memory.trans ((actionState_mem (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).trans post.mem), eventFrame, e2 ▸ hg2, e2 ▸ hs2, e2 ▸ hz2, e2 ▸ hn2, e2 ▸ hc2, e2 ▸ hv2⟩
  calc
    nativeTail real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) enc0 fetched =
        afterSpecPmu real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn)
        (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1) enc0
        (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) := boundary
    _ = nativeAfterAction real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) enc0 fin :=
      action_boundary real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn)
        (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate 31#5 Rn 2#6 0#6 1#1 3#2 1#1) enc0
        (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) fin action


#print axioms action_prefixV

theorem native_tailV (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rn : BitVec 5) (rn : Rn.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) 31 12 == 879088#20) = false) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ sp a fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) ∧
      nativeTail real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame NativeEntryBodyFlag.AndsImm0_2.writes
        (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      BrSysEq a.regs fin.regs ∧ CongOut fin a ∧
      fin.mem = fetched.mem ∧ fin.events = fetched.events ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs.PSTATE.DIT = a.regs.PSTATE.DIT ∧
      fin.regs._PC = source.regs._PC + 4#64 ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs ∧
      a.regs.gpr = (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).regs.gpr ∧ a.regs.SP_EL0 = (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).regs.SP_EL0 ∧ (a.regs.PSTATE.Z = 1#1 ↔ (actionState (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) sp 41).regs.gpr[(GPRSummary.key Rn.toNat).val] &&& 7#64 = 0#64) ∧
      a.regs.PSTATE.N = 0#1 ∧ a.regs.PSTATE.C = 0#1 ∧ a.regs.PSTATE.V = 0#1 := by
  obtain ⟨sp, a, hook, metadataInput, metadataMem, metadataEvents,
    nativePrefix, actionBtn, frame, actionQuiet, actionMem, actionEvents, shapeA⟩ :=
    action_prefixV real source fetched enc0 Rn rn pins input guard (budget + 1) quiet
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have metadataPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) 41
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have actionPins := NativeEntryTail.EntryPins.after_action frame metadataPins
  have next : a.regs.BTypeNext = 0#2 := by
    rw [actionBtn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have enc : a.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) 31 12 == 879088#20) = false
    exact noEret
  have actionIT : a.regs.ShouldAdvanceIT = false :=
    frame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : a.regs.ShouldAdvanceSS = true :=
    frame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, branch, output, events, gic, dit, pc, nonProj⟩ :=
    guarded_after_action_entry real source (NativeEntryBodyDispatch.AndsImm0_2.selected Rn) enc0 a budget actionQuiet
      actionPins next enc eret actionIT actionSS
  have noBranch : a.regs.__BranchTaken = false := frame.bt
  have actionPC : a.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  refine ⟨sp, a, fin, hook, metadataInput, nativePrefix.trans tail,
    frame, finalQuiet, finalPins, sys, branch, output, output.mem.trans actionMem,
    events.trans actionEvents, gic, dit, ?_, nonProj, shapeA⟩
  simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc


#print axioms native_tailV

end HeapV2StepCerts.FlagVN.AndsImm0_2
