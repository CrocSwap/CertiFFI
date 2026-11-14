import Bridge.CruxGenGuarded.EntryCallerControls
import Bridge.CruxGenGuarded.EntryControls
import Bridge.CruxGenGuarded.EntryBlTail
import NativeEntryCallerDispatch.Bl
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded.CallerBl
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded NativeEntryCallerParts
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryTail (EntryPins)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.CallerBl.word_not_eret"
  (← IO.getStderr).flush
theorem word_not_eret (imm26 : BitVec 26) :
    (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v => BitVec.getLsbD v 18) h
    simp only [NativeEntryCallerDispatch.Bl.word, Sail.BitVec.extractLsb,
      BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.append,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend,
      BitVec.getLsbD_setWidth'] at bit
    simp at bit
  simpa using ne

/- Actual post-fetch tail: same owner spec successor, original word dispatch,
canonical metadata/action/tail. No input requires a future state or action
answer. Fetch/profile/source bindings and whole Entry remain separate. -/
run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.CallerBl.native_tail"
  (← IO.getStderr).flush
theorem native_tail (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc) (imm26 : BitVec 26)
    (controls : CallerControls fetched)
    (low : (blTarget imm26 fetched).toNat < 2^55)
    (pins : EntryPins fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched = .ok () fin ∧
      HookQuiet budget fin ∧ EntryPins fin ∧
      fin.regs.PSTATE.BTYPE = fetched.regs.BTypeNext ∧ fin.regs.BTypeNext = fetched.regs.BTypeNext ∧
      SysEq2 fetched.regs fin.regs ∧ BrSysEq fetched.regs fin.regs ∧
      fin.events = fetched.events ∧ fin.mem = fetched.mem ∧
      fin.regs._PC = blTarget imm26 fetched ∧
      fin.regs.gpr = fetched.regs.gpr.set 30 (NativeEntryCallerRegisters.linkValue fetched) ∧
      fin.regs.gpr[30] = fetched.regs._PC + 4#64 ∧
      fin.regs.PSTATE.DIT = fetched.regs.PSTATE.DIT ∧
      CongOut fin (blActionState imm26 (actionState (NativeEntryCallerDispatch.Bl.word imm26) sp 68)) ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap
        (blActionState imm26 (actionState (NativeEntryCallerDispatch.Bl.word imm26) sp 68)).regs fin.regs := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have ps := NativeEntryTail.EntryPins.after_E20 fetched sp pins post.frame
  have pc := caller_controls_after_E20 fetched sp controls post.frame
  let a := actionState (NativeEntryCallerDispatch.Bl.word imm26) sp 68
  have ca : CallerControls a := caller_controls_at_metadata sp (NativeEntryCallerDispatch.Bl.word imm26) 68 pc
  have pa : EntryPins a := entryPins_at_metadata sp (NativeEntryCallerDispatch.Bl.word imm26) 68 ps
  have qa : HookQuiet (budget + 1) a := actionState_quiet (NativeEntryCallerDispatch.Bl.word imm26) sp 68 (budget + 1) post.quiet
  have specOut := e20_output fetched sp post.frame post.mem
  have metadataOut := caller_metadata_output sp (NativeEntryCallerDispatch.Bl.word imm26) 68
  have target : blTarget imm26 a = blTarget imm26 fetched := by
    rw [NativeEntryCallerRegisters.bl_target, NativeEntryCallerRegisters.bl_target]
    change sp.regs._PC + _ = fetched.regs._PC + _
    rw [(PMUFrame.of_E20 post.frame).pc]
  have lowA : (blTarget imm26 a).toNat < 2^55 := by rw [target]; exact low
  have encA : a.regs.__ThisInstrEnc = .__A64 := by rfl
  have eretA : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false :=
    word_not_eret imm26
  have itA : a.regs.ShouldAdvanceIT = false := (PMUFrame.of_E20 post.frame).it.trans it
  have ssA : a.regs.ShouldAdvanceSS = true := (PMUFrame.of_E20 post.frame).ss.trans ss
  have dispatch : DispatchAt real (NativeEntryCallerDispatch.Bl.word imm26) (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1) 68 := by
    intro pc t see
    exact NativeEntryCallerDispatch.Bl.dispatch_at real pc imm26 t (by simpa using see)
  have metadataBoundary := metadata_boundary_at real source (NativeEntryCallerDispatch.Bl.word imm26) (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1) enc0 sp
    (guard.after_E20 post.frame) 68 (by decide) dispatch
  obtain ⟨fin, run, qfin, pfin, btype, next, sys, branch, out, events, gic, dit, finalPC,
    memory, gpr, lr, frame⟩ :=
    bl_action_tail real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 imm26 a budget ca lowA qa pa encA eretA itA ssA
  have btnA : a.regs.BTypeNext = fetched.regs.BTypeNext := by
    change sp.regs.BTypeNext = fetched.regs.BTypeNext
    exact (PMUFrame.of_E20 post.frame).btn
  have pcA : a.regs._PC = fetched.regs._PC := (PMUFrame.of_E20 post.frame).pc
  have gprA : a.regs.gpr = fetched.regs.gpr := metadataOut.gpr.trans specOut.gpr
  have linkA : NativeEntryCallerRegisters.linkValue a = NativeEntryCallerRegisters.linkValue fetched := by
    rw [NativeEntryCallerRegisters.link_value, NativeEntryCallerRegisters.link_value, pcA]
  refine ⟨sp, fin, hook, ?_, qfin, pfin, btype.trans btnA, next.trans btnA,
    sysEq2_trans _ _ _ (e20_sys _ _ post.frame)
      (sysEq2_trans _ _ _ (caller_metadata_sys sp (NativeEntryCallerDispatch.Bl.word imm26) 68 ps) sys),
    brSysEq_trans _ _ _ (e20_branch _ _ post.frame)
      (brSysEq_trans _ _ _ (caller_metadata_branch sp (NativeEntryCallerDispatch.Bl.word imm26) 68) branch),
    events.trans ((actionState_events (NativeEntryCallerDispatch.Bl.word imm26) sp 68).trans post.events),
    memory.trans ((actionState_mem (NativeEntryCallerDispatch.Bl.word imm26) sp 68).trans post.mem),
    finalPC.trans target, ?_, ?_, ?_, out, frame⟩
  · exact (spec_pmu_boundary real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched sp hook).trans (metadataBoundary.trans run)
  · simpa only [gprA, linkA] using gpr
  · simpa only [pcA] using lr
  · exact dit.trans (congrArg ProcState.DIT (PMUFrame.of_E20 post.frame).pstate)

#print axioms word_not_eret
#print axioms native_tail
end ArmBridge.CruxGenGuarded.CallerBl
