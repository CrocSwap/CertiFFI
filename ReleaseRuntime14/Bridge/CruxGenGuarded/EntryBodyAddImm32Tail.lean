import Bridge.CruxGenGuarded.EntryControls
import Bridge.CruxGenGuarded.EntryBodyAddImm32
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded.EntryBodyAddImm32
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/- Internal actual tail, starting at the post-fetch state. Fetch, landing and
full modelStep/Entry/CT are separate obligations. BTI needs neither incoming
BTYPE0 nor BTN0. Other classes consume the protected phase's actual StepPins.
Advance flags and Q are current-state inputs, not future-success premises. -/
run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.EntryBodyAddImm32.native_tail"
  (← IO.getStderr).flush

theorem native_tail (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.AddImm32.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) 31 12 == 879088#20) = false) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ sp a fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18) ∧
      nativeTail real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) enc0 fetched = .ok () fin ∧
      NativeEntryBody.AddImm32.projection a =
        NativeEntryBody.AddImm32.expected (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18) Rd Rn imm12 ∧
      NativeEntryContract.Frame NativeEntryBodyAdapters.AddImm32.writes
        (actionState (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) sp 18) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      BrSysEq a.regs fin.regs ∧ CongOut fin a ∧
      fin.mem = fetched.mem ∧ fin.events = fetched.events ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs.PSTATE.DIT = a.regs.PSTATE.DIT ∧
      fin.regs._PC = source.regs._PC + 4#64 ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs := by
  obtain ⟨sp, a, hook, metadataInput, metadataMem, metadataEvents,
    nativePrefix, projection, frame, actionQuiet, actionMem, actionEvents⟩ :=
    action_prefix real source fetched enc0 Rd Rn imm12 rd rn profile pins input guard (budget + 1) quiet
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have metadataPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) 18
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have actionPins := NativeEntryTail.EntryPins.after_action frame metadataPins
  have actualRegs := congrArg Prod.fst projection
  change a.regs = _ at actualRegs
  have next : a.regs.BTypeNext = 0#2 := by
    rw [actualRegs]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have enc : a.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) 31 12 == 879088#20) = false
    exact noEret
  have actionIT : a.regs.ShouldAdvanceIT = false :=
    frame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : a.regs.ShouldAdvanceSS = true :=
    frame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, branch, output, events, gic, dit, pc, nonProj⟩ :=
    guarded_after_action_entry real source (NativeEntryBodyDispatch.AddImm32.selected Rd Rn imm12) enc0 a budget actionQuiet
      actionPins next enc eret actionIT actionSS
  have noBranch : a.regs.__BranchTaken = false := frame.bt
  have actionPC : a.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  refine ⟨sp, a, fin, hook, metadataInput, nativePrefix.trans tail, projection,
    frame, finalQuiet, finalPins, sys, branch, output, output.mem.trans actionMem,
    events.trans actionEvents, gic, dit, ?_, nonProj⟩
  simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc

#print axioms native_tail
end ArmBridge.CruxGenGuarded.EntryBodyAddImm32
