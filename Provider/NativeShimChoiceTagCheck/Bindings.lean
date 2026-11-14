import NativeShimChoiceTagCheck.Actions
import Bridge.CruxGenGuarded.EntryBtiCTail
import Bridge.CruxGenGuarded.EntryMrsDitTail
import Bridge.CruxGenGuarded.EntryDitOnTail
import Bridge.CruxGenGuarded.EntryMsrDitTail
import Bridge.CruxGenGuarded.EntryIsbSyTail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeMteTagCheck NativeEntryTail
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
namespace NativeShimChoiceTagCheck

/-- Expanded stable contract, definitionally matching the current scalar trace API. -/
def TailChoiceAt (real : Type) [Sail.SailReal real] (source : NativeState) (word : BitVec 32) : Prop :=
  ∀ (fetched : NativeState) (enc : __InstrEnc) (budget : Nat),
    StepPins fetched → NativeEntryInput.Input source fetched → MetadataGuard fetched →
    HookQuiet (budget+1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true →
    ∀ fin, nativeTail real source word enc fetched = .ok () fin → ChoiceDelta fetched fin 0

namespace Prefix.BtiC
theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryDispatch.BtiC.word) sp 97) ∧
      (actionState (NativeEntryDispatch.BtiC.word) sp 97).mem = fetched.mem ∧
      (actionState (NativeEntryDispatch.BtiC.word) sp 97).events = fetched.events ∧
      nativeTail real source (NativeEntryDispatch.BtiC.word) enc0 fetched =
        nativeAfterAction real source (NativeEntryDispatch.BtiC.word) enc0 fin ∧
      NativeEntry.BtiC.projection fin =
        NativeEntry.BtiC.expected (actionState (NativeEntryDispatch.BtiC.word) sp 97) ∧
      NativeEntryContract.Frame NativeEntryAdapters.BtiC.writes
        (actionState (NativeEntryDispatch.BtiC.word) sp 97) fin ∧
      HookQuiet ticks fin ∧
      (decode_bti_aarch64_instrs_system_hints 2#3 4#4 : SailM Unit) (actionState (NativeEntryDispatch.BtiC.word) sp 97) = .ok () fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryDispatch.BtiC.word) 97
  have metadataQuiet := actionState_quiet (NativeEntryDispatch.BtiC.word) sp 97 ticks post.quiet

  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryContract.BtiC.run (actionState (NativeEntryDispatch.BtiC.word) sp 97) ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryDispatch.BtiC.word)
      (decode_bti_aarch64_instrs_system_hints 2#3 4#4) 97 := by
    intro pc t see
    exact NativeEntryDispatch.BtiC.dispatch_at real pc t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryDispatch.BtiC.word)
    (decode_bti_aarch64_instrs_system_hints 2#3 4#4) enc0 sp currentGuard 97 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryDispatch.BtiC.word) sp 97).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryDispatch.BtiC.word) sp 97).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryDispatch.BtiC.word) sp 97).trans post.mem,
    (actionState_events (NativeEntryDispatch.BtiC.word) sp 97).trans post.events,
    ?_, projection, frame, finalQuiet, action,
    memory.trans ((actionState_mem (NativeEntryDispatch.BtiC.word) sp 97).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryDispatch.BtiC.word) enc0 fetched =
        afterSpecPmu real source (NativeEntryDispatch.BtiC.word) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryDispatch.BtiC.word) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryDispatch.BtiC.word)
        (decode_bti_aarch64_instrs_system_hints 2#3 4#4) enc0
        (actionState (NativeEntryDispatch.BtiC.word) sp 97) := boundary
    _ = nativeAfterAction real source (NativeEntryDispatch.BtiC.word) enc0 fin :=
      action_boundary real source (NativeEntryDispatch.BtiC.word)
        (decode_bti_aarch64_instrs_system_hints 2#3 4#4) enc0
        (actionState (NativeEntryDispatch.BtiC.word) sp 97) fin action


#print axioms action_prefix
end Prefix.BtiC

theorem btiC_choice (real : Type) [Sail.SailReal real]
    (source : NativeState) : TailChoiceAt real source (NativeEntryDispatch.BtiC.word) := by
  intro fetched enc budget pins input guard quiet it ss fin run
  obtain ⟨sp, act, hook, metadataInput, _, _, boundary, projection, frame, actionQuiet,
    actionRun, _, _⟩ := Prefix.BtiC.action_prefix real source fetched enc input guard (budget+1) quiet
  have post := entry_spec_post fetched sp (budget+1) quiet hook

  have actionDelta := BtiC.action_choice (actionState (NativeEntryDispatch.BtiC.word) sp 97) act actionRun
  have metadataPins := entryPins_at_metadata sp (NativeEntryDispatch.BtiC.word) 97
    (EntryPins.after_E20 fetched sp (EntryPins.of_scalar fetched pins) post.frame)
  have actionPins := EntryPins.after_action frame metadataPins
  have encoding : act.regs.__ThisInstrEnc = .__A64 := frame.enc
  have notEret : (Sail.BitVec.extractLsb (act.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    exact EntryBtiC.word_not_eret
  have actionIT : act.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : act.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  exact NativeTagCheck.native_tail_choice_of_delta real source fetched sp act fin (NativeEntryDispatch.BtiC.word) enc 97 budget 0
    quiet hook actionDelta boundary actionQuiet actionPins encoding notEret actionIT actionSS run

#print axioms btiC_choice

namespace Prefix.MrsDit
theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rt : BitVec 5) (rt : Rt.toNat < 31)
    (profile : NativeEntryAdapters.MrsDit.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701) ∧
      (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701).mem = fetched.mem ∧
      (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701).events = fetched.events ∧
      nativeTail real source (NativeEntryDispatch.MrsDit.word Rt) enc0 fetched =
        nativeAfterAction real source (NativeEntryDispatch.MrsDit.word Rt) enc0 fin ∧
      NativeEntry.MrsDit.projection fin =
        NativeEntry.MrsDit.expected (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701) Rt ∧
      NativeEntryContract.Frame NativeEntryAdapters.MrsDit.writes
        (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701) fin ∧
      HookQuiet ticks fin ∧
      (decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1 : SailM Unit) (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701) = .ok () fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryDispatch.MrsDit.word Rt) 701
  have metadataQuiet := actionState_quiet (NativeEntryDispatch.MrsDit.word Rt) sp 701 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntry.MrsDit.Guard (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701) Rt := by
    exact NativeEntryAdapters.MrsDit.guard_at_metadata source sp Rt (NativeEntryDispatch.MrsDit.word Rt) 701 profile currentInput.controls currentPins ticks post.quiet rt
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryContract.MrsDit.run (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701) Rt classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryDispatch.MrsDit.word Rt)
      (decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1) 701 := by
    intro pc t see
    exact NativeEntryDispatch.MrsDit.dispatch_at real pc Rt t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryDispatch.MrsDit.word Rt)
    (decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1) enc0 sp currentGuard 701 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryDispatch.MrsDit.word Rt) sp 701).trans post.mem,
    (actionState_events (NativeEntryDispatch.MrsDit.word Rt) sp 701).trans post.events,
    ?_, projection, frame, finalQuiet, action,
    memory.trans ((actionState_mem (NativeEntryDispatch.MrsDit.word Rt) sp 701).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryDispatch.MrsDit.word Rt) enc0 fetched =
        afterSpecPmu real source (NativeEntryDispatch.MrsDit.word Rt) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryDispatch.MrsDit.word Rt) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryDispatch.MrsDit.word Rt)
        (decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1) enc0
        (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701) := boundary
    _ = nativeAfterAction real source (NativeEntryDispatch.MrsDit.word Rt) enc0 fin :=
      action_boundary real source (NativeEntryDispatch.MrsDit.word Rt)
        (decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1) enc0
        (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701) fin action


#print axioms action_prefix
end Prefix.MrsDit

theorem mrsDit_choice (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rt : BitVec 5) (rt : Rt.toNat < 31) (profile : NativeEntryAdapters.MrsDit.Profile source) : TailChoiceAt real source (NativeEntryDispatch.MrsDit.word Rt) := by
  intro fetched enc budget pins input guard quiet it ss fin run
  obtain ⟨sp, act, hook, metadataInput, _, _, boundary, projection, frame, actionQuiet,
    actionRun, _, _⟩ := Prefix.MrsDit.action_prefix real source fetched enc Rt rt profile pins input guard (budget+1) quiet
  have post := entry_spec_post fetched sp (budget+1) quiet hook

  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntry.MrsDit.Guard (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701) Rt := by
    exact NativeEntryAdapters.MrsDit.guard_at_metadata source sp Rt (NativeEntryDispatch.MrsDit.word Rt) 701 profile currentInput.controls currentPins (budget+1) post.quiet rt

  have actionDelta := MrsDit.action_choice (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701) act Rt classGuard actionRun
  have metadataPins := entryPins_at_metadata sp (NativeEntryDispatch.MrsDit.word Rt) 701
    (EntryPins.after_E20 fetched sp (EntryPins.of_scalar fetched pins) post.frame)
  have actionPins := EntryPins.after_action frame metadataPins
  have encoding : act.regs.__ThisInstrEnc = .__A64 := frame.enc
  have notEret : (Sail.BitVec.extractLsb (act.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    exact EntryMrsDit.word_not_eret Rt
  have actionIT : act.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : act.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  exact NativeTagCheck.native_tail_choice_of_delta real source fetched sp act fin (NativeEntryDispatch.MrsDit.word Rt) enc 701 budget 0
    quiet hook actionDelta boundary actionQuiet actionPins encoding notEret actionIT actionSS run

#print axioms mrsDit_choice

namespace Prefix.DitOn
theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (profile : NativeEntryAdapters.DitOn.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryDispatch.DitOn.word) sp 703) ∧
      (actionState (NativeEntryDispatch.DitOn.word) sp 703).mem = fetched.mem ∧
      (actionState (NativeEntryDispatch.DitOn.word) sp 703).events = fetched.events ∧
      nativeTail real source (NativeEntryDispatch.DitOn.word) enc0 fetched =
        nativeAfterAction real source (NativeEntryDispatch.DitOn.word) enc0 fin ∧
      NativeEntry.DitOn.projection fin =
        NativeEntry.DitOn.expected (actionState (NativeEntryDispatch.DitOn.word) sp 703) ∧
      NativeEntryContract.Frame NativeEntryAdapters.DitOn.writes
        (actionState (NativeEntryDispatch.DitOn.word) sp 703) fin ∧
      HookQuiet ticks fin ∧
      (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3 : SailM Unit) (actionState (NativeEntryDispatch.DitOn.word) sp 703) = .ok () fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryDispatch.DitOn.word) 703
  have metadataQuiet := actionState_quiet (NativeEntryDispatch.DitOn.word) sp 703 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntry.DitOn.Guard (actionState (NativeEntryDispatch.DitOn.word) sp 703) := by
    exact NativeEntryAdapters.DitOn.guard_at_metadata source sp 703 profile currentInput.controls currentPins ticks post.quiet
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryContract.DitOn.run (actionState (NativeEntryDispatch.DitOn.word) sp 703) classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryDispatch.DitOn.word)
      (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3) 703 := by
    intro pc t see
    exact NativeEntryDispatch.DitOn.dispatch_at real pc t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryDispatch.DitOn.word)
    (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3) enc0 sp currentGuard 703 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryDispatch.DitOn.word) sp 703).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryDispatch.DitOn.word) sp 703).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryDispatch.DitOn.word) sp 703).trans post.mem,
    (actionState_events (NativeEntryDispatch.DitOn.word) sp 703).trans post.events,
    ?_, projection, frame, finalQuiet, action,
    memory.trans ((actionState_mem (NativeEntryDispatch.DitOn.word) sp 703).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryDispatch.DitOn.word) enc0 fetched =
        afterSpecPmu real source (NativeEntryDispatch.DitOn.word) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryDispatch.DitOn.word) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryDispatch.DitOn.word)
        (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3) enc0
        (actionState (NativeEntryDispatch.DitOn.word) sp 703) := boundary
    _ = nativeAfterAction real source (NativeEntryDispatch.DitOn.word) enc0 fin :=
      action_boundary real source (NativeEntryDispatch.DitOn.word)
        (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 1#4 3#3) enc0
        (actionState (NativeEntryDispatch.DitOn.word) sp 703) fin action


#print axioms action_prefix
end Prefix.DitOn

theorem ditOn_choice (real : Type) [Sail.SailReal real]
    (source : NativeState) (profile : NativeEntryAdapters.DitOn.Profile source) : TailChoiceAt real source (NativeEntryDispatch.DitOn.word) := by
  intro fetched enc budget pins input guard quiet it ss fin run
  obtain ⟨sp, act, hook, metadataInput, _, _, boundary, projection, frame, actionQuiet,
    actionRun, _, _⟩ := Prefix.DitOn.action_prefix real source fetched enc profile pins input guard (budget+1) quiet
  have post := entry_spec_post fetched sp (budget+1) quiet hook

  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntry.DitOn.Guard (actionState (NativeEntryDispatch.DitOn.word) sp 703) := by
    exact NativeEntryAdapters.DitOn.guard_at_metadata source sp 703 profile currentInput.controls currentPins (budget+1) post.quiet

  have actionDelta := DitOn.action_choice (actionState (NativeEntryDispatch.DitOn.word) sp 703) act classGuard actionRun
  have metadataPins := entryPins_at_metadata sp (NativeEntryDispatch.DitOn.word) 703
    (EntryPins.after_E20 fetched sp (EntryPins.of_scalar fetched pins) post.frame)
  have actionPins := EntryPins.after_action frame metadataPins
  have encoding : act.regs.__ThisInstrEnc = .__A64 := frame.enc
  have notEret : (Sail.BitVec.extractLsb (act.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    exact EntryDitOn.word_not_eret
  have actionIT : act.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : act.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  exact NativeTagCheck.native_tail_choice_of_delta real source fetched sp act fin (NativeEntryDispatch.DitOn.word) enc 703 budget 0
    quiet hook actionDelta boundary actionQuiet actionPins encoding notEret actionIT actionSS run

#print axioms ditOn_choice

namespace Prefix.MsrDit
theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rt : BitVec 5) (rt : Rt.toNat < 31)
    (profile : NativeEntryAdapters.MsrDit.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) ∧
      (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702).mem = fetched.mem ∧
      (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702).events = fetched.events ∧
      nativeTail real source (NativeEntryDispatch.MsrDit.word Rt) enc0 fetched =
        nativeAfterAction real source (NativeEntryDispatch.MsrDit.word Rt) enc0 fin ∧
      NativeEntry.MsrDit.projection fin =
        NativeEntry.MsrDit.expected (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) Rt ∧
      NativeEntryContract.Frame NativeEntryAdapters.MsrDit.writes
        (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) fin ∧
      HookQuiet ticks fin ∧
      (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1 : SailM Unit) (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) = .ok () fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryDispatch.MsrDit.word Rt) 702
  have metadataQuiet := actionState_quiet (NativeEntryDispatch.MsrDit.word Rt) sp 702 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntry.MsrDit.Guard (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) Rt := by
    simpa only [NativeEntryDispatch.MsrDit.effect_word] using NativeEntryAdapters.MsrDit.guard_at_metadata source sp Rt 702 profile currentInput.controls currentPins ticks post.quiet rt
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryContract.MsrDit.run (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) Rt classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryDispatch.MsrDit.word Rt)
      (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1) 702 := by
    intro pc t see
    exact NativeEntryDispatch.MsrDit.dispatch_at real pc Rt t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryDispatch.MsrDit.word Rt)
    (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1) enc0 sp currentGuard 702 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702).events := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryDispatch.MsrDit.word Rt) sp 702).trans post.mem,
    (actionState_events (NativeEntryDispatch.MsrDit.word Rt) sp 702).trans post.events,
    ?_, projection, frame, finalQuiet, action,
    memory.trans ((actionState_mem (NativeEntryDispatch.MsrDit.word Rt) sp 702).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryDispatch.MsrDit.word Rt) enc0 fetched =
        afterSpecPmu real source (NativeEntryDispatch.MsrDit.word Rt) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryDispatch.MsrDit.word Rt) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryDispatch.MsrDit.word Rt)
        (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1) enc0
        (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) := boundary
    _ = nativeAfterAction real source (NativeEntryDispatch.MsrDit.word Rt) enc0 fin :=
      action_boundary real source (NativeEntryDispatch.MsrDit.word Rt)
        (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1) enc0
        (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) fin action


#print axioms action_prefix
end Prefix.MsrDit

theorem msrDit_choice (real : Type) [Sail.SailReal real]
    (source : NativeState) (Rt : BitVec 5) (rt : Rt.toNat < 31) (profile : NativeEntryAdapters.MsrDit.Profile source) : TailChoiceAt real source (NativeEntryDispatch.MsrDit.word Rt) := by
  intro fetched enc budget pins input guard quiet it ss fin run
  obtain ⟨sp, act, hook, metadataInput, _, _, boundary, projection, frame, actionQuiet,
    actionRun, _, _⟩ := Prefix.MsrDit.action_prefix real source fetched enc Rt rt profile pins input guard (budget+1) quiet
  have post := entry_spec_post fetched sp (budget+1) quiet hook

  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntry.MsrDit.Guard (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) Rt := by
    simpa only [NativeEntryDispatch.MsrDit.effect_word] using NativeEntryAdapters.MsrDit.guard_at_metadata source sp Rt 702 profile currentInput.controls currentPins (budget+1) post.quiet rt

  have actionDelta := MsrDit.action_choice (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) act Rt classGuard actionRun
  have metadataPins := entryPins_at_metadata sp (NativeEntryDispatch.MsrDit.word Rt) 702
    (EntryPins.after_E20 fetched sp (EntryPins.of_scalar fetched pins) post.frame)
  have actionPins := EntryPins.after_action frame metadataPins
  have encoding : act.regs.__ThisInstrEnc = .__A64 := frame.enc
  have notEret : (Sail.BitVec.extractLsb (act.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    exact EntryMsrDit.word_not_eret Rt
  have actionIT : act.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : act.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  exact NativeTagCheck.native_tail_choice_of_delta real source fetched sp act fin (NativeEntryDispatch.MsrDit.word Rt) enc 702 budget 0
    quiet hook actionDelta boundary actionQuiet actionPins encoding notEret actionIT actionSS run

#print axioms msrDit_choice

namespace Prefix.IsbSy
theorem action_prefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (profile : NativeEntryAdapters.IsbSy.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    ∃ sp fin,
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntryInput.Input source (actionState (NativeEntryDispatch.IsbSy.word) sp 483) ∧
      (actionState (NativeEntryDispatch.IsbSy.word) sp 483).mem = fetched.mem ∧
      (actionState (NativeEntryDispatch.IsbSy.word) sp 483).events = fetched.events ∧
      nativeTail real source (NativeEntryDispatch.IsbSy.word) enc0 fetched =
        nativeAfterAction real source (NativeEntryDispatch.IsbSy.word) enc0 fin ∧
      NativeEntry.IsbSy.projection fin =
        NativeEntry.IsbSy.expected (actionState (NativeEntryDispatch.IsbSy.word) sp 483) ∧
      NativeEntryContract.Frame NativeEntryAdapters.IsbSy.writes
        (actionState (NativeEntryDispatch.IsbSy.word) sp 483) fin ∧
      HookQuiet ticks fin ∧
      (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4 : SailM Unit) (actionState (NativeEntryDispatch.IsbSy.word) sp 483) = .ok () fin ∧ fin.mem = fetched.mem ∧
      fin.events = fetched.events.push (.barrier (.Barrier_ISB ())) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryDispatch.IsbSy.word) 483
  have metadataQuiet := actionState_quiet (NativeEntryDispatch.IsbSy.word) sp 483 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntry.IsbSy.Guard (actionState (NativeEntryDispatch.IsbSy.word) sp 483) := by
    exact NativeEntryAdapters.IsbSy.guard_at_metadata source sp (NativeEntryDispatch.IsbSy.word) 483 profile currentInput.controls currentPins ticks post.quiet
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryContract.IsbSy.run (actionState (NativeEntryDispatch.IsbSy.word) sp 483) classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryDispatch.IsbSy.word)
      (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4) 483 := by
    intro pc t see
    exact NativeEntryDispatch.IsbSy.dispatch_at real pc t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryDispatch.IsbSy.word)
    (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4) enc0 sp currentGuard 483 (by decide) dispatch
  have memory : fin.mem = (actionState (NativeEntryDispatch.IsbSy.word) sp 483).mem := by
    exact congrArg (fun value => value.2.1) projection
  have events : fin.events = (actionState (NativeEntryDispatch.IsbSy.word) sp 483).events.push (.barrier (.Barrier_ISB ())) := by
    exact congrArg (fun value => value.2.2) projection
  have eventFrame : fin.events = fetched.events.push (.barrier (.Barrier_ISB ())) := by
    simpa only [actionState_events, post.events] using events
  refine ⟨sp, fin, hook, metadataInput,
    (actionState_mem (NativeEntryDispatch.IsbSy.word) sp 483).trans post.mem,
    (actionState_events (NativeEntryDispatch.IsbSy.word) sp 483).trans post.events,
    ?_, projection, frame, finalQuiet, action,
    memory.trans ((actionState_mem (NativeEntryDispatch.IsbSy.word) sp 483).trans post.mem), eventFrame⟩
  calc
    nativeTail real source (NativeEntryDispatch.IsbSy.word) enc0 fetched =
        afterSpecPmu real source (NativeEntryDispatch.IsbSy.word) enc0 sp :=
      spec_pmu_boundary real source (NativeEntryDispatch.IsbSy.word) enc0 fetched sp hook
    _ = nativeAtAction real source (NativeEntryDispatch.IsbSy.word)
        (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4) enc0
        (actionState (NativeEntryDispatch.IsbSy.word) sp 483) := boundary
    _ = nativeAfterAction real source (NativeEntryDispatch.IsbSy.word) enc0 fin :=
      action_boundary real source (NativeEntryDispatch.IsbSy.word)
        (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4) enc0
        (actionState (NativeEntryDispatch.IsbSy.word) sp 483) fin action


#print axioms action_prefix
end Prefix.IsbSy

theorem isbSy_choice (real : Type) [Sail.SailReal real]
    (source : NativeState) (profile : NativeEntryAdapters.IsbSy.Profile source) : TailChoiceAt real source (NativeEntryDispatch.IsbSy.word) := by
  intro fetched enc budget pins input guard quiet it ss fin run
  obtain ⟨sp, act, hook, metadataInput, _, _, boundary, projection, frame, actionQuiet,
    actionRun, _, _⟩ := Prefix.IsbSy.action_prefix real source fetched enc profile pins input guard (budget+1) quiet
  have post := entry_spec_post fetched sp (budget+1) quiet hook

  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntry.IsbSy.Guard (actionState (NativeEntryDispatch.IsbSy.word) sp 483) := by
    exact NativeEntryAdapters.IsbSy.guard_at_metadata source sp (NativeEntryDispatch.IsbSy.word) 483 profile currentInput.controls currentPins (budget+1) post.quiet

  have actionDelta := IsbSy.action_choice (actionState (NativeEntryDispatch.IsbSy.word) sp 483) act classGuard actionRun
  have metadataPins := entryPins_at_metadata sp (NativeEntryDispatch.IsbSy.word) 483
    (EntryPins.after_E20 fetched sp (EntryPins.of_scalar fetched pins) post.frame)
  have actionPins := EntryPins.after_action frame metadataPins
  have encoding : act.regs.__ThisInstrEnc = .__A64 := frame.enc
  have notEret : (Sail.BitVec.extractLsb (act.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    exact EntryIsbSy.word_not_eret
  have actionIT : act.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : act.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  exact NativeTagCheck.native_tail_choice_of_delta real source fetched sp act fin (NativeEntryDispatch.IsbSy.word) enc 483 budget 0
    quiet hook actionDelta boundary actionQuiet actionPins encoding notEret actionIT actionSS run

#print axioms isbSy_choice

theorem mrsDit9_choice (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.MrsDit.Profile source) :
    TailChoiceAt real source (NativeEntryDispatch.MrsDit.word 9#5) :=
  mrsDit_choice real source 9#5 (by decide) profile

theorem msrDit9_choice (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.MsrDit.Profile source) :
    TailChoiceAt real source (NativeEntryDispatch.MsrDit.word 9#5) :=
  msrDit_choice real source 9#5 (by decide) profile

#print axioms mrsDit9_choice
#print axioms msrDit9_choice
end NativeShimChoiceTagCheck
