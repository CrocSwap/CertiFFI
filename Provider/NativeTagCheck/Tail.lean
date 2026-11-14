import NativeTagCheck.Hooks
import NativeTagCheck.PrimitiveFrames
import Bridge.CruxGenGuarded.EntryTail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryTail (EntryPins)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
namespace NativeTagCheck
open NativeMteTagCheck

theorem metadata_choice (word : BitVec 32) (s : NativeState) (see : Int) :
    ChoiceDelta s (actionState word s see) 0 := by
  simp [ChoiceDelta, actionState,
    PrimitiveFrames.res_source _ PrimitiveFrames.spe_pre_preserves,
    PrimitiveFrames.res_counter _ PrimitiveFrames.spe_pre_preserves,
    Std.ExtHashMap.getD_insert]

theorem before_counter_choice (s : NativeState) :
    ChoiceDelta s (beforeCounterCurrent s) 0 := by
  unfold beforeCounterCurrent beforeCounterWithNext
  split <;> simp [ChoiceDelta, beforeCounterTakenWithNext, beforeCounterNotTakenWithNext,
    PrimitiveFrames.res_source _ PrimitiveFrames.ss_advance_preserves,
    PrimitiveFrames.res_counter _ PrimitiveFrames.ss_advance_preserves,
    PrimitiveFrames.res_source _ PrimitiveFrames.spe_cycle_preserves,
    PrimitiveFrames.res_counter _ PrimitiveFrames.spe_cycle_preserves,
    Std.ExtHashMap.getD_insert]

theorem end_choice (s : NativeState) : ChoiceDelta s (nativeEndState s) 0 := by
  exact ⟨rfl, (Nat.add_zero _).symm⟩

/-- Actual epilogue execution, with the original full hook-control domain. -/
theorem after_action_choice (real : Type) [Sail.SailReal real]
    (initial : NativeState) (word : BitVec 32) (enc0 : __InstrEnc)
    (a : NativeState) (budget : Nat) (quiet : HookQuiet (budget+1) a) (pins : EntryPins a)
    (encoding : a.regs.__ThisInstrEnc = .__A64)
    (notEret : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false)
    (it : a.regs.ShouldAdvanceIT = false) (ss : a.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeAfterAction real initial word enc0 a = .ok () fin ∧ ChoiceDelta a fin 0 := by
  obtain ⟨retired, hr, pr, dr⟩ := Hooks.pmu_event_choice (budget+1) a quiet PMU_EVENT_INST_RETIRED
  have frame := PMUFrame.of_E20 pr.frame
  have retiredPins := EntryPins.after_E20 a retired pins pr.frame
  have retiredEncoding : retired.regs.__ThisInstrEnc = .__A64 := frame.enc.trans encoding
  have retiredNotEret :
      (Sail.BitVec.extractLsb (retired.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.thisInstr]
    exact notEret
  have epilogue := epilogue_current_boundary real retired retiredPins retiredEncoding retiredNotEret
    (frame.it.trans it) (frame.ss.trans ss)
  have counterPins := beforeCounterCurrent_pins retired retiredPins
  obtain ⟨counter, hc, pc, dc⟩ := Hooks.system_counter_choice budget (beforeCounterCurrent retired)
    (beforeCounterCurrent_quiet (budget+1) retired pr.quiet)
  have afterCounterPins := entry_after_E22 (beforeCounterCurrent retired) counter counterPins pc.frame
  have counterBoundary := counter_boundary real (beforeCounterCurrent retired) counter hc
    afterCounterPins.f4 afterCounterPins.nrw
  obtain ⟨cycle, hcycle, pcycle, dcycle⟩ := Hooks.pmu_cycle_choice budget counter pc.quiet
  have cycleBoundary := cycle_boundary real counter cycle hcycle
  refine ⟨nativeEndState cycle, ?_, ?_⟩
  · calc
      nativeAfterAction real initial word enc0 a = nativeAfterRetired retired :=
        retired_pmu_boundary real initial word enc0 a retired hr
      _ = nativeAtCounter (beforeCounterCurrent retired) := epilogue
      _ = nativeAtPmuCycle counter := counterBoundary
      _ = .ok () (nativeEndState cycle) := cycleBoundary
  · simpa only [Nat.add_zero] using
      choice_delta_trans (choice_delta_trans (choice_delta_trans
        (choice_delta_trans dr (before_counter_choice retired)) dc) dcycle) (end_choice cycle)

theorem after_action_choice_of_run (real : Type) [Sail.SailReal real]
    (initial : NativeState) (word : BitVec 32) (enc0 : __InstrEnc)
    (a fin : NativeState) (budget : Nat) (quiet : HookQuiet (budget+1) a) (pins : EntryPins a)
    (encoding : a.regs.__ThisInstrEnc = .__A64)
    (notEret : (Sail.BitVec.extractLsb (a.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false)
    (it : a.regs.ShouldAdvanceIT = false) (ss : a.regs.ShouldAdvanceSS = true)
    (run : nativeAfterAction real initial word enc0 a = .ok () fin) : ChoiceDelta a fin 0 := by
  obtain ⟨other, actual, delta⟩ :=
    after_action_choice real initial word enc0 a budget quiet pins encoding notEret it ss
  have equal : fin = other := (EStateM.Result.ok.inj (run.symm.trans actual)).2
  exact equal.symm ▸ delta

theorem spec_choice_of_run (budget : Nat) (s sp : NativeState)
    (quiet : HookQuiet budget s)
    (run : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) s = .ok () sp) : ChoiceDelta s sp 0 := by
  obtain ⟨other, actual, _, delta⟩ := Hooks.pmu_event_choice budget s quiet PMU_EVENT_INST_SPEC
  have equal : sp = other := (EStateM.Result.ok.inj (run.symm.trans actual)).2
  exact equal.symm ▸ delta

/-- Internal composition: every effect premise is filled by a concrete native producer. -/
theorem action_prefix_choice (ticks : Nat) (fetched sp actionFinal : NativeState)
    (word : BitVec 32) (see : Int) (action : SailM Unit)
    (quiet : HookQuiet ticks fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    (preserves : PrimitiveFrames.Preserves action)
    (run : action (actionState word sp see) = .ok () actionFinal) :
    ChoiceDelta fetched actionFinal 0 := by
  simpa only [Nat.add_zero] using choice_delta_trans
    (choice_delta_trans (spec_choice_of_run ticks fetched sp quiet hook) (metadata_choice word sp see))
    (preserves _ _ _ run)

/-- This helper joins real prefix/action/tail runs on the same final state. -/
theorem native_tail_choice_of_action (real : Type) [Sail.SailReal real]
    (initial fetched sp actionFinal fin : NativeState) (word : BitVec 32) (enc0 : __InstrEnc)
    (see : Int) (action : SailM Unit) (budget : Nat)
    (quiet : HookQuiet (budget+1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    (preserves : PrimitiveFrames.Preserves action)
    (actionRun : action (actionState word sp see) = .ok () actionFinal)
    (prefixRun : nativeTail real initial word enc0 fetched = nativeAfterAction real initial word enc0 actionFinal)
    (actionQuiet : HookQuiet (budget+1) actionFinal) (pins : EntryPins actionFinal)
    (encoding : actionFinal.regs.__ThisInstrEnc = .__A64)
    (notEret : (Sail.BitVec.extractLsb (actionFinal.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false)
    (it : actionFinal.regs.ShouldAdvanceIT = false) (ss : actionFinal.regs.ShouldAdvanceSS = true)
    (run : nativeTail real initial word enc0 fetched = .ok () fin) : ChoiceDelta fetched fin 0 := by
  have finalRun : nativeAfterAction real initial word enc0 actionFinal = .ok () fin := prefixRun.symm.trans run
  have delta := after_action_choice_of_run real initial word enc0 actionFinal fin budget
    actionQuiet pins encoding notEret it ss finalRun
  simpa only [Nat.add_zero] using choice_delta_trans
    (action_prefix_choice (budget+1) fetched sp actionFinal word see action quiet hook preserves actionRun) delta

/-- Internal memory-tail composition retains the actual allocation-tag draw count. -/
theorem native_tail_choice_of_delta (real : Type) [Sail.SailReal real]
    (initial fetched sp actionFinal fin : NativeState) (word : BitVec 32) (enc0 : __InstrEnc)
    (see : Int) (budget draws : Nat)
    (quiet : HookQuiet (budget+1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    (actionDelta : ChoiceDelta (actionState word sp see) actionFinal draws)
    (prefixRun : nativeTail real initial word enc0 fetched = nativeAfterAction real initial word enc0 actionFinal)
    (actionQuiet : HookQuiet (budget+1) actionFinal) (pins : EntryPins actionFinal)
    (encoding : actionFinal.regs.__ThisInstrEnc = .__A64)
    (notEret : (Sail.BitVec.extractLsb (actionFinal.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false)
    (it : actionFinal.regs.ShouldAdvanceIT = false) (ss : actionFinal.regs.ShouldAdvanceSS = true)
    (run : nativeTail real initial word enc0 fetched = .ok () fin) :
    ChoiceDelta fetched fin draws := by
  have finalRun : nativeAfterAction real initial word enc0 actionFinal = .ok () fin := prefixRun.symm.trans run
  have delta := after_action_choice_of_run real initial word enc0 actionFinal fin budget
    actionQuiet pins encoding notEret it ss finalRun
  simpa only [Nat.add_zero, Nat.zero_add] using choice_delta_trans
    (choice_delta_trans
      (choice_delta_trans (spec_choice_of_run (budget+1) fetched sp quiet hook)
        (metadata_choice word sp see)) actionDelta) delta

#print axioms metadata_choice
#print axioms after_action_choice
#print axioms after_action_choice_of_run
#print axioms native_tail_choice_of_action
#print axioms native_tail_choice_of_delta
end NativeTagCheck
