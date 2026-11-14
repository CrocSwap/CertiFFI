import Bridge.CruxGenGuarded.EntryBodySecpAdcZZ
import Bridge.CruxGenGuarded.EntryBodySecpAdcsZR
import Bridge.CruxGenGuarded.EntryBodySecpAddsZR
import Bridge.CruxGenGuarded.EntryBodySecpAnd64
import Bridge.CruxGenGuarded.EntryBodySecpAndMask32
import Bridge.CruxGenGuarded.EntryBodySecpCsel1
import Bridge.CruxGenGuarded.EntryBodySecpCsinv0ZZ
import Bridge.CruxGenGuarded.EntryBodySecpCsinv2ZZ
import Bridge.CruxGenGuarded.EntryBodySecpEor64
import Bridge.CruxGenGuarded.EntryBodySecpLsl1
import Bridge.CruxGenGuarded.EntryBodySecpLsr31
import Bridge.CruxGenGuarded.EntryBodySecpLsr32
import Bridge.CruxGenGuarded.EntryBodySecpLsr63
import Bridge.CruxGenGuarded.EntryBodySecpOrr64
import Bridge.CruxGenGuarded.EntryBodySecpSbc64
import TranslateScalarTagCheck.Actions
import TranslateSpan.DefaultScalarTrace
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024
set_option Elab.async false
namespace TranslateScalarTagCheck.Secp
theorem prefix_0 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpAndMask32.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) enc0
      NativeEntryBodyAdapters.SecpAndMask32.writes 40 (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 31#6 0#6 1#1 0#2 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) 40
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) sp 40 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpAndMask32.Guard (actionState (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) sp 40) Rd Rn := by
    exact NativeEntryBodyAdapters.SecpAndMask32.guard_at_metadata source sp Rd Rn (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) 40 profile currentInput.controls currentPins ticks post.quiet rd rn
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpAndMask32.run (actionState (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) sp 40) Rd Rn classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn)
      (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 31#6 0#6 1#1 0#2 1#1) 40 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpAndMask32.dispatch_at real pc Rd Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn)
    (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 31#6 0#6 1#1 0#2 1#1) enc0 sp currentGuard 40 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn)
          (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 31#6 0#6 1#1 0#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) sp 40) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn)
          (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 31#6 0#6 1#1 0#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) sp 40) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) sp 40) ((decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 31#6 0#6 1#1 0#2 1#1) (actionState (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) sp 40)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_0

theorem tail_0 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpAndMask32.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpAndMask32.selected Rd Rn)
    NativeEntryBodyAdapters.SecpAndMask32.writes 40 (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 31#6 0#6 1#1 0#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_5 Rd Rn 31#6 0#6 state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_0 real source fetched enc0 Rd Rn rd rn profile pins input guard (budget + 1) quiet

#print axioms tail_0

theorem prefix_1 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpCsinv0ZZ.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0
      NativeEntryBodyAdapters.SecpCsinv0ZZ.writes 189 (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) 189
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpCsinv0ZZ.Guard (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) Rd := by
    exact NativeEntryBodyAdapters.SecpCsinv0ZZ.guard_at_metadata source sp Rd (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) 189 profile currentInput.controls currentPins ticks post.quiet rd
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpCsinv0ZZ.run (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) Rd classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd)
      (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1) 189 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpCsinv0ZZ.dispatch_at real pc Rd t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd)
    (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1) enc0 sp currentGuard 189 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd)
          (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd)
          (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189) ((decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1) (actionState (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) sp 189)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_1

theorem tail_1 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpCsinv0ZZ.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpCsinv0ZZ.selected Rd)
    NativeEntryBodyAdapters.SecpCsinv0ZZ.writes 189 (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_11 Rd 31#5 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_1 real source fetched enc0 Rd rd profile pins input guard (budget + 1) quiet

#print axioms tail_1

theorem prefix_2 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpCsinv2ZZ.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) enc0
      NativeEntryBodyAdapters.SecpCsinv2ZZ.writes 189 (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 2#4 31#5 1#1 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) 189
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) sp 189 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpCsinv2ZZ.Guard (actionState (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) sp 189) Rd := by
    exact NativeEntryBodyAdapters.SecpCsinv2ZZ.guard_at_metadata source sp Rd (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) 189 profile currentInput.controls currentPins ticks post.quiet rd
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpCsinv2ZZ.run (actionState (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) sp 189) Rd classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd)
      (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 2#4 31#5 1#1 1#1) 189 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpCsinv2ZZ.dispatch_at real pc Rd t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd)
    (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 2#4 31#5 1#1 1#1) enc0 sp currentGuard 189 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd)
          (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 2#4 31#5 1#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) sp 189) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd)
          (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 2#4 31#5 1#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) sp 189) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) sp 189) ((decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 2#4 31#5 1#1 1#1) (actionState (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) sp 189)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_2

theorem tail_2 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpCsinv2ZZ.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpCsinv2ZZ.selected Rd)
    NativeEntryBodyAdapters.SecpCsinv2ZZ.writes 189 (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 2#4 31#5 1#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_12 Rd 31#5 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_2 real source fetched enc0 Rd rd profile pins input guard (budget + 1) quiet

#print axioms tail_2

theorem prefix_3 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpLsl1.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) enc0
      NativeEntryBodyAdapters.SecpLsl1.writes 78 (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 62#6 63#6 1#1 2#2 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) 78
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) sp 78 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpLsl1.Guard (actionState (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) sp 78) Rd Rn := by
    exact NativeEntryBodyAdapters.SecpLsl1.guard_at_metadata source sp Rd Rn (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) 78 profile currentInput.controls currentPins ticks post.quiet rd rn
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpLsl1.run (actionState (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) sp 78) Rd Rn classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn)
      (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 62#6 63#6 1#1 2#2 1#1) 78 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpLsl1.dispatch_at real pc Rd Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn)
    (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 62#6 63#6 1#1 2#2 1#1) enc0 sp currentGuard 78 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn)
          (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 62#6 63#6 1#1 2#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) sp 78) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn)
          (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 62#6 63#6 1#1 2#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) sp 78) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) sp 78) ((decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 62#6 63#6 1#1 2#2 1#1) (actionState (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) sp 78)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_3

theorem tail_3 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpLsl1.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpLsl1.selected Rd Rn)
    NativeEntryBodyAdapters.SecpLsl1.writes 78 (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 62#6 63#6 1#1 2#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_24 Rd Rn 62#6 63#6 state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_3 real source fetched enc0 Rd Rn rd rn profile pins input guard (budget + 1) quiet

#print axioms tail_3

theorem prefix_4 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpLsr31.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) enc0
      NativeEntryBodyAdapters.SecpLsr31.writes 78 (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 31#6 1#1 2#2 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) 78
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) sp 78 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpLsr31.Guard (actionState (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) sp 78) Rd Rn := by
    exact NativeEntryBodyAdapters.SecpLsr31.guard_at_metadata source sp Rd Rn (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) 78 profile currentInput.controls currentPins ticks post.quiet rd rn
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpLsr31.run (actionState (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) sp 78) Rd Rn classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn)
      (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 31#6 1#1 2#2 1#1) 78 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpLsr31.dispatch_at real pc Rd Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn)
    (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 31#6 1#1 2#2 1#1) enc0 sp currentGuard 78 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn)
          (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 31#6 1#1 2#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) sp 78) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn)
          (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 31#6 1#1 2#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) sp 78) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) sp 78) ((decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 31#6 1#1 2#2 1#1) (actionState (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) sp 78)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_4

theorem tail_4 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpLsr31.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpLsr31.selected Rd Rn)
    NativeEntryBodyAdapters.SecpLsr31.writes 78 (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 31#6 1#1 2#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_24 Rd Rn 63#6 31#6 state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_4 real source fetched enc0 Rd Rn rd rn profile pins input guard (budget + 1) quiet

#print axioms tail_4

theorem prefix_5 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpLsr32.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0
      NativeEntryBodyAdapters.SecpLsr32.writes 78 (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) 78
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpLsr32.Guard (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) Rd Rn := by
    exact NativeEntryBodyAdapters.SecpLsr32.guard_at_metadata source sp Rd Rn (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) 78 profile currentInput.controls currentPins ticks post.quiet rd rn
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpLsr32.run (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) Rd Rn classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn)
      (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1) 78 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpLsr32.dispatch_at real pc Rd Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn)
    (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1) enc0 sp currentGuard 78 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn)
          (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn)
          (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78) ((decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1) (actionState (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) sp 78)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_5

theorem tail_5 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpLsr32.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpLsr32.selected Rd Rn)
    NativeEntryBodyAdapters.SecpLsr32.writes 78 (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_24 Rd Rn 63#6 32#6 state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_5 real source fetched enc0 Rd Rn rd rn profile pins input guard (budget + 1) quiet

#print axioms tail_5

theorem prefix_6 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpLsr63.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) enc0
      NativeEntryBodyAdapters.SecpLsr63.writes 78 (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 63#6 1#1 2#2 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) 78
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) sp 78 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpLsr63.Guard (actionState (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) sp 78) Rd Rn := by
    exact NativeEntryBodyAdapters.SecpLsr63.guard_at_metadata source sp Rd Rn (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) 78 profile currentInput.controls currentPins ticks post.quiet rd rn
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpLsr63.run (actionState (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) sp 78) Rd Rn classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn)
      (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 63#6 1#1 2#2 1#1) 78 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpLsr63.dispatch_at real pc Rd Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn)
    (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 63#6 1#1 2#2 1#1) enc0 sp currentGuard 78 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn)
          (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 63#6 1#1 2#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) sp 78) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn)
          (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 63#6 1#1 2#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) sp 78) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) sp 78) ((decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 63#6 1#1 2#2 1#1) (actionState (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) sp 78)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_6

theorem tail_6 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpLsr63.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn)
    NativeEntryBodyAdapters.SecpLsr63.writes 78 (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 63#6 1#1 2#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_24 Rd Rn 63#6 63#6 state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_6 real source fetched enc0 Rd Rn rd rn profile pins input guard (budget + 1) quiet

#print axioms tail_6

theorem prefix_7 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpAdcZZ.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) enc0
      NativeEntryBodyAdapters.SecpAdcZZ.writes 6 (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd 31#5 31#5 0#1 0#1 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) 6
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) sp 6 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpAdcZZ.Guard (actionState (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) sp 6) Rd := by
    exact NativeEntryBodyAdapters.SecpAdcZZ.guard_at_metadata source sp Rd (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) 6 profile currentInput.controls currentPins ticks post.quiet rd
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpAdcZZ.run (actionState (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) sp 6) Rd classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd)
      (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd 31#5 31#5 0#1 0#1 1#1) 6 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpAdcZZ.dispatch_at real pc Rd t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd)
    (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd 31#5 31#5 0#1 0#1 1#1) enc0 sp currentGuard 6 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd)
          (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd 31#5 31#5 0#1 0#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) sp 6) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd)
          (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd 31#5 31#5 0#1 0#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) sp 6) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) sp 6) ((decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd 31#5 31#5 0#1 0#1 1#1) (actionState (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) sp 6)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_7

theorem tail_7 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5) (rd : Rd.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpAdcZZ.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpAdcZZ.selected Rd)
    NativeEntryBodyAdapters.SecpAdcZZ.writes 6 (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd 31#5 31#5 0#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_0 Rd 31#5 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_7 real source fetched enc0 Rd rd profile pins input guard (budget + 1) quiet

#print axioms tail_7

theorem prefix_8 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rn : BitVec 5) (rn : Rn.toNat < 31)
    (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) enc0
      NativeEntryBodyFlag.SecpAdcsZR.writes 7 (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry 31#5 Rn 31#5 1#1 0#1 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) 7
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) sp 7 ticks post.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) 7
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have classGuard : NativeEntryBodyFlag.SecpAdcsZR.Guard (actionState (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) sp 7) Rn := by
    constructor <;> first | assumption | exact metaPins.el | exact metaPins.nrw | exact metaPins.f4 | exact metaPins.spe | (show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype) | (show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn)
  obtain ⟨fin, action, memRun, eventsRun, actFrame, _, frame, finalQuiet⟩ :=
    NativeEntryBodyFlag.SecpAdcsZR.run (actionState (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) sp 7) Rn classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn)
      (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry 31#5 Rn 31#5 1#1 0#1 1#1) 7 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpAdcsZR.dispatch_at real pc Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn)
    (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry 31#5 Rn 31#5 1#1 0#1 1#1) enc0 sp currentGuard 7 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn)
          (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry 31#5 Rn 31#5 1#1 0#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) sp 7) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn)
          (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry 31#5 Rn 31#5 1#1 0#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) sp 7) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) sp 7) ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry 31#5 Rn 31#5 1#1 0#1 1#1) (actionState (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) sp 7)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_8

theorem tail_8 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rn : BitVec 5) (rn : Rn.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn)
    NativeEntryBodyFlag.SecpAdcsZR.writes 7 (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry 31#5 Rn 31#5 1#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_1 31#5 Rn 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_8 real source fetched enc0 Rn rn pins input guard (budget + 1) quiet

#print axioms tail_8

theorem prefix_9 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) enc0
      NativeEntryBodyFlag.SecpAddsZR.writes 15 (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn 0#6 Rm 0#2 1#1 0#1 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) 15
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) sp 15 ticks post.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) 15
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have classGuard : NativeEntryBodyFlag.SecpAddsZR.Guard (actionState (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) sp 15) Rn Rm := by
    constructor <;> first | assumption | exact metaPins.el | exact metaPins.nrw | exact metaPins.f4 | exact metaPins.spe | (show sp.regs.PSTATE.BTYPE = 0#2; rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype) | (show sp.regs.BTypeNext = 0#2; exact (PMUFrame.of_E20 post.frame).btn.trans pins.btn)
  obtain ⟨fin, action, memRun, eventsRun, actFrame, _, frame, finalQuiet⟩ :=
    NativeEntryBodyFlag.SecpAddsZR.run (actionState (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) sp 15) Rn Rm classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm)
      (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn 0#6 Rm 0#2 1#1 0#1 1#1) 15 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpAddsZR.dispatch_at real pc Rn Rm t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm)
    (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn 0#6 Rm 0#2 1#1 0#1 1#1) enc0 sp currentGuard 15 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm)
          (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn 0#6 Rm 0#2 1#1 0#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) sp 15) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm)
          (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn 0#6 Rm 0#2 1#1 0#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) sp 15) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) sp 15) ((decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn 0#6 Rm 0#2 1#1 0#1 1#1) (actionState (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) sp 15)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_9

theorem tail_9 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
   
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpAddsZR.selected Rn Rm)
    NativeEntryBodyFlag.SecpAddsZR.writes 15 (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn 0#6 Rm 0#2 1#1 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_4 31#5 Rn 0#6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_9 real source fetched enc0 Rn Rm rn rm pins input guard (budget + 1) quiet

#print axioms tail_9

theorem prefix_10 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpAnd64.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0
      NativeEntryBodyAdapters.SecpAnd64.writes 48 (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 0#2 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) 48
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpAnd64.Guard (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) Rd Rn Rm := by
    exact NativeEntryBodyAdapters.SecpAnd64.guard_at_metadata source sp Rd Rn Rm (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) 48 profile currentInput.controls currentPins ticks post.quiet rd rn rm
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpAnd64.run (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) Rd Rn Rm classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm)
      (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 0#2 1#1) 48 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpAnd64.dispatch_at real pc Rd Rn Rm t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm)
    (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 0#2 1#1) enc0 sp currentGuard 48 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm)
          (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 0#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm)
          (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 0#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48) ((decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 0#2 1#1) (actionState (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) sp 48)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_10

theorem tail_10 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpAnd64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpAnd64.selected Rd Rn Rm)
    NativeEntryBodyAdapters.SecpAnd64.writes 48 (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 0#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_6 Rd Rn 0#6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_10 real source fetched enc0 Rd Rn Rm rd rn rm profile pins input guard (budget + 1) quiet

#print axioms tail_10

theorem prefix_11 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpCsel1.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) enc0
      NativeEntryBodyAdapters.SecpCsel1.writes 187 (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 1#4 31#5 0#1 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) 187
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) sp 187 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpCsel1.Guard (actionState (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) sp 187) Rd Rn := by
    exact NativeEntryBodyAdapters.SecpCsel1.guard_at_metadata source sp Rd Rn (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) 187 profile currentInput.controls currentPins ticks post.quiet rd rn
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpCsel1.run (actionState (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) sp 187) Rd Rn classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn)
      (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 1#4 31#5 0#1 1#1) 187 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpCsel1.dispatch_at real pc Rd Rn t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn)
    (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 1#4 31#5 0#1 1#1) enc0 sp currentGuard 187 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn)
          (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 1#4 31#5 0#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) sp 187) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn)
          (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 1#4 31#5 0#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) sp 187) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) sp 187) ((decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 1#4 31#5 0#1 1#1) (actionState (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) sp 187)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_11

theorem tail_11 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpCsel1.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpCsel1.selected Rd Rn)
    NativeEntryBodyAdapters.SecpCsel1.writes 187 (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 1#4 31#5 0#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_8 Rd Rn 31#5 state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_11 real source fetched enc0 Rd Rn rd rn profile pins input guard (budget + 1) quiet

#print axioms tail_11

theorem prefix_12 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpEor64.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) enc0
      NativeEntryBodyAdapters.SecpEor64.writes 53 (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 2#2 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) 53
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) sp 53 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpEor64.Guard (actionState (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) sp 53) Rd Rn Rm := by
    exact NativeEntryBodyAdapters.SecpEor64.guard_at_metadata source sp Rd Rn Rm (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) 53 profile currentInput.controls currentPins ticks post.quiet rd rn rm
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpEor64.run (actionState (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) sp 53) Rd Rn Rm classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm)
      (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 2#2 1#1) 53 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpEor64.dispatch_at real pc Rd Rn Rm t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm)
    (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 2#2 1#1) enc0 sp currentGuard 53 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm)
          (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 2#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) sp 53) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm)
          (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 2#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) sp 53) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) sp 53) ((decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 2#2 1#1) (actionState (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) sp 53)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_12

theorem tail_12 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpEor64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpEor64.selected Rd Rn Rm)
    NativeEntryBodyAdapters.SecpEor64.writes 53 (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 2#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_14 Rd Rn 0#6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_12 real source fetched enc0 Rd Rn Rm rd rn rm profile pins input guard (budget + 1) quiet

#print axioms tail_12

theorem prefix_13 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpOrr64.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) enc0
      NativeEntryBodyAdapters.SecpOrr64.writes 55 (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 1#2 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) 55
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) sp 55 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpOrr64.Guard (actionState (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) sp 55) Rd Rn Rm := by
    exact NativeEntryBodyAdapters.SecpOrr64.guard_at_metadata source sp Rd Rn Rm (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) 55 profile currentInput.controls currentPins ticks post.quiet rd rn rm
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpOrr64.run (actionState (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) sp 55) Rd Rn Rm classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm)
      (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 1#2 1#1) 55 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpOrr64.dispatch_at real pc Rd Rn Rm t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm)
    (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 1#2 1#1) enc0 sp currentGuard 55 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm)
          (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 1#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) sp 55) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm)
          (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 1#2 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) sp 55) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) sp 55) ((decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 1#2 1#1) (actionState (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) sp 55)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_13

theorem tail_13 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpOrr64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpOrr64.selected Rd Rn Rm)
    NativeEntryBodyAdapters.SecpOrr64.writes 55 (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn 0#6 Rm 0#1 0#2 1#2 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_19 Rd Rn 0#6 Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_13 real source fetched enc0 Rd Rn Rm rd rn rm profile pins input guard (budget + 1) quiet

#print axioms tail_13

theorem prefix_14 (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpSbc64.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched)
    (guard : MetadataGuard fetched) (ticks : Nat) (quiet : HookQuiet ticks fetched) :
    Nonempty (TranslateSpan.DefaultScalarTrace.ActionPrefix real source fetched (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0
      NativeEntryBodyAdapters.SecpSbc64.writes 8 (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) ticks) := by
  obtain ⟨sp, hook, post⟩ := Owner.spec_rule ticks fetched quiet
  have currentGuard := guard.after_E20 post.frame
  have el : fetched.regs.PSTATE.EL = 0#2 := by
    rw [← input.ps]
    exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp post.frame el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) 8
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8 ticks post.quiet
  have currentPins := e20_pins fetched sp pins post.frame
  have classGuard : NativeEntryBody.SecpSbc64.Guard (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) Rd Rn Rm := by
    exact NativeEntryBodyAdapters.SecpSbc64.guard_at_metadata source sp Rd Rn Rm (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) 8 profile currentInput.controls currentPins ticks post.quiet rd rn rm
  obtain ⟨fin, action, projection, frame, finalQuiet⟩ :=
    NativeEntryBodyContract.SecpSbc64.run (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) Rd Rn Rm classGuard ticks metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm)
      (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) 8 := by
    intro pc t see
    exact NativeEntryBodyDispatch.SecpSbc64.dispatch_at real pc Rd Rn Rm t (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm)
    (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) enc0 sp currentGuard 8 (by decide) dispatch
  have actualPrefix : nativeTail real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 fin := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm)
          (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) enc0 fin :=
        action_boundary real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm)
          (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) enc0
          (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) fin action
  have result : fin = resSt (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8) ((decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) (actionState (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) sp 8)) := by
    rw [action]
    rfl
  exact ⟨⟨sp, fin, hook, metadataInput, actualPrefix, frame, finalQuiet, result⟩⟩

#print axioms prefix_14

theorem tail_14 (real : Type) [Sail.SailReal real]
    (source : NativeState)
    (Rd : BitVec 5)
    (Rn : BitVec 5)
    (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (profile : NativeEntryBodyAdapters.SecpSbc64.Profile source)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) 31 12 == 879088#20) = false) :
    TranslateSpan.DefaultScalarTrace.TailChoiceAt real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm) := by
  classical
  apply TranslateSpan.DefaultScalarTrace.tail_choice_of_nonempty_prefix real source (NativeEntryBodyDispatch.SecpSbc64.selected Rd Rn Rm)
    NativeEntryBodyAdapters.SecpSbc64.writes 8 (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1) noEret
  · intro state input value after run
    exact TranslateScalarTagCheck.Actions.action_21 Rd Rn Rm state value after run
  · intro fetched enc0 budget pins input guard quiet
    exact prefix_14 real source fetched enc0 Rd Rn Rm rd rn rm profile pins input guard (budget + 1) quiet

#print axioms tail_14

end TranslateScalarTagCheck.Secp
