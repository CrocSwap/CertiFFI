import TranslateSpan.DefaultClass
import NativeTagCheck.BeforeFetch
import TagCheckFrames.Fetch
import TranslateSpan.ClassMTE2Frame

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeMteTagCheck ArmCertWalk ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option Elab.async false

namespace TranslateSpan.DefaultScalarTrace

theorem resSt_choice {α : Type} (action : SailM α) (s : NativeState)
    (law : ∀ value after, action s = .ok value after → ChoiceDelta s after 0) :
    ChoiceDelta s (resSt s (action s)) 0 := by
  cases run : action s with
  | ok value after => exact law value after run
  | error error after => exact choice_delta_refl s

/-- The boundary witnesses retained by the existing constructive class roots. -/
structure ActionPrefix (real : Type) [Sail.SailReal real]
    (source fetched : NativeState) (word : BitVec 32) (enc : __InstrEnc)
    (writes : NativeEntry.Effects.Writes) (see : Int) (action : SailM Unit)
    (ticks : Nat) where
  sp : NativeState
  after : NativeState
  hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp
  input : NativeEntryInput.Input source (actionState word sp see)
  boundary : nativeTail real source word enc fetched = nativeAfterAction real source word enc after
  frame : NativeEntryContract.Frame writes (actionState word sp see) after
  quiet : HookQuiet ticks after
  result : after = resSt (actionState word sp see) (action (actionState word sp see))

def TailChoiceAt (real : Type) [Sail.SailReal real] (source : NativeState)
    (word : BitVec 32) : Prop :=
  ∀ (fetched : NativeState) (enc : __InstrEnc) (budget : Nat),
    StepPins fetched → NativeEntryInput.Input source fetched → MetadataGuard fetched →
    HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true →
    ∀ fin, nativeTail real source word enc fetched = .ok () fin → ChoiceDelta fetched fin 0

theorem tail_choice_of_prefix (real : Type) [Sail.SailReal real]
    (source : NativeState) (word : BitVec 32) (writes : NativeEntry.Effects.Writes)
    (see : Int) (action : SailM Unit)
    (noEret : (Sail.BitVec.extractLsb word 31 12 == 879088#20) = false)
    (law : ∀ state, NativeEntryInput.Input source state →
      ∀ value after, action state = .ok value after → ChoiceDelta state after 0)
    (progress : ∀ fetched enc budget, StepPins fetched → NativeEntryInput.Input source fetched →
      MetadataGuard fetched → HookQuiet (budget + 1) fetched →
      ActionPrefix real source fetched word enc writes see action (budget + 1)) :
    TailChoiceAt real source word := by
  intro fetched enc budget pins input guard quiet it ss fin run
  have progressResult := progress fetched enc budget pins input guard quiet
  have post := entry_spec_post fetched progressResult.sp (budget + 1) quiet progressResult.hook
  have metadataPins := entryPins_at_metadata progressResult.sp word see
    (NativeEntryTail.EntryPins.after_E20 fetched progressResult.sp
      (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have actionPins := NativeEntryTail.EntryPins.after_action progressResult.frame metadataPins
  have encoding : progressResult.after.regs.__ThisInstrEnc = .__A64 := progressResult.frame.enc
  have eret :
      (Sail.BitVec.extractLsb (progressResult.after.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [progressResult.frame.b32]
    exact noEret
  have actionIT : progressResult.after.regs.ShouldAdvanceIT = false :=
    progressResult.frame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : progressResult.after.regs.ShouldAdvanceSS = true :=
    progressResult.frame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  have actionDelta : ChoiceDelta (actionState word progressResult.sp see) progressResult.after 0 := by
    rw [progressResult.result]
    exact resSt_choice action _ (law _ progressResult.input)
  have prefixDelta : ChoiceDelta fetched progressResult.after 0 := by
    simpa only [Nat.add_zero] using choice_delta_trans
      (choice_delta_trans
        (NativeTagCheck.spec_choice_of_run (budget + 1) fetched progressResult.sp quiet progressResult.hook)
        (NativeTagCheck.metadata_choice word progressResult.sp see)) actionDelta
  have tailDelta := NativeTagCheck.after_action_choice_of_run real source word enc
    progressResult.after fin budget progressResult.quiet actionPins encoding eret actionIT actionSS
    (progressResult.boundary.symm.trans run)
  simpa only [Nat.add_zero] using choice_delta_trans prefixDelta tailDelta

/-- `tail_choice_of_prefix` from a merely inhabited prefix (no data choice; Prop goal). -/
theorem tail_choice_of_nonempty_prefix (real : Type) [Sail.SailReal real]
    (source : NativeState) (word : BitVec 32) (writes : NativeEntry.Effects.Writes)
    (see : Int) (action : SailM Unit)
    (noEret : (Sail.BitVec.extractLsb word 31 12 == 879088#20) = false)
    (law : ∀ state, NativeEntryInput.Input source state →
      ∀ value after, action state = .ok value after → ChoiceDelta state after 0)
    (progress : ∀ fetched enc budget, StepPins fetched → NativeEntryInput.Input source fetched →
      MetadataGuard fetched → HookQuiet (budget + 1) fetched →
      Nonempty (ActionPrefix real source fetched word enc writes see action (budget + 1))) :
    TailChoiceAt real source word := by
  intro fetched enc budget pins input guard quiet it ss fin run
  obtain ⟨progressResult⟩ := progress fetched enc budget pins input guard quiet
  have post := entry_spec_post fetched progressResult.sp (budget + 1) quiet progressResult.hook
  have metadataPins := entryPins_at_metadata progressResult.sp word see
    (NativeEntryTail.EntryPins.after_E20 fetched progressResult.sp
      (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame)
  have actionPins := NativeEntryTail.EntryPins.after_action progressResult.frame metadataPins
  have encoding : progressResult.after.regs.__ThisInstrEnc = .__A64 := progressResult.frame.enc
  have eret :
      (Sail.BitVec.extractLsb (progressResult.after.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [progressResult.frame.b32]
    exact noEret
  have actionIT : progressResult.after.regs.ShouldAdvanceIT = false :=
    progressResult.frame.it.trans ((PMUFrame.of_E20 post.frame).it.trans it)
  have actionSS : progressResult.after.regs.ShouldAdvanceSS = true :=
    progressResult.frame.ss.trans ((PMUFrame.of_E20 post.frame).ss.trans ss)
  have actionDelta : ChoiceDelta (actionState word progressResult.sp see) progressResult.after 0 := by
    rw [progressResult.result]
    exact resSt_choice action _ (law _ progressResult.input)
  have prefixDelta : ChoiceDelta fetched progressResult.after 0 := by
    simpa only [Nat.add_zero] using choice_delta_trans
      (choice_delta_trans
        (NativeTagCheck.spec_choice_of_run (budget + 1) fetched progressResult.sp quiet progressResult.hook)
        (NativeTagCheck.metadata_choice word progressResult.sp see)) actionDelta
  have tailDelta := NativeTagCheck.after_action_choice_of_run real source word enc
    progressResult.after fin budget progressResult.quiet actionPins encoding eret actionIT actionSS
    (progressResult.boundary.symm.trans run)
  simpa only [Nat.add_zero] using choice_delta_trans prefixDelta tailDelta

theorem fetched_of_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : NativeAccess.AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (word : BitVec 32) (source fin : NativeState)
    (core : DefaultMTE2.Core spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k source)
    (ob : FetchObligations spec config rows mapping word source)
    (stepRun : modelStep real source = .ok () fin) :
    ∃ (fetched : NativeState) (enc : __InstrEnc),
      StepPins fetched ∧ NativeEntryInput.Input source fetched ∧ MetadataGuard fetched ∧
      HookQuiet ((budget - (k + 1)) + 1) fetched ∧
      fetched.regs.ShouldAdvanceIT = false ∧ fetched.regs.ShouldAdvanceSS = true ∧
      nativeTail real source word enc fetched = .ok () fin ∧ ChoiceDelta source fetched 0 := by
  have pins := NativeEntryTail.EntryPins.of_scalar source core.v1.pins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ :=
    before_fetch_facts source pins core.v1.features core.v1.debug
  obtain ⟨acc, word', fetched, address, faultOut, translated, data, actualAcc, run, clean,
      bytes, fregs, _fmem, _fev, _current, _, fetchChoice,
      _info, _walk, _leaf, _middle, _len, _traffic, _tev, _noUpd⟩ :=
    native_fetch_current_preserving_events_choice spec config rows mapping (beforeFetchState source)
      step el (pc_low_of_placement _ base (offset k) core.v1.pc page aligned) il
      core.v1.current mode step.b0 ⟨e11.mde,e11.hde⟩ spe
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc
  have wordEqual := ob.code acc data.leafLevel data.view faultOut address translated word' clean bytes
  subst wordEqual
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have regs : fetched.regs = FetchedRegs acc (translateCurrent out) source := by
    rw [fregs,translatedRegs,ob.rawOf acc]
    rfl
  have emuFinal : fetched.regs.__emulator_termination_opcode = none := by
    rw [regs]
    unfold FetchedRegs fetchGuardRegs
    split <;> exact emu0
  obtain ⟨enc, boundary⟩ := entry_prefetch_boundary real source fetched _ pins core.v1.gic run emuFinal
  have fetchedPins := EntryClassNext.fetched_steppins acc (translateCurrent out) source fetched
    core.v1.pins regs
  have input := fetched_input acc (translateCurrent out) source fetched pins.el regs
  have quiet : HookQuiet ((budget - (k + 1)) + 1) source := by
    have equal : budget - (k + 1) + 1 = budget - k := by omega
    rw [equal]
    exact core.v1.quiet
  obtain ⟨guard, fetchedQuiet, it, ss⟩ :=
    fetched_rest acc (translateCurrent out) source fetched _ pins quiet regs
  have tailRun : nativeTail real source word' enc fetched = .ok () fin := boundary.symm.trans stepRun
  refine ⟨fetched,enc,fetchedPins,input,guard,fetchedQuiet,it,ss,tailRun,?_⟩
  simpa only [Nat.add_zero] using choice_delta_trans
    (NativeTagCheck.before_fetch_choice source) fetchChoice

theorem step_choice (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : NativeAccess.AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (word : BitVec 32) (source fin : NativeState)
    (core : DefaultMTE2.Core spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k source)
    (ob : FetchObligations spec config rows mapping word source)
    (tailChoice : TailChoiceAt real source word)
    (stepRun : modelStep real source = .ok () fin) : ChoiceDelta source fin 0 := by
  obtain ⟨fetched,enc,pins,input,guard,quiet,it,ss,run,delta⟩ :=
    fetched_of_step real spec config rows mapping consumer scope image loadBase base offset budget
      profile catalogue k room page aligned word source fin core ob stepRun
  have tailDelta := tailChoice fetched enc (budget - (k + 1)) pins input guard quiet it ss fin run
  simpa only [Nat.add_zero] using choice_delta_trans delta tailDelta

theorem srcVal_of_input (source fetched : NativeState)
    (input : NativeEntryInput.Input source fetched) :
    ArmCertValue.srcVal fetched = ArmCertValue.srcVal source := by
  funext value
  cases value with
  | reg r =>
    cases r with
    | sp => exact input.sp.symm
    | x index =>
      exact congrArg (fun registers => registers[index.val]) input.gpr.symm
  | flag index => simp only [ArmCertValue.srcVal, ArmCertValue.flagWord, ← input.ps]
  | lit value => rfl

theorem locationValue_of_input (source fetched : NativeState)
    (input : NativeEntryInput.Input source fetched) (location : ArmCertValue.Expr.Location) :
    ArmCertValue.Expr.locationValue fetched location = ArmCertValue.Expr.locationValue source location := by
  cases location with
  | reg r => exact congrFun (srcVal_of_input source fetched input) (.reg r)
  | flag index => exact congrFun (srcVal_of_input source fetched input) (.flag index)

theorem outputs_of_input (source fetched fin : NativeState)
    (input : NativeEntryInput.Input source fetched)
    (outputs : List (ArmCertValue.Expr.Location × ArmCertValue.Expr.Term))
    (holds : ArmCertValue.Expr.OutputHolds outputs fetched fin) :
    ArmCertValue.Expr.OutputHolds outputs source fin := by
  constructor
  · intro location term member
    rw [← srcVal_of_input source fetched input]
    exact holds.1 location term member
  · intro location absent
    exact (holds.2 location absent).trans (locationValue_of_input source fetched input location)

theorem outputs_of_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (profile : NativeAccess.AccessProfile) (catalogue : ControlCatalogue) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (word : BitVec 32) (source fin : NativeState)
    (core : DefaultMTE2.Core spec config rows mapping consumer scope image loadBase
      base offset budget profile catalogue k source)
    (ob : FetchObligations spec config rows mapping word source)
    (outputs : List (ArmCertValue.Expr.Location × ArmCertValue.Expr.Term))
    (nativeOutputs : ∀ fetched enc ticks, StepPins fetched → NativeEntryInput.Input source fetched →
      MetadataGuard fetched → HookQuiet (ticks + 1) fetched →
      fetched.regs.ShouldAdvanceIT = false → fetched.regs.ShouldAdvanceSS = true →
      nativeTail real source word enc fetched = .ok () fin →
      ArmCertValue.Expr.OutputHolds outputs fetched fin)
    (stepRun : modelStep real source = .ok () fin) : ArmCertValue.Expr.OutputHolds outputs source fin := by
  obtain ⟨fetched,enc,pins,input,guard,quiet,it,ss,run,_delta⟩ :=
    fetched_of_step real spec config rows mapping consumer scope image loadBase base offset budget
      profile catalogue k room page aligned word source fin core ob stepRun
  exact outputs_of_input source fetched fin input outputs
    (nativeOutputs fetched enc (budget - (k + 1)) pins input guard quiet it ss run)

#print axioms fetched_of_step
#print axioms srcVal_of_input
#print axioms locationValue_of_input
#print axioms outputs_of_input
#print axioms outputs_of_step
#print axioms step_choice
#print axioms resSt_choice
#print axioms tail_choice_of_prefix
end TranslateSpan.DefaultScalarTrace
