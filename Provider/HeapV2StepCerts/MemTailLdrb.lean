import HeapV2StepCerts.ActionTransport
import Bridge.CruxGenGuarded.OwnerMetadata
import Bridge.CruxGenGuarded.Action
import Bridge.CruxGenGuarded.EntryControls
import Bridge.CruxGenGuarded.EntryTraffic
import NativeEntryInput.Input
import NativeEntryBodyMem.Ldrb
import NativeEntryBodyDispatch.Ldrb
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to HeapV2StepCerts.MemTailLdrbLNSym.
namespace HeapV2StepCerts.MemTail

-- Memory ((B)): memory ClassTail for Ldrb (post-index), over

-- NativeEntryBodyMem.Ldrb.run at the actual action state. Every memory premise is taken at

-- the FETCHED state and transported (ActionTransport); events are split into a Covered delta.

theorem memRead_covered (pa : Nat) (n : Nat) (va : Nat) (t : Bool) :
    ArmCertCTOrdered.OrderedEventV2.Covered
      #[Event.memRead pa n (some va) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) t] := by
  intro e he
  simp only [List.mem_singleton] at he
  subst he
  rfl

theorem mem_tail_Ldrb (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (source fetched : NativeState) (enc0 : __InstrEnc) (imm9 : BitVec 9) (Rn Rt : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) 31 12 == 879088#20) = false)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (current : CurrentS1At spec config rows fetched)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemReadD2.AccDR2 acc →
      domain (MemClass.Ldrb.query fetched Rn acc) ∧
      ∃ data : S1AccessData spec config rows (MemClass.Ldrb.query fetched Rn acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Ldrb.query fetched Rn acc) data fetched)
    (mode : HostEL0ModeAt fetched.regs) (debug : ExistingE11DebugAt fetched.regs)
    (post : MemM1.MemReadD2.PostRegs2 fetched.regs)
    (hEL3A64 : fetched.regs.FeatureImpl[7] = true) (hNoEL3A32 : fetched.regs.FeatureImpl[3] = false)
    (hTME : fetched.regs.FeatureImpl[227] = false) (dcache : currentDCache fetched.regs = true)
    (pa : BitVec 56) (mapped : mapping (MemClass.Ldrb.base fetched Rn) = some pa.toNat)
    (mmio : MemM1.MemReadIF.NotMMIO pa)
    (v : BitVec 8) (byte : fetched.mem[pa.toNat]? = some v)
    (outside : ¬ (rowsFootprint spec.imageRows).byte pa.toNat)
    (raw : RawImageAt spec.imageRows fetched.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT fetched.regs} acc spec.imageRows = true) :
    ∃ (sp a fin : NativeState) (written : Nat → Prop) (delta : Array Event),
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame NativeEntryBodyMem.Ldrb.writes
        (actionState (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) sp 631) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      WritesOnly written (fun x => fetched.mem[x]?) (fun x => fin.mem[x]?) ∧
      Separated (rowsFootprint spec.imageRows).byte written ∧
      fin.events = fetched.events ++ delta ∧ ArmCertCTOrdered.OrderedEventV2.Covered delta ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = source.regs._PC + 4#64 ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs := by
  obtain ⟨sp, hook, postS⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) 631
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) sp 631 (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) 631
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  -- transport the memory premises to the action state
  have actMem := ActionTransport.mem (w := NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) (K := 631) postS.mem
  have qEq : ∀ acc, MemClass.Ldrb.query (actionState (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) sp 631) Rn acc =
      MemClass.Ldrb.query fetched Rn acc := by
    intro acc; simp only [MemClass.Ldrb.query, MemClass.Ldrb.base, ActionTransport.gpr e20]
  have bEq : MemClass.Ldrb.base (actionState (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) sp 631) Rn =
      MemClass.Ldrb.base fetched Rn := by
    simp only [MemClass.Ldrb.base, ActionTransport.gpr e20]
  have feat := ActionTransport.feat (w := NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) (K := 631) e20
  obtain ⟨t, ok, _, hm, he, af, _, _, frame, tq⟩ :=
    NativeEntryBodyMem.Ldrb.run spec config rows mapping
      (actionState (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) sp 631) imm9 Rn Rt hRn hRt hRnt
      (ActionTransport.current e20 postS.mem current)
      (fun acc a0 a2 => by
        rw [qEq acc]
        obtain ⟨member, data, access⟩ := perAcc acc a0 a2
        exact ⟨member, data, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 mode) (ActionTransport.debug e20 debug) (ActionTransport.post2 e20 post)
      (feat ▸ hEL3A64) (feat ▸ hNoEL3A32) (feat ▸ hTME) (ActionTransport.dcache e20 dcache)
      pa (bEq ▸ mapped) mmio v (by rw [actMem]; exact byte) outside (by rw [actMem]; exact raw)
      (fun acc a0 => by rw [ActionTransport.haft e20]; exact noUpd acc a0)
      (budget + 1) metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9)
      (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2) 631 := by
    intro pc u see
    exact NativeEntryBodyDispatch.Ldrb.dispatch_at real pc Rt Rn imm9 u (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9)
    (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2) enc0 sp
    currentGuard 631 (by decide) dispatch
  have nativePrefix : nativeTail real source (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) enc0 fetched =
      nativeAfterAction real source (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) enc0 t := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) enc0 fetched =
          afterSpecPmu real source (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9)
          (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2) enc0
          (actionState (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) sp 631) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) enc0 t :=
        action_boundary real source (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9)
          (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2) enc0
          (actionState (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) sp 631) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) enc0 t budget tq
      actionPins next enc eret actionIT actionSS
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  have finMem : fin.mem = fetched.mem := output.mem.trans (hm.trans actMem)
  have actEvents : (actionState (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) sp 631).events = fetched.events :=
    (actionState_events (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) sp 631).trans postS.events
  obtain ⟨info, walk, leaf, middle, address, traffic, _, _, _, _, after⟩ := he
  rw [actEvents] at traffic
  obtain ⟨d, hd, cov⟩ := EntryTraffic.translate_delta_covered fetched.events info walk leaf middle address traffic
  refine ⟨sp, t, fin, fun _ => False, d ++ #[Event.memRead pa.toNat 1
      (some (MemClass.Ldrb.base (actionState (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) sp 631) Rn).toNat)
      (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false],
    hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [finMem],
    EntryBtiNext.no_writes_separated _, ?_, EntryTraffic.covered_append cov (memRead_covered _ _ _ _),
    gic, ?_, nonProj⟩
  · rw [events, after, Array.push_eq_append, hd, Array.append_assoc]
  · simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc

end HeapV2StepCerts.MemTail

