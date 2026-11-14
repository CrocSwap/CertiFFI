import DefaultActionControls
-- Exact ordered records and NZCV frames for the six heap-v2 memory tails.
import HeapDefaultTagCheck.MemTail
import HeapDefaultTagCheck.BodyMem
import HeapV2StepCerts.MemHolds
import HeapV2StepCerts.DataRecs
import HeapV2StepCerts.Flags
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
open NativeMteTagCheck
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ReleaseProfile.DefaultHeapSavedTail
open HeapV2StepCerts
open HeapV2StepCerts.MemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)

theorem mem_tailP_Stp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (source fetched : NativeState) (enc0 : __InstrEnc) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (current : CurrentS1At spec config rows fetched)
    (perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      domain (MemClass.Stp.query fetched imm7 acc) ∧
      (∃ data : S1AccessData spec config rows (MemClass.Stp.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Stp.query fetched imm7 acc) data fetched))
    (mode : HostEL0ModeAt fetched.regs) (debug : ExistingE11DebugAt fetched.regs)
    (post : MemM1.MemReadD.PostRegs fetched.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue fetched)
    (statusRows : TagStatusRows fetched (fetched.choiceOcc.getD 1354 0) 1)
    (hEL3A64 : fetched.regs.FeatureImpl[7] = true) (hNoEL3A32 : fetched.regs.FeatureImpl[3] = false)
    (hTME : fetched.regs.FeatureImpl[227] = false) (lse2 : fetched.regs.FeatureImpl[111] = true)
    (dcache : currentDCache fetched.regs = true)
    (hsp : fetched.regs.SP_EL0.toNat % 16 = 0) (hal : (ArmCertMem.LdpEval.ldpAddr fetched imm7).toNat % 16 = 0)
    (pa : BitVec 56) (mapped : mapping (ArmCertMem.LdpEval.ldpAddr fetched imm7) = some pa.toNat)
    (mmio : MemM1.MemReadIF.NotMMIO pa)
    (outside : ∀ i < 16, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i))
    (D : Nat → Prop) (inD : ∀ i < 16, D (pa.toNat + i))
    (raw : RawImageAt spec.imageRows fetched.mem)
    (noUpd : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      NoUpdateRows {spec.params with haft := hostHAFT fetched.regs} acc spec.imageRows = true) :
    ∃ (sp a fin : NativeState) (written : Nat → Prop) (delta : Array Event) (draws : Nat),
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame NativeEntryBodyMem.Stp.writes (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      WritesOnly written (fun x => fetched.mem[x]?) (fun x => fin.mem[x]?) ∧
      Separated (rowsFootprint spec.imageRows).byte written ∧
      fin.events = fetched.events ++ delta ∧ ArmCertCTOrdered.OrderedEventV2.Covered delta ∧
      ((spec.logicalRows.map (·.logical)).Nodup →
        delta.toList.map ArmCertCTOrdered.OrderedEventV2.record = DataRecs.dataRecs spec (ArmCertMem.LdpEval.ldpAddr fetched imm7) true 16) ∧
      Flags.nzcv fin.regs = Flags.nzcv fetched.regs ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = source.regs._PC + 4#64 ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs ∧
      (∀ a : Nat, (fetched.mem[a]?).isSome → (fin.mem[a]?).isSome) ∧
      (RegBind.Holds ([]) fetched fin ∧ (∀ x, written x → D x) ∧
            (∀ i < 16, fin.mem[pa.toNat + i]? = some (MemM1.MemWriteD4.wbyte (ArmCertMem.StpEval.stpData fetched Rt Rt2) i))) ∧ ChoiceDelta fetched fin draws ∧ draws ≤ 1 := by
  obtain ⟨sp, hook, postS⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 617
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617 (budget + 1) postS.quiet
  have actionPrefixDelta : ChoiceDelta fetched (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617) 0 := by
    simpa only [Nat.add_zero] using choice_delta_trans
      (NativeTagCheck.spec_choice_of_run (budget+1) fetched sp quiet hook)
      (NativeTagCheck.metadata_choice (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617)
  have actionRows : TagStatusRows (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617)
      ((actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617).choiceOcc.getD 1354 0) 1 := by
    unfold TagStatusRows at *
    rw [actionPrefixDelta.1,actionPrefixDelta.2,Nat.add_zero]
    exact statusRows
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 617
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (K := 617) postS.mem
  have feat := ActionTransport.feat (w := NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (K := 617) e20
  have gprEq := ActionTransport.gpr (w := NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (K := 617) e20
  have spEq := ActionTransport.sp0 (w := NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (K := 617) e20
  have actEvents : (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617).events = fetched.events :=
    (actionState_events (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617).trans postS.events
  obtain ⟨t,draws,ok, hr, hmw, he, wo, sepW, af, _, _, frame,tq,actionDelta,drawBound⟩ :=
    HeapV2StepCerts.BodyMemD.Stp.runDefaultTagCheck spec config rows mapping (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617) imm7 Rt Rt2 hRt hRt2
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        have qEq : MemClass.Stp.query (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617) imm7 acc = MemClass.Stp.query fetched imm7 acc := by
          simp only [MemClass.Stp.query, ArmCertMem.LdpEval.ldpAddr, spEq]
        rw [qEq]
        obtain ⟨member, data, access⟩ := perAcc acc sh
        exact ⟨member, data, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 mode) (ActionTransport.debug e20 debug) (ActionTransport.postDefault236 e20 post) catalogue (ReleaseProfile.DefaultActionControls.default_at e20 controls) actionRows
      (feat ▸ hEL3A64) (feat ▸ hNoEL3A32) (feat ▸ hTME) (feat ▸ lse2) (ActionTransport.dcache e20 dcache)
      (by rw [spEq]; exact hsp) (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact hal)
      pa (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact mapped) mmio outside
      (by rw [actMem]; exact raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact noUpd acc sh)
      (budget + 1) metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 0#1 2#2) 617 := by
    intro pc u see
    exact NativeEntryBodyDispatch.Stp.dispatch_at real pc Rt Rt2 imm7 u (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 0#1 2#2) enc0 sp currentGuard 617 (by decide) dispatch
  have nativePrefix : nativeTail real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) enc0 fetched = nativeAfterAction real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) enc0 t := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) enc0 fetched = afterSpecPmu real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 0#1 2#2) enc0 (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) enc0 t :=
        action_boundary real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 0#1 2#2) enc0 (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) enc0 t budget tq actionPins next enc eret actionIT actionSS
  have finalDelta : ChoiceDelta fetched fin draws :=
    NativeTagCheck.native_tail_choice_of_delta real source fetched sp t fin (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) enc0 617 budget draws
      quiet hook actionDelta nativePrefix tq actionPins enc eret actionIT actionSS (nativePrefix.trans tail)
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  rw [actEvents] at he
  obtain ⟨delta, hd, cov⟩ := single_delta he (memWrite_covered _ _ _ _ _ _)
  have payload : ∀ i < 16, fin.mem[pa.toNat + i]? =
      some (MemM1.MemWriteD4.wbyte (ArmCertMem.StpEval.stpData fetched Rt Rt2) i) := by
    intro i hi
    have sd : ArmCertMem.StpEval.stpData (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617) Rt Rt2 =
        ArmCertMem.StpEval.stpData fetched Rt Rt2 := by
      unfold ArmCertMem.StpEval.stpData; rw [gprEq]
    rw [output.mem, hmw, MemM1.MemWriteD1.wfold_get, if_pos ⟨Nat.le_add_right _ _, by omega⟩,
      Nat.add_sub_cancel_left, sd]
  refine ⟨sp, t, fin, fun x => pa.toNat ≤ x ∧ x < pa.toNat + 16, delta, draws, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x hx => by show fin.mem[x]? = fetched.mem[x]?; rw [output.mem, ← actMem]; exact wo x hx, sepW, by rw [events, hd], cov,
    (fun nd => by rw [DataRecs.single_records he hd nd]; simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; rfl), (by have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20; simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]; exact h), gic, ?_, nonProj, ?_, ?_, finalDelta, drawBound⟩
  simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  exact fun a h => by rw [output.mem, hmw]; exact wfold_isSome _ _ _ _ _ (by rw [actMem]; exact h)
  exact ⟨RegBind.Holds.of_prefix (ActionTransport.gpr e20) (ActionTransport.sp0 e20) (RegBind.holds_nil _ fin (by rw [output.gpr, hr]) (by rw [output.sp, hr])), fun x h => by obtain ⟨h1, h2⟩ := (h : pa.toNat ≤ x ∧ x < pa.toNat + 16); have hx := inD (x - pa.toNat) (by omega); rwa [Nat.add_sub_cancel' h1] at hx, payload⟩

theorem mem_tailP_Ldp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (source fetched : NativeState) (enc0 : __InstrEnc) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (current : CurrentS1At spec config rows fetched)
    (perAcc : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      domain (MemClass.Ldp.query fetched imm7 acc) ∧
      ∃ data : S1AccessData spec config rows (MemClass.Ldp.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Ldp.query fetched imm7 acc) data fetched)
    (mode : HostEL0ModeAt fetched.regs) (debug : ExistingE11DebugAt fetched.regs)
    (post : MemM1.MemReadD.PostRegs fetched.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue fetched)
    (statusRows : TagStatusRows fetched (fetched.choiceOcc.getD 1354 0) 1)
    (hEL3A64 : fetched.regs.FeatureImpl[7] = true) (hNoEL3A32 : fetched.regs.FeatureImpl[3] = false)
    (hTME : fetched.regs.FeatureImpl[227] = false) (lse2 : fetched.regs.FeatureImpl[111] = true)
    (dcache : currentDCache fetched.regs = true)
    (hsp : fetched.regs.SP_EL0.toNat % 16 = 0) (hal : (ArmCertMem.LdpEval.ldpAddr fetched imm7).toNat % 16 = 0)
    (pa : BitVec 56) (mapped : mapping (ArmCertMem.LdpEval.ldpAddr fetched imm7) = some pa.toNat)
    (mmio : MemM1.MemReadIF.NotMMIO pa)
    (data : BitVec 128) (bytes : ∀ i < 16, fetched.mem[pa.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8))
    (D : Nat → Prop)
    (raw : RawImageAt spec.imageRows fetched.mem)
    (noUpd : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      NoUpdateRows {spec.params with haft := hostHAFT fetched.regs} acc spec.imageRows = true) :
    ∃ (sp a fin : NativeState) (written : Nat → Prop) (delta : Array Event) (draws : Nat),
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame NativeEntryBodyMem.Ldp.writes (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      WritesOnly written (fun x => fetched.mem[x]?) (fun x => fin.mem[x]?) ∧
      Separated (rowsFootprint spec.imageRows).byte written ∧
      fin.events = fetched.events ++ delta ∧ ArmCertCTOrdered.OrderedEventV2.Covered delta ∧
      ((spec.logicalRows.map (·.logical)).Nodup →
        delta.toList.map ArmCertCTOrdered.OrderedEventV2.record = DataRecs.dataRecs spec (ArmCertMem.LdpEval.ldpAddr fetched imm7) false 16) ∧
      Flags.nzcv fin.regs = Flags.nzcv fetched.regs ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = source.regs._PC + 4#64 ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs ∧
      (∀ a : Nat, (fetched.mem[a]?).isSome → (fin.mem[a]?).isSome) ∧
      (RegBind.Holds (RegBind.updLdp Rt Rt2) fetched fin ∧ (∀ x, written x → D x) ∧
            fin.regs.gpr[(RegBind.rk Rt2).val] = ArmCertMem.LdpEval.ldpHi data ∧
      fin.regs.gpr[(RegBind.rk Rt).val] = ArmCertMem.LdpEval.ldpLo data) ∧ ChoiceDelta fetched fin draws ∧ draws ≤ 1 := by
  obtain ⟨sp, hook, postS⟩ := Owner.spec_rule (budget + 1) fetched quiet
  have e20 := postS.frame
  have currentGuard := guard.after_E20 e20
  have el : fetched.regs.PSTATE.EL = 0#2 := by rw [← input.ps]; exact input.el0
  have currentInput := input.trans (NativeEntryInput.of_E20 fetched sp e20 el)
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) 611
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611 (budget + 1) postS.quiet
  have actionPrefixDelta : ChoiceDelta fetched (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611) 0 := by
    simpa only [Nat.add_zero] using choice_delta_trans
      (NativeTagCheck.spec_choice_of_run (budget+1) fetched sp quiet hook)
      (NativeTagCheck.metadata_choice (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611)
  have actionRows : TagStatusRows (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611)
      ((actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611).choiceOcc.getD 1354 0) 1 := by
    unfold TagStatusRows at *
    rw [actionPrefixDelta.1,actionPrefixDelta.2,Nat.add_zero]
    exact statusRows
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) 611
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (K := 611) postS.mem
  have feat := ActionTransport.feat (w := NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (K := 611) e20
  have gprEq := ActionTransport.gpr (w := NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (K := 611) e20
  have spEq := ActionTransport.sp0 (w := NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (K := 611) e20
  have actEvents : (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611).events = fetched.events :=
    (actionState_events (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611).trans postS.events
  obtain ⟨t,draws,ok, hr, hm, he, af, _, _, frame,tq,actionDelta,drawBound⟩ :=
    HeapV2StepCerts.BodyMemD.Ldp.runDefaultTagCheck spec config rows mapping (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611) imm7 Rt Rt2 hRt hRt2 hRtt
      (ActionTransport.current e20 postS.mem current)
      (fun acc sh => by
        have qEq : MemClass.Ldp.query (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611) imm7 acc = MemClass.Ldp.query fetched imm7 acc := by
          simp only [MemClass.Ldp.query, ArmCertMem.LdpEval.ldpAddr, spEq]
        rw [qEq]
        obtain ⟨member, data, access⟩ := perAcc acc sh
        exact ⟨member, data, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 mode) (ActionTransport.debug e20 debug) (ActionTransport.postDefault236 e20 post) catalogue (ReleaseProfile.DefaultActionControls.default_at e20 controls) actionRows
      (feat ▸ hEL3A64) (feat ▸ hNoEL3A32) (feat ▸ hTME) (feat ▸ lse2) (ActionTransport.dcache e20 dcache)
      (by rw [spEq]; exact hsp) (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact hal)
      pa (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact mapped) mmio data (by rw [actMem]; exact bytes)
      (by rw [actMem]; exact raw) (fun acc sh => by rw [ActionTransport.haft e20]; exact noUpd acc sh)
      (budget + 1) metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2) 611 := by
    intro pc u see
    exact NativeEntryBodyDispatch.Ldp.dispatch_at real pc Rt Rt2 imm7 u (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2) enc0 sp currentGuard 611 (by decide) dispatch
  have nativePrefix : nativeTail real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) enc0 fetched = nativeAfterAction real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) enc0 t := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) enc0 fetched = afterSpecPmu real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2) enc0 (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) enc0 t :=
        action_boundary real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2) enc0 (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) enc0 t budget tq actionPins next enc eret actionIT actionSS
  have finalDelta : ChoiceDelta fetched fin draws :=
    NativeTagCheck.native_tail_choice_of_delta real source fetched sp t fin (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) enc0 611 budget draws
      quiet hook actionDelta nativePrefix tq actionPins enc eret actionIT actionSS (nativePrefix.trans tail)
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  rw [actEvents] at he
  obtain ⟨delta, hd, cov⟩ := single_delta he (memRead_covered _ _ _ _)
  have payload : fin.regs.gpr[(RegBind.rk Rt2).val] = ArmCertMem.LdpEval.ldpHi data := by
    rw [output.gpr, hr]
    simp only [ArmCertMem.LdpEval.ldpPost, RegBind.setGpr_get]
    exact if_pos rfl
  have payloadLo : fin.regs.gpr[(RegBind.rk Rt).val] = ArmCertMem.LdpEval.ldpLo data := by
    have kv : ∀ n, n < 31 → (GPRSummary.key n).val = n := by decide
    have hne : ¬ (GPRSummary.key Rt2.toNat = RegBind.rk Rt) := by
      intro h
      apply hRtt
      apply BitVec.eq_of_toNat_eq
      have h' := congrArg Fin.val h
      simp only [RegBind.rk] at h'
      rw [kv _ hRt2, kv _ hRt] at h'
      exact h'.symm
    rw [output.gpr, hr]
    simp only [ArmCertMem.LdpEval.ldpPost, RegBind.setGpr_get]
    rw [if_neg hne, if_pos (show GPRSummary.key Rt.toNat = RegBind.rk Rt from rfl)]
  refine ⟨sp, t, fin, fun _ => False, delta, draws, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [output.mem, hm, actMem], EntryBtiNext.no_writes_separated _, by rw [events, hd], cov,
    (fun nd => by rw [DataRecs.single_records he hd nd]; simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; rfl), (by have h := frame_pres_E20 (fun x => (x.PSTATE.N, x.PSTATE.Z, x.PSTATE.C, x.PSTATE.V)) (fun x => by simp only [eraseE20]) e20; simp only [Flags.nzcv, output.n, output.zf, output.c, output.v, hr]; exact h), gic, ?_, nonProj, ?_, ?_, finalDelta, drawBound⟩
  simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc
  exact fun a h => by rw [output.mem, hm, actMem]; exact h
  exact ⟨RegBind.Holds.of_prefix (ActionTransport.gpr e20) (ActionTransport.sp0 e20) (RegBind.holds_ldp _ fin Rt Rt2 data (by rw [output.gpr, hr]) (by rw [output.sp, hr]; rfl)), fun _ h => h.elim, payload, payloadLo⟩

#print axioms mem_tailP_Stp
#print axioms mem_tailP_Ldp
end ReleaseProfile.DefaultHeapSavedTail
