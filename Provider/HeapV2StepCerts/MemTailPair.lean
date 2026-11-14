-- Memory ((B)): memory ClassTails for the pair classes Stp/Ldp (SP base,
-- 16-aligned LSE2) and Stp8/Ldp8 (Rn base, one 16-byte access or two 8-byte halves), over
-- NativeEntryBodyMem.<K>.run at the actual action state.
import HeapV2StepCerts.MemTailStrb
import NativeEntryBodyMem.Stp
import NativeEntryBodyMem.Ldp
import NativeEntryBodyMem.Stp8
import NativeEntryBodyMem.Ldp8
import NativeEntryBodyDispatch.Stp
import NativeEntryBodyDispatch.Ldp
import NativeEntryBodyDispatch.Stp8
import NativeEntryBodyDispatch.Ldp8
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace HeapV2StepCerts.MemTail
open ArmCertWalk ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)

theorem noupdate_delta {domain : QueryDomain} {spec : TopologyImageSpec domain} {va : BitVec 64}
    {before mid : Array Event} {ad : AddressDescriptor} (h : NoUpdateTraffic spec va before ad mid) :
    ∃ d, mid = before ++ d ∧ ArmCertCTOrdered.OrderedEventV2.Covered d := by
  obtain ⟨info, walk, leaf, middle, traffic, _, _, _, after⟩ := h
  obtain ⟨d, hd, cov⟩ := EntryTraffic.translate_delta_covered before info walk leaf middle ad traffic
  exact ⟨d, after.trans hd, cov⟩

theorem single_delta {domain : QueryDomain} {spec : TopologyImageSpec domain} {va : BitVec 64}
    {before after : Array Event} {e : Event}
    (h : ∃ ad mid, NoUpdateTraffic spec va before ad mid ∧ after = mid.push e)
    (he : ArmCertCTOrdered.OrderedEventV2.Covered #[e]) :
    ∃ d, after = before ++ d ∧ ArmCertCTOrdered.OrderedEventV2.Covered d := by
  obtain ⟨ad, mid, traffic, hafter⟩ := h
  obtain ⟨d, hd, cov⟩ := noupdate_delta traffic
  exact ⟨d ++ #[e], by rw [hafter, hd, Array.push_eq_append, Array.append_assoc],
    EntryTraffic.covered_append cov he⟩

theorem pair_delta {domain : QueryDomain} {spec : TopologyImageSpec domain} {A : BitVec 64}
    {pa1 pa2 : BitVec 56} {one half1 half2 : Event} {before after : Array Event}
    (h : PairEvents spec A pa1 pa2 one half1 half2 before after)
    (h0 : ArmCertCTOrdered.OrderedEventV2.Covered #[one]) (h1 : ArmCertCTOrdered.OrderedEventV2.Covered #[half1])
    (h2 : ArmCertCTOrdered.OrderedEventV2.Covered #[half2]) :
    ∃ d, after = before ++ d ∧ ArmCertCTOrdered.OrderedEventV2.Covered d := by
  rcases h with ⟨_, single⟩ | ⟨_, ad1, mid1, ad2, mid2, t1, t2, hafter⟩
  · exact single_delta single h0
  · obtain ⟨d1, hd1, c1⟩ := noupdate_delta t1
    obtain ⟨d2, hd2, c2⟩ := noupdate_delta t2
    refine ⟨d1 ++ #[half1] ++ d2 ++ #[half2], ?_, EntryTraffic.covered_append
      (EntryTraffic.covered_append (EntryTraffic.covered_append c1 h1) c2) h2⟩
    rw [hafter, hd2, hd1, Array.push_eq_append, Array.push_eq_append]
    simp only [Array.append_assoc]

theorem pairAccess_act {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {fetched sp : NativeState} {w : BitVec 32} {K : Int} {A : BitVec 64} {acc : AccessDescriptor}
    (e20 : E20Frame fetched.regs sp.regs) (h : PairAccess spec config rows mapping A acc fetched) :
    PairAccess spec config rows mapping A acc (actionState w sp K) := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · obtain ⟨m, d, x⟩ := h.1 a; exact ⟨m, d, ActionTransport.access e20 x⟩
  · obtain ⟨⟨m1, d1, x1⟩, ⟨m2, d2, x2⟩⟩ := h.2 a
    exact ⟨⟨m1, d1, ActionTransport.access e20 x1⟩, ⟨m2, d2, ActionTransport.access e20 x2⟩⟩

theorem mem_tail_Stp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (source fetched : NativeState) (enc0 : __InstrEnc) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (current : CurrentS1At spec config rows fetched)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc →
      domain (MemClass.Stp.query fetched imm7 acc) ∧
      (∃ data : S1AccessData spec config rows (MemClass.Stp.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Stp.query fetched imm7 acc) data fetched) ∧
      MemM1.MemWriteD6.PreW acc fetched.regs)
    (mode : HostEL0ModeAt fetched.regs) (debug : ExistingE11DebugAt fetched.regs)
    (post : MemM1.MemReadD2.PostRegs2 fetched.regs)
    (hEL3A64 : fetched.regs.FeatureImpl[7] = true) (hNoEL3A32 : fetched.regs.FeatureImpl[3] = false)
    (hTME : fetched.regs.FeatureImpl[227] = false) (lse2 : fetched.regs.FeatureImpl[111] = true)
    (dcache : currentDCache fetched.regs = true)
    (hsp : fetched.regs.SP_EL0.toNat % 16 = 0) (hal : (ArmCertMem.LdpEval.ldpAddr fetched imm7).toNat % 16 = 0)
    (pa : BitVec 56) (mapped : mapping (ArmCertMem.LdpEval.ldpAddr fetched imm7) = some pa.toNat)
    (mmio : MemM1.MemReadIF.NotMMIO pa)
    (outside : ∀ i < 16, ¬ (rowsFootprint spec.imageRows).byte (pa.toNat + i))
    (raw : RawImageAt spec.imageRows fetched.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT fetched.regs} acc spec.imageRows = true) :
    ∃ (sp a fin : NativeState) (written : Nat → Prop) (delta : Array Event),
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame NativeEntryBodyMem.Stp.writes (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617) a ∧
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
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 617
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617 (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) 617
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (K := 617) postS.mem
  have feat := ActionTransport.feat (w := NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (K := 617) e20
  have gprEq := ActionTransport.gpr (w := NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (K := 617) e20
  have spEq := ActionTransport.sp0 (w := NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) (K := 617) e20
  have actEvents : (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617).events = fetched.events :=
    (actionState_events (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617).trans postS.events
  obtain ⟨t, ok, _, _, he, wo, sepW, af, _, _, frame, tq⟩ :=
    NativeEntryBodyMem.Stp.run spec config rows mapping (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617) imm7 Rt Rt2 hRt hRt2
      (ActionTransport.current e20 postS.mem current)
      (fun acc a0 a2 => by
        have qEq : MemClass.Stp.query (actionState (NativeEntryBodyDispatch.Stp.selected Rt Rt2 imm7) sp 617) imm7 acc = MemClass.Stp.query fetched imm7 acc := by
          simp only [MemClass.Stp.query, ArmCertMem.LdpEval.ldpAddr, spEq]
        rw [qEq]
        obtain ⟨member, ⟨data, access⟩, pre⟩ := perAcc acc a0 a2
        exact ⟨member, ⟨data, ActionTransport.access e20 access⟩, ActionTransport.preW e20 pre⟩)
      (ActionTransport.mode e20 mode) (ActionTransport.debug e20 debug) (ActionTransport.post2 e20 post)
      (feat ▸ hEL3A64) (feat ▸ hNoEL3A32) (feat ▸ hTME) (feat ▸ lse2) (ActionTransport.dcache e20 dcache)
      (by rw [spEq]; exact hsp) (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact hal)
      pa (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact mapped) mmio outside
      (by rw [actMem]; exact raw) (fun acc a0 => by rw [ActionTransport.haft e20]; exact noUpd acc a0)
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
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  rw [actEvents] at he
  obtain ⟨delta, hd, cov⟩ := single_delta he (memWrite_covered _ _ _ _ _ _)
  refine ⟨sp, t, fin, fun x => pa.toNat ≤ x ∧ x < pa.toNat + 16, delta, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x hx => by show fin.mem[x]? = fetched.mem[x]?; rw [output.mem, ← actMem]; exact wo x hx, sepW, by rw [events, hd], cov, gic, ?_, nonProj⟩
  simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc

#print axioms mem_tail_Stp

theorem mem_tail_Ldp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (source fetched : NativeState) (enc0 : __InstrEnc) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) 31 12 == 879088#20) = false)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (current : CurrentS1At spec config rows fetched)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemReadD2.AccDR2 acc →
      domain (MemClass.Ldp.query fetched imm7 acc) ∧
      ∃ data : S1AccessData spec config rows (MemClass.Ldp.query fetched imm7 acc),
        CurrentS1AccessAt spec config rows mapping (MemClass.Ldp.query fetched imm7 acc) data fetched)
    (mode : HostEL0ModeAt fetched.regs) (debug : ExistingE11DebugAt fetched.regs)
    (post : MemM1.MemReadD2.PostRegs2 fetched.regs)
    (hEL3A64 : fetched.regs.FeatureImpl[7] = true) (hNoEL3A32 : fetched.regs.FeatureImpl[3] = false)
    (hTME : fetched.regs.FeatureImpl[227] = false) (lse2 : fetched.regs.FeatureImpl[111] = true)
    (dcache : currentDCache fetched.regs = true)
    (hsp : fetched.regs.SP_EL0.toNat % 16 = 0) (hal : (ArmCertMem.LdpEval.ldpAddr fetched imm7).toNat % 16 = 0)
    (pa : BitVec 56) (mapped : mapping (ArmCertMem.LdpEval.ldpAddr fetched imm7) = some pa.toNat)
    (mmio : MemM1.MemReadIF.NotMMIO pa)
    (data : BitVec 128) (bytes : ∀ i < 16, fetched.mem[pa.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8))
    (raw : RawImageAt spec.imageRows fetched.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT fetched.regs} acc spec.imageRows = true) :
    ∃ (sp a fin : NativeState) (written : Nat → Prop) (delta : Array Event),
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame NativeEntryBodyMem.Ldp.writes (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611) a ∧
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
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) 611
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611 (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) 611
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (K := 611) postS.mem
  have feat := ActionTransport.feat (w := NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (K := 611) e20
  have gprEq := ActionTransport.gpr (w := NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (K := 611) e20
  have spEq := ActionTransport.sp0 (w := NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) (K := 611) e20
  have actEvents : (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611).events = fetched.events :=
    (actionState_events (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611).trans postS.events
  obtain ⟨t, ok, _, hm, he, af, _, _, frame, tq⟩ :=
    NativeEntryBodyMem.Ldp.run spec config rows mapping (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611) imm7 Rt Rt2 hRt hRt2 hRtt
      (ActionTransport.current e20 postS.mem current)
      (fun acc a0 a2 => by
        have qEq : MemClass.Ldp.query (actionState (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 imm7) sp 611) imm7 acc = MemClass.Ldp.query fetched imm7 acc := by
          simp only [MemClass.Ldp.query, ArmCertMem.LdpEval.ldpAddr, spEq]
        rw [qEq]
        obtain ⟨member, data, access⟩ := perAcc acc a0 a2
        exact ⟨member, data, ActionTransport.access e20 access⟩)
      (ActionTransport.mode e20 mode) (ActionTransport.debug e20 debug) (ActionTransport.post2 e20 post)
      (feat ▸ hEL3A64) (feat ▸ hNoEL3A32) (feat ▸ hTME) (feat ▸ lse2) (ActionTransport.dcache e20 dcache)
      (by rw [spEq]; exact hsp) (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact hal)
      pa (by simp only [ArmCertMem.LdpEval.ldpAddr, spEq]; exact mapped) mmio data (by rw [actMem]; exact bytes)
      (by rw [actMem]; exact raw) (fun acc a0 => by rw [ActionTransport.haft e20]; exact noUpd acc a0)
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
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  rw [actEvents] at he
  obtain ⟨delta, hd, cov⟩ := single_delta he (memRead_covered _ _ _ _)
  refine ⟨sp, t, fin, fun _ => False, delta, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [output.mem, hm, actMem], EntryBtiNext.no_writes_separated _, by rw [events, hd], cov, gic, ?_, nonProj⟩
  simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc

#print axioms mem_tail_Ldp

theorem mem_tail_Stp8 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (source fetched : NativeState) (enc0 : __InstrEnc) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) 31 12 == 879088#20) = false)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (current : CurrentS1At spec config rows fetched)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc →
      PairAccess spec config rows mapping (MemClass.Stp8.pairAddr fetched Rn imm7) acc fetched)
    (preW : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc → MemM1.MemWriteD6.PreW acc fetched.regs)
    (mode : HostEL0ModeAt fetched.regs) (debug : ExistingE11DebugAt fetched.regs)
    (post : MemM1.MemReadD2.PostRegs2 fetched.regs)
    (hEL3A64 : fetched.regs.FeatureImpl[7] = true) (hNoEL3A32 : fetched.regs.FeatureImpl[3] = false)
    (hTME : fetched.regs.FeatureImpl[227] = false) (lse2 : fetched.regs.FeatureImpl[111] = true)
    (dcache : currentDCache fetched.regs = true)
    (h8 : (MemClass.Stp8.pairAddr fetched Rn imm7).toNat % 8 = 0)
    (pa1 pa2 : BitVec 56) (mapped1 : mapping (MemClass.Stp8.pairAddr fetched Rn imm7) = some pa1.toNat)
    (mapped2 : mapping (plus8 (MemClass.Stp8.pairAddr fetched Rn imm7)) = some pa2.toNat)
    (contiguous : (MemClass.Stp8.pairAddr fetched Rn imm7).toNat % 16 = 0 → pa2.toNat = pa1.toNat + 8)
    (mmio1 : MemM1.MemReadIF.NotMMIO pa1) (mmio2 : MemM1.MemReadIF.NotMMIO pa2)
    (outside1 : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa1.toNat + i))
    (outside2 : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa2.toNat + i))
    (raw : RawImageAt spec.imageRows fetched.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT fetched.regs} acc spec.imageRows = true) :
    ∃ (sp a fin : NativeState) (written : Nat → Prop) (delta : Array Event),
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame NativeEntryBodyMem.Stp8.writes (actionState (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) sp 617) a ∧
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
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) 617
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) sp 617 (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) 617
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) (K := 617) postS.mem
  have feat := ActionTransport.feat (w := NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) (K := 617) e20
  have gprEq := ActionTransport.gpr (w := NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) (K := 617) e20
  have spEq := ActionTransport.sp0 (w := NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) (K := 617) e20
  have actEvents : (actionState (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) sp 617).events = fetched.events :=
    (actionState_events (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) sp 617).trans postS.events
  obtain ⟨t, ok, _, _, he, wo, sepW, af, _, _, frame, tq⟩ :=
    NativeEntryBodyMem.Stp8.run spec config rows mapping (actionState (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) sp 617) imm7 Rn Rt Rt2 hRn hRt hRt2
      (ActionTransport.current e20 postS.mem current)
      (fun acc a0 a2 => by simp only [MemClass.Stp8.pairAddr, gprEq]; exact pairAccess_act e20 (perAcc acc a0 a2))
      (fun acc a0 a2 => ActionTransport.preW e20 (preW acc a0 a2))
      (ActionTransport.mode e20 mode) (ActionTransport.debug e20 debug) (ActionTransport.post2 e20 post)
      (feat ▸ hEL3A64) (feat ▸ hNoEL3A32) (feat ▸ hTME) (feat ▸ lse2) (ActionTransport.dcache e20 dcache)
      (by simp only [MemClass.Stp8.pairAddr, gprEq]; exact h8)
      pa1 pa2 (by simp only [MemClass.Stp8.pairAddr, gprEq]; exact mapped1)
      (by simp only [MemClass.Stp8.pairAddr, gprEq]; exact mapped2)
      (by simp only [MemClass.Stp8.pairAddr, gprEq]; exact contiguous) mmio1 mmio2 outside1 outside2
      (by rw [actMem]; exact raw) (fun acc a0 => by rw [ActionTransport.haft e20]; exact noUpd acc a0)
      (budget + 1) metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) 617 := by
    intro pc u see
    exact NativeEntryBodyDispatch.Stp8.dispatch_at real pc Rt Rn Rt2 imm7 u (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0 sp currentGuard 617 (by decide) dispatch
  have nativePrefix : nativeTail real source (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) enc0 fetched = nativeAfterAction real source (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) enc0 t := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) enc0 fetched = afterSpecPmu real source (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0 (actionState (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) sp 617) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) enc0 t :=
        action_boundary real source (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) enc0 (actionState (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) sp 617) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source (NativeEntryBodyDispatch.Stp8.selected Rt Rn Rt2 imm7) enc0 t budget tq actionPins next enc eret actionIT actionSS
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  rw [actEvents] at he
  obtain ⟨delta, hd, cov⟩ := pair_delta he (memWrite_covered _ _ _ _ _ _) (memWrite_covered _ _ _ _ _ _) (memWrite_covered _ _ _ _ _ _)
  refine ⟨sp, t, fin, fun x => (pa1.toNat ≤ x ∧ x < pa1.toNat + 8) ∨ (pa2.toNat ≤ x ∧ x < pa2.toNat + 8), delta, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x hx => by show fin.mem[x]? = fetched.mem[x]?; rw [output.mem, ← actMem]; exact wo x hx, sepW, by rw [events, hd], cov, gic, ?_, nonProj⟩
  simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc

#print axioms mem_tail_Stp8

theorem mem_tail_Ldp8 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (source fetched : NativeState) (enc0 : __InstrEnc) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) 31 12 == 879088#20) = false)
    (pins : StepPins fetched) (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched)
    (budget : Nat) (quiet : HookQuiet (budget + 1) fetched)
    (it : fetched.regs.ShouldAdvanceIT = false) (ss : fetched.regs.ShouldAdvanceSS = true)
    (current : CurrentS1At spec config rows fetched)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemReadD2.AccDR2 acc →
      PairAccess spec config rows mapping (MemClass.Ldp8.pairAddr fetched Rn imm7) acc fetched)
    (mode : HostEL0ModeAt fetched.regs) (debug : ExistingE11DebugAt fetched.regs)
    (post : MemM1.MemReadD2.PostRegs2 fetched.regs)
    (hEL3A64 : fetched.regs.FeatureImpl[7] = true) (hNoEL3A32 : fetched.regs.FeatureImpl[3] = false)
    (hTME : fetched.regs.FeatureImpl[227] = false) (lse2 : fetched.regs.FeatureImpl[111] = true)
    (dcache : currentDCache fetched.regs = true)
    (h8 : (MemClass.Ldp8.pairAddr fetched Rn imm7).toNat % 8 = 0)
    (pa1 pa2 : BitVec 56) (mapped1 : mapping (MemClass.Ldp8.pairAddr fetched Rn imm7) = some pa1.toNat)
    (mapped2 : mapping (plus8 (MemClass.Ldp8.pairAddr fetched Rn imm7)) = some pa2.toNat)
    (contiguous : (MemClass.Ldp8.pairAddr fetched Rn imm7).toNat % 16 = 0 → pa2.toNat = pa1.toNat + 8)
    (mmio1 : MemM1.MemReadIF.NotMMIO pa1) (mmio2 : MemM1.MemReadIF.NotMMIO pa2)
    (data : BitVec 128)
    (bytes1 : ∀ i < 8, fetched.mem[pa1.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8))
    (bytes2 : ∀ i < 8, fetched.mem[pa2.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * (i + 8)) 8))
    (raw : RawImageAt spec.imageRows fetched.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT fetched.regs} acc spec.imageRows = true) :
    ∃ (sp a fin : NativeState) (written : Nat → Prop) (delta : Array Event),
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame NativeEntryBodyMem.Ldp8.writes (actionState (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) sp 611) a ∧
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
  have metadataInput := currentInput.after_metadata (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) 611
  have metadataQuiet := actionState_quiet (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) sp 611 (budget + 1) postS.quiet
  have metaPins := entryPins_at_metadata sp (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) 611
    (NativeEntryTail.EntryPins.after_E20 fetched sp (NativeEntryTail.EntryPins.of_scalar fetched pins) e20)
  have actMem := ActionTransport.mem (w := NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) (K := 611) postS.mem
  have feat := ActionTransport.feat (w := NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) (K := 611) e20
  have gprEq := ActionTransport.gpr (w := NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) (K := 611) e20
  have spEq := ActionTransport.sp0 (w := NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) (K := 611) e20
  have actEvents : (actionState (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) sp 611).events = fetched.events :=
    (actionState_events (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) sp 611).trans postS.events
  obtain ⟨t, ok, _, hm, he, af, _, _, frame, tq⟩ :=
    NativeEntryBodyMem.Ldp8.run spec config rows mapping (actionState (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) sp 611) imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt
      (ActionTransport.current e20 postS.mem current)
      (fun acc a0 a2 => by simp only [MemClass.Ldp8.pairAddr, gprEq]; exact pairAccess_act e20 (perAcc acc a0 a2))
      (ActionTransport.mode e20 mode) (ActionTransport.debug e20 debug) (ActionTransport.post2 e20 post)
      (feat ▸ hEL3A64) (feat ▸ hNoEL3A32) (feat ▸ hTME) (feat ▸ lse2) (ActionTransport.dcache e20 dcache)
      (by simp only [MemClass.Ldp8.pairAddr, gprEq]; exact h8)
      pa1 pa2 (by simp only [MemClass.Ldp8.pairAddr, gprEq]; exact mapped1)
      (by simp only [MemClass.Ldp8.pairAddr, gprEq]; exact mapped2)
      (by simp only [MemClass.Ldp8.pairAddr, gprEq]; exact contiguous) mmio1 mmio2 data
      (by rw [actMem]; exact bytes1) (by rw [actMem]; exact bytes2)
      (by rw [actMem]; exact raw) (fun acc a0 => by rw [ActionTransport.haft e20]; exact noUpd acc a0)
      (budget + 1) metadataQuiet
  have dispatch : DispatchAt real (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) 611 := by
    intro pc u see
    exact NativeEntryBodyDispatch.Ldp8.dispatch_at real pc Rt Rn Rt2 imm7 u (by simpa using see)
  have boundary := metadata_boundary_at real source (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0 sp currentGuard 611 (by decide) dispatch
  have nativePrefix : nativeTail real source (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) enc0 fetched = nativeAfterAction real source (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) enc0 t := by
    calc
      nativeTail real source (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) enc0 fetched = afterSpecPmu real source (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) enc0 sp :=
        spec_pmu_boundary real source (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) enc0 fetched sp hook
      _ = nativeAtAction real source (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0 (actionState (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) sp 611) := boundary
      _ = nativeAfterAction real source (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) enc0 t :=
        action_boundary real source (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) enc0 (actionState (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) sp 611) t ok
  have actionPins := NativeEntryTail.EntryPins.after_action frame metaPins
  have next : t.regs.BTypeNext = 0#2 := by
    rw [af.btn]
    change sp.regs.BTypeNext = 0#2
    exact (PMUFrame.of_E20 e20).btn.trans pins.btn
  have enc : t.regs.__ThisInstrEnc = .__A64 := frame.enc
  have eret : (Sail.BitVec.extractLsb (t.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [frame.b32]
    change (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) 31 12 == 879088#20) = false
    exact noEret
  have actionIT : t.regs.ShouldAdvanceIT = false := frame.it.trans ((PMUFrame.of_E20 e20).it.trans it)
  have actionSS : t.regs.ShouldAdvanceSS = true := frame.ss.trans ((PMUFrame.of_E20 e20).ss.trans ss)
  obtain ⟨fin, tail, finalQuiet, finalPins, sys, _, output, events, gic, _, pc, nonProj⟩ :=
    guarded_after_action_entry real source (NativeEntryBodyDispatch.Ldp8.selected Rt Rn Rt2 imm7) enc0 t budget tq actionPins next enc eret actionIT actionSS
  have noBranch : t.regs.__BranchTaken = false := frame.bt
  have actionPC : t.regs._PC = source.regs._PC := frame.pc.trans metadataInput.pc
  rw [actEvents] at he
  obtain ⟨delta, hd, cov⟩ := pair_delta he (memRead_covered _ _ _ _) (memRead_covered _ _ _ _) (memRead_covered _ _ _ _)
  refine ⟨sp, t, fin, fun _ => False, delta, hook, nativePrefix.trans tail, frame, finalQuiet, finalPins, sys,
    fun x _ => by show fin.mem[x]? = fetched.mem[x]?; rw [output.mem, hm, actMem], EntryBtiNext.no_writes_separated _, by rw [events, hd], cov, gic, ?_, nonProj⟩
  simpa only [noBranch, Bool.false_eq_true, ite_false, actionPC] using pc

#print axioms mem_tail_Ldp8

end HeapV2StepCerts.MemTail
