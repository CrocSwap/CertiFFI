-- the ChainInv v3 BL step (k = 15, 150, 252: calls into the
-- copy helpers; the plan is unrolled through calls, so the callee entry is base + offset (k+1)).
-- BlTailAt = CallerBl.native_tail_x's facts over the fetched state; entry_class_next_v3_bl = Core's
-- entry_class_next_v3 with that tail (BL frame: SysEq2/BrSysEq fetched → fin, X30 dropped);
-- plan_step3_bl with upds k = [(.x 30, .drop)]; instances blStep_15/150/252.
import Bridge.CruxGenGuarded.ChainInvV3
import RtBranch.BranchStepV3
import RtBl.BlTailX
import HeapV2StepCerts.MemStepsV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace HeapV2StepCerts.BlStepV3
open HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/-- CallerControls is static configuration; the actual fetch keeps it. -/
theorem caller_controls_fetched (s final : NativeState) {acc : AccessDescriptor} {out : TTWState}
    (hregs : final.regs = FetchedRegs acc out s) (sys : SysEq2 s.regs final.regs)
    (c : CallerControls s) : CallerControls final := by
  have g : ∀ k : Bank_BitVec_64,
      (ArmBridge.CruxGenGuarded.beforeFetchState s).regs.bank_BitVec_64 k = s.regs.bank_BitVec_64 k →
      final.regs.bank_BitVec_64 k = s.regs.bank_BitVec_64 k := by
    intro k hb
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 k) _ _ s (fun _ _ => rfl) (fun _ => rfl) hb
  exact
    { f4 := by rw [sys.feat]; exact c.f4
      f2 := by rw [sys.feat]; exact c.f2
      f3 := by rw [sys.feat]; exact c.f3
      f6 := by rw [sys.feat]; exact c.f6
      f7 := by rw [sys.feat]; exact c.f7
      rme := by rw [sys.feat]; exact c.rme
      vhe := by rw [sys.feat]; exact c.vhe
      brbe := by rw [sys.feat]; exact c.brbe
      el := by rw [sys.el]; exact c.el
      nrw := by rw [sys.nrw]; exact c.nrw
      e2h := by rw [sys.hcr]; exact c.e2h
      tge := by rw [sys.hcr]; exact c.tge
      ns := by rw [sys.scr]; exact c.ns
      pmb := by rw [g _ (by simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne])]; exact c.pmb
      spe := by rw [sys.spe]; exact c.spe
      pmbs := by rw [g _ (by simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne])]; exact c.pmbs
      nspb := by rw [g _ (by simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne])]; exact c.nspb
      nspbe := by rw [g _ (by simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne])]; exact c.nspbe
      gcsEn := by rw [g _ (by simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne])]; exact c.gcsEn }

/-- The actual BL tail from the post-fetch state, as the v3 chain consumes it. -/
def BlTailAt (real : Type) [Sail.SailReal real] (imm26 : BitVec 26) (source : NativeState)
    (next : BitVec 64) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → NativeEntryInput.Input source fetched →
    MetadataGuard fetched → HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true → CallerControls fetched →
    ∃ fin, nativeTail real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched = .ok () fin ∧
      HookQuiet budget fin ∧ StepPins fin ∧
      SysEq2 fetched.regs fin.regs ∧ ArmBridge.CruxGen.BrSysEq fetched.regs fin.regs ∧
      fin.mem = fetched.mem ∧ fin.regs._PC = next ∧
      (∃ v, fin.regs.gpr = fetched.regs.gpr.set 30 v) ∧ fin.regs.SP_EL0 = fetched.regs.SP_EL0 ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = fetched.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs.bank_Int .__block_bbm_implemented = fetched.regs.bank_Int .__block_bbm_implemented ∧
      fin.regs.bank_BitVec_64 .PIR_EL2 = fetched.regs.bank_BitVec_64 .PIR_EL2 ∧
      fin.regs.bank_BitVec_64 .PIRE0_EL2 = fetched.regs.bank_BitVec_64 .PIRE0_EL2 ∧
      fin.regs.bank_BitVec_64 .POR_EL0 = fetched.regs.bank_BitVec_64 .POR_EL0

/-- CallerBl.native_tail_x gives BlTailAt at the BL target (the fetch keeps PC). -/
theorem bl_tail (real : Type) [Sail.SailReal real] (imm26 : BitVec 26) (source : NativeState)
    (low : (blTarget imm26 source).toNat < 2 ^ 55) : BlTailAt real imm26 source (blTarget imm26 source) := by
  intro fetched enc0 budget pins input guard quiet it ss controls
  have pcEq : fetched.regs._PC = source.regs._PC := input.pc
  have target : blTarget imm26 fetched = blTarget imm26 source := by
    rw [NativeEntryCallerRegisters.bl_target, NativeEntryCallerRegisters.bl_target, pcEq]
  obtain ⟨fin, run, q, sp, sys, br, mem, pc, gpr, spr, gic, bbm, pir, pire0, por⟩ :=
    ArmBridge.CruxGenGuarded.CallerBl.native_tail_x real source fetched enc0 imm26 controls
      (by rw [target]; exact low) pins guard budget quiet it ss
  exact ⟨fin, run, q, sp, sys, br, mem, pc.trans target, ⟨_, gpr⟩, spr, gic, bbm, pir, pire0, por⟩

set_option maxHeartbeats 200000 in
theorem entry_class_next_v3_bl (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (imm26 : BitVec 26)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (tail : BlTailAt real imm26 s next) (controls : CallerControls s)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (nextPlaced : next = base + nextOffset)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (placedImg : MemReloc.ImageOn scope image s loadBase mapping)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (bp : Crypto.BranchV2.BranchPinsV2PA s)
    (rawS : RawImageAt spec.imageRows s.mem)
    (noUpdS : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (mmio : MappedNotMMIO mapping s.regs._PC)
    (present : MappedBytesPresent mapping s.regs._PC s.mem)
    (perAcc : ∀ acc, ActualIFetchAcc (ArmBridge.CruxGenGuarded.beforeFetchState s) acc →
      domain (queryOf acc) ∧ ∃ data : S1AccessData spec config rows (queryOf acc),
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data
          (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (code : ∀ acc leafLevel view faultOut (address : AddressDescriptor) translated (word' : BitVec 32),
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view
        (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)) (faultOut, address) translated →
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? = some (word'.extractLsb' (8 * i) 8)) →
      word' = NativeEntryCallerDispatch.Bl.word imm26) :
    ∃ fin,
      modelStep real s = .ok () fin ∧
      StepPins fin ∧ HookQuiet budget fin ∧
      CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState fin) ∧
      fin.regs._PC = base + nextOffset ∧
      E11Debug.E11CheckDebug fin.regs ∧ EntryFeatures fin.regs ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = none ∧
      ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState fin) ∧
      MemReloc.ImageOn scope image fin loadBase mapping ∧
      Crypto.BranchV2.BranchPinsV2PA fin ∧
      (∃ v, fin.regs.gpr = s.regs.gpr.set 30 v) ∧ fin.regs.SP_EL0 = s.regs.SP_EL0 ∧ fin.mem = s.mem ∧
      SysEq2 s.regs fin.regs := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, actualAcc, run, clean, bytes, fregs,
      fmem, _fev, curFinal, _, _info, _walk, _leaf, _middle, _len, _traffic, _tev, noUpdCond⟩ :=
    native_fetch_current_preserving_events spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  have hw := code acc data.leafLevel data.view faultOut address translated w' clean bytes
  subst hw
  have closedFinal := closed_membership_after_fetch closed clean fregs
  have placedFinal := HeapV2StepCerts.placed_fetch placedImg separated clean fmem
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have hregs : final.regs = FetchedRegs acc (translateCurrent out) s := by
    rw [fregs, translatedRegs, rawOf acc]; rfl
  have emuFinal : final.regs.__emulator_termination_opcode = none := by
    rw [hregs]; unfold FetchedRegs fetchGuardRegs; split
    · exact emu0
    · exact emu0
  obtain ⟨enc0, hstep⟩ := entry_prefetch_boundary real s final _ pins hGIC run emuFinal
  have fpins := EntryClassNext.fetched_steppins acc (translateCurrent out) s final stepPins hregs
  have finput := fetched_input acc (translateCurrent out) s final pins.el hregs
  obtain ⟨guard, fquiet, it, ss⟩ :=
    fetched_rest acc (translateCurrent out) s final (budget + 1) pins quiet hregs
  have bpFinal := EntryFetchedBranch.fetched_branch_pins acc (translateCurrent out) s final stepPins hregs bp
  have sysF : SysEq2 s.regs final.regs := EntryBranchPins.sysEq2_symm _ _ finput.sys
  have controlsF := caller_controls_fetched s final hregs sysF controls
  obtain ⟨fin, tail, finQuiet, finStep, sys, brsys, mem, pc, ⟨v, gprF⟩, spF, gicF, bbm, pir, pire0, por⟩ :=
    tail final enc0 budget fpins finput guard fquiet it ss controlsF
  have curFin : CurrentS1At spec config rows fin := by
    refine current_s1_program_write curFinal (fun _ => False) (EntryBtiNext.no_writes final fin mem)
      (EntryBtiNext.no_writes_separated _) sys.feat sys.el sys.nrw sys.tcr sys.tcr2 sys.hcr sys.scr sys.sctlr
      sys.mair sys.pa (fun _ => pir) (fun _ => pire0) (fun _ => por) sys.tlb
  have mdscrFinal : final.regs.bank_BitVec_64 .MDSCR_EL1 = s.regs.bank_BitVec_64 .MDSCR_EL1 := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .MDSCR_EL1) _ _ s (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]
  have hdeFinal : _get_EDSCR_Type_HDE (final.regs.bank_BitVec_32 ._EDSCR) =
      _get_EDSCR_Type_HDE (s.regs.bank_BitVec_32 ._EDSCR) := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR)) _ _ s
      (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne, RegMap.set_same]
    exact ArmBridge.CruxCore.hde_pipeadv _ _
  have featFin : fin.regs.FeatureImpl = s.regs.FeatureImpl := sys.feat.trans sysF.feat
  have gicFin : fin.regs.bank_Option_InterruptID .__GIC_Pending = none := by
    rw [gicF, hregs]
    rw [ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_Option_InterruptID .__GIC_Pending) _ _ s (fun _ _ => rfl)
      (fun _ => rfl) rfl]
    exact hGIC
  have closedFin := ClosedChain.closed_of_fields closedFinal sys.feat sys.tcr sys.sctlr sys.ttbr0 sys.httbr sys.ttbr1 bbm
  have placedFin := HeapV2StepCerts.placed_class mem placedFinal
  have memNoUpd : translated.mem = (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).mem :=
    (noUpdCond rawS (by
      rw [rawOf acc]
      exact HeapV2StepCerts.RawFetch.noUpd_read noUpdS acc (actual_ifetch_flags actualAcc).2.2.1)).2.2
  have finMem : fin.mem = s.mem := mem.trans (fmem.trans memNoUpd)
  have gprFinal : final.regs.gpr = s.regs.gpr := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.gpr) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have spFinal : final.regs.SP_EL0 = s.regs.SP_EL0 := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have sysS : SysEq2 s.regs fin.regs := sysEq2_trans _ _ _ sysF sys
  have bpFin := Crypto4.branchPinsV2_step_pa final fin bpFinal sys finStep brsys
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin, closed_before_fetch fin closedFin, placedFin, bpFin, ⟨v, by rw [gprF, gprFinal]⟩, spF.trans spFinal, finMem, sysS⟩
  · rw [pc, nextPlaced]
  · rw [sys.mdscr, mdscrFinal]; exact debug.mde
  · rw [sys.hde, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

#print axioms entry_class_next_v3_bl

/-- upds k = [(.x 30, .drop)]: X30 dropped, everything else kept. -/
theorem bl_holds {k : Nat} {x y : NativeState} (upd : HeapV2StepCerts.RegBind.upds k = [(.x 30, .drop)])
    (gpr : ∃ v, y.regs.gpr = x.regs.gpr.set 30 v) (sp : y.regs.SP_EL0 = x.regs.SP_EL0) :
    HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) x y := by
  obtain ⟨v, gpr⟩ := gpr
  rw [upd]
  intro r
  cases r with
  | sp => simp [HeapV2StepCerts.RegBind.updOf, List.find?, HeapV2StepCerts.RegBind.regVal, sp]
  | x i =>
    by_cases h : i = 30
    · subst h; simp [HeapV2StepCerts.RegBind.updOf, List.find?]
    · have hv : i.val ≠ 30 := fun e => h (Fin.ext e)
      have e1 : (HeapV2StepCerts.RegBind.Reg.x 30 = HeapV2StepCerts.RegBind.Reg.x i) = False := by
        simp only [HeapV2StepCerts.RegBind.Reg.x.injEq, eq_iff_iff, iff_false]; exact fun e => h e.symm
      simp only [HeapV2StepCerts.RegBind.updOf, List.find?, e1, decide_false, Option.map_none,
        Option.getD_none, HeapV2StepCerts.RegBind.regVal, gpr]
      exact Vector.getElem_set_ne _ _ (fun e => hv e.symm)

theorem plan_step3_bl (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm26 : BitVec 26) (upd : HeapV2StepCerts.RegBind.upds k = [(.x 30, .drop)])
    (next : NativeState → BitVec 64)
    (tail : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      BlTailAt real imm26 x (next x))
    (controls : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      CallerControls x)
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x) :
    Uget.Chain.Step real (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)) := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, gprEq, spEq, finMem, sys⟩ :=
    entry_class_next_v3_bl real spec config rows mapping imm26 x inv.v2.v1.pins (next x)
      (offset (k + 1)) (tail x inv) (controls x inv) inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩,
    HeapV2StepCerts.RegBind.carry_step hk (bl_holds upd gprEq spEq) inv.regBind, ?_, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩⟩
  · intro e he n hn i hi; rw [finMem]; exact inv.present e he n hn i hi
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [ChainInvV3.hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms plan_step3_bl
