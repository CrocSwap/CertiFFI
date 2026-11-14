-- rich-v3: the callee-link interface. BL steps export the link write
-- fin.gpr[30] = x.PC + 4 (before SCR_EL3, still last); the helper RET's target and low bound are pointwise
-- (Core feeds them from RtSaved2.link_target). Branch layer reused from RtB2.RichG (rich-v2).
import RtB2.RichAt
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace RtB3.RichH
open RtB2.RichG
open HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false

/-- The actual BL tail from the post-fetch state, as the v3 chain consumes it. -/
def BlTailAtL (real : Type) [Sail.SailReal real] (imm26 : BitVec 26) (source : NativeState)
    (next : BitVec 64) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → NativeEntryInput.Input source fetched →
    MetadataGuard fetched → HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true → CallerControls fetched →
    ∃ fin, nativeTail real source (NativeEntryCallerDispatch.Bl.word imm26) enc0 fetched = .ok () fin ∧
      HookQuiet budget fin ∧ StepPins fin ∧
      SysEq2 fetched.regs fin.regs ∧ ArmBridge.CruxGen.BrSysEq fetched.regs fin.regs ∧
      fin.mem = fetched.mem ∧ fin.regs._PC = next ∧
      (∃ v, fin.regs.gpr = fetched.regs.gpr.set 30 v) ∧ fin.regs.gpr[30] = source.regs._PC + 4#64 ∧
      fin.regs.SP_EL0 = fetched.regs.SP_EL0 ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = fetched.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs.bank_Int .__block_bbm_implemented = fetched.regs.bank_Int .__block_bbm_implemented ∧
      fin.regs.bank_BitVec_64 .PIR_EL2 = fetched.regs.bank_BitVec_64 .PIR_EL2 ∧
      fin.regs.bank_BitVec_64 .PIRE0_EL2 = fetched.regs.bank_BitVec_64 .PIRE0_EL2 ∧
      fin.regs.bank_BitVec_64 .POR_EL0 = fetched.regs.bank_BitVec_64 .POR_EL0 ∧
      fin.regs.bank_BitVec_64 .SCR_EL3 = fetched.regs.bank_BitVec_64 .SCR_EL3

/-- CallerBl.native_tail_x gives BlTailAtL at the BL target (the fetch keeps PC). -/
theorem bl_tailL (real : Type) [Sail.SailReal real] (imm26 : BitVec 26) (source : NativeState)
    (low : (blTarget imm26 source).toNat < 2 ^ 55) : BlTailAtL real imm26 source (blTarget imm26 source) := by
  intro fetched enc0 budget pins input guard quiet it ss controls
  have pcEq : fetched.regs._PC = source.regs._PC := input.pc
  have target : blTarget imm26 fetched = blTarget imm26 source := by
    rw [NativeEntryCallerRegisters.bl_target, NativeEntryCallerRegisters.bl_target, pcEq]
  obtain ⟨fin, run, q, sp, sys, br, mem, pc, gpr, spr, gic, bbm, pir, pire0, por, gcs⟩ :=
    ArmBridge.CruxGenGuarded.CallerBl.native_tail_g real source fetched enc0 imm26 controls
      (by rw [target]; exact low) pins guard budget quiet it ss
  exact ⟨fin, run, q, sp, sys, br, mem, pc.trans target, ⟨_, gpr⟩, by rw [gpr, pcEq]; simp, spr, gic, bbm, pir, pire0, por, gcs⟩

set_option maxHeartbeats 200000 in
theorem entry_class_next_v3_blL (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (imm26 : BitVec 26)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (tail : BlTailAtL real imm26 s next) (controls : CallerControls s)
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
      (∃ v, fin.regs.gpr = s.regs.gpr.set 30 v) ∧ fin.regs.gpr[30] = s.regs._PC + 4#64 ∧
      fin.regs.SP_EL0 = s.regs.SP_EL0 ∧ fin.mem = s.mem ∧
      SysEq2 s.regs fin.regs ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 := by
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
  obtain ⟨fin, tail, finQuiet, finStep, sys, brsys, mem, pc, ⟨v, gprF⟩, lrF, spF, gicF, bbm, pir, pire0, por, gcsF⟩ :=
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
  have gcsFinal : final.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .SCR_EL3) _ _ s (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]
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
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin, closed_before_fetch fin closedFin, placedFin, bpFin, ⟨v, by rw [gprF, gprFinal]⟩, lrF, spF.trans spFinal, finMem, sysS, gcsF.trans gcsFinal⟩
  · rw [pc, nextPlaced]
  · rw [sys.mdscr, mdscrFinal]; exact debug.mde
  · rw [sys.hde, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

#print axioms entry_class_next_v3_bl

/-- upds k = [(.x 30, .drop)]: X30 dropped, everything else kept. -/
theorem rich_bl_atL (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm26 : BitVec 26) (upd : HeapV2StepCerts.RegBind.upds k = [(.x 30, .drop)]) (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (tail : BlTailAtL real imm26 x (next x)) (controls : CallerControls x)
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
        ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) x fin ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
          fin.mem = x.mem ∧ fin.regs.gpr[30] = x.regs._PC + 4#64 ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) := by
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, gprEq, lrEq, spEq, finMem, sys, gcs⟩ :=
    entry_class_next_v3_blL real spec config rows mapping imm26 x inv.v2.v1.pins (next x)
      (offset (k + 1)) tail controls inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩,
    HeapV2StepCerts.RegBind.carry_step hk (bl_holds upd gprEq spEq) inv.regBind, ?_, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩,
    bl_holds upd gprEq spEq, HeapV2StepCerts.ValBind.veff_none veff x fin, finMem, lrEq, gcs⟩
  · intro e he n hn i hi; rw [finMem]; exact inv.present e he n hn i hi
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [ChainInvV3.hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

theorem rich_branch_ret_atL (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = []) (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyRet.W Rn) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (hlow : (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (target : x.regs.gpr[(GPRSummary.key Rn.toNat).val] = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping (EntryBodyRet.W Rn) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
        ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) x fin ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
          fin.mem = x.mem ∧ fin.regs.gpr = x.regs.gpr ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) := by
  refine RtB2.RichG.rich_branch_at real spec config rows mapping m scope image loadBase separated base offset
    budget p k room hk page aligned (EntryBodyRet.W Rn) 94 upd0 veff (fun _ => base + offset (k + 1))
    x inv ?_ (fun _ _ => rfl) obligations
  intro fetched enc0 b pins bp input guard quiet it ss
  obtain ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, _, _, _, _, _, nonProj, _, pcS,
      gpr, spr, gic⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyRet.native_tail_x real x fetched enc0 Rn hRn noEret pins bp input guard b quiet it ss
      hlow
  exact ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, gic, pcS.trans target, nonProj,
    gpr, spr⟩

#print axioms bl_tailL
#print axioms entry_class_next_v3_blL
#print axioms rich_bl_atL
#print axioms rich_branch_ret_atL
end RtB3.RichH

namespace HeapV2StepCerts.RichH
open NativeEntryCallerParts
/-- One BL step from its plan word (generic in k). -/
theorem richBl_at_ptL (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (k : Nat) (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (aligned : (ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf k).toNat % 4 = 0)
    (imm26 : BitVec 26) (upd : RegBind.upds k = [(.x 30, .drop)])
    (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (off wordNat : Nat) (member : (off, wordNat) ∈ HeapV2Plan.codeWords)
    (here : ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf k = BitVec.ofNat 64 (0x10278 + off))
    (wordEq : NativeEntryCallerDispatch.Bl.word imm26 = BitVec.ofNat 32 wordNat)
    (land : ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf k + sign_extend (imm26 ++ 0#2) 64 =
      ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (k + 1))
    (low : (base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (k + 1)).toNat < 2 ^ 55)
    (x : NativeState) (inv : ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins k x) (controls : CallerControls x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins (k + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) x fin ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
          fin.mem = x.mem ∧ fin.regs.gpr[30]'(by decide) = x.regs._PC + 4#64 ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) := by
  have placedNext : ∀ x, ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins k x →
      blTarget imm26 x = base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (k + 1) := by
    intro x inv
    rw [NativeEntryCallerRegisters.bl_target, inv.v2.v1.pc, BitVec.add_assoc, land]
  exact RtB3.RichH.rich_bl_atL real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins k room hk page aligned imm26 upd veff
    (fun x => blTarget imm26 x) x inv
    (RtB3.RichH.bl_tailL real imm26 x (by rw [placedNext x inv]; exact low))
    controls placedNext
    (fun x inv => MemNext.memFetch spec config rows mapping base budget k pins table static off wordNat
      member here _ wordEq x inv.v2)

/-- step 15 @+0x3c BL 0x9400003b (imm26 = 59: callee at entry offset 296) -/
theorem richBl_15_atL (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 15 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (15 + 1)).toNat < 2 ^ 55)
    (x : NativeState) (inv : ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 15 x) (controls : CallerControls x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins (15 + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds 15) x fin ∧ HeapV2StepCerts.ValBind.VEff 15 x fin ∧
          fin.mem = x.mem ∧ fin.regs.gpr[30]'(by decide) = x.regs._PC + 4#64 ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) :=
  richBl_at_ptL real spec config rows mapping base budget pins table static 15 room (by decide) page
    (by decide +kernel) (59#26) (by decide) (by decide) 60 2483028027 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) low x inv controls

/-- step 150 @+0x4c BL 0x9400004b (imm26 = 75: callee at entry offset 376) -/
theorem richBl_150_atL (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 150 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (150 + 1)).toNat < 2 ^ 55)
    (x : NativeState) (inv : ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 150 x) (controls : CallerControls x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins (150 + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds 150) x fin ∧ HeapV2StepCerts.ValBind.VEff 150 x fin ∧
          fin.mem = x.mem ∧ fin.regs.gpr[30]'(by decide) = x.regs._PC + 4#64 ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) :=
  richBl_at_ptL real spec config rows mapping base budget pins table static 150 room (by decide) page
    (by decide +kernel) (75#26) (by decide) (by decide) 76 2483028043 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) low x inv controls

/-- step 252 @+0x58 BL 0x9400004e (imm26 = 78: callee at entry offset 400) -/
theorem richBl_252_atL (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 252 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (252 + 1)).toNat < 2 ^ 55)
    (x : NativeState) (inv : ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 252 x) (controls : CallerControls x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins (252 + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds 252) x fin ∧ HeapV2StepCerts.ValBind.VEff 252 x fin ∧
          fin.mem = x.mem ∧ fin.regs.gpr[30]'(by decide) = x.regs._PC + 4#64 ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) :=
  richBl_at_ptL real spec config rows mapping base budget pins table static 252 room (by decide) page
    (by decide +kernel) (78#26) (by decide) (by decide) 88 2483028046 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) low x inv controls

#print axioms richBl_at_ptL
#print axioms richBl_15_atL
#print axioms richBl_150_atL
#print axioms richBl_252_atL
end HeapV2StepCerts.RichH
