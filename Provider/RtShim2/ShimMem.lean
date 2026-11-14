-- (H-P13 (3),): the generic shim MEMORY step. ShimCtx is Memory's FetchedCtx with the
-- body RegBind/DataPresent replaced by the shim's slot facts (slot bytes present, SP = p.sp);
-- entry_shim_mem is Memory's entry_mem_next_v3 over ShimCtx (fetch half unchanged); memS_Stp / memS_Ldp are
-- memV_Stp / memV_Ldp over consumerMapShim via SlotPrem.prem_shimStp/Ldp; plan_shim_mem carries ShimInv.
import HeapV2StepCerts.MemStepV3
import RtShim2.ShimInv
import RtShim2.SlotPrem
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts HeapV2StepCerts.MemNext
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace RtShim2.ShimMem

/-- What the shim memory tails need at the fetched state. -/
structure ShimCtx {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (p : HeapV2E17.Pins)
    (x : NativeState) : Prop where
  closed : ClosedMembershipAt spec config rows mapping m x
  slot : RtShim.SlotPrem.ShimSlotPresent p mapping x
  spAt : x.regs.SP_EL0 = BitVec.ofNat 64 p.sp
  raw : RawImageAt spec.imageRows x.mem
  noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
    NoUpdateRows {spec.params with haft := hostHAFT x.regs} acc spec.imageRows = true
  post2 : MemM1.MemReadD2.PostRegs2 x.regs
  mode : HostEL0ModeAt x.regs
  debug : ExistingE11DebugAt x.regs
  feat : x.regs.FeatureImpl[7] = true ∧ x.regs.FeatureImpl[3] = false ∧
    x.regs.FeatureImpl[227] = false ∧ x.regs.FeatureImpl[111] = true
  dcache : currentDCache x.regs = true

run_cmd do
  IO.eprintln "CURRENT_DECL RtShim2.ShimMem.entry_shim_mem"
  (← IO.getStderr).flush

set_option maxHeartbeats 200000 in
theorem entry_shim_mem (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (us : List (RegBind.Reg × RegBind.Upd))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (p : HeapV2E17.Pins) (D : Nat → Prop)
    (tail : MemTailVAt real spec config rows (ShimCtx spec config rows mapping m p) D w writes K s next us)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (nextPlaced : next = base + nextOffset)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (placedImg : MemReloc.ImageOn scope image s loadBase mapping)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    (bp : Crypto.BranchV2.BranchPinsV2PA s)
    (rawS : RawImageAt spec.imageRows s.mem)
    (noUpdS : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (slotS : RtShim.SlotPrem.ShimSlotPresent p mapping s) (spS : s.regs.SP_EL0 = BitVec.ofNat 64 p.sp)
    (post2S : MemM1.MemReadD2.PostRegs2 s.regs) (modeS : HostEL0ModeAt s.regs)
    (edebugS : ExistingE11DebugAt s.regs)
    (featS : s.regs.FeatureImpl[7] = true ∧ s.regs.FeatureImpl[3] = false ∧
      s.regs.FeatureImpl[227] = false ∧ s.regs.FeatureImpl[111] = true)
    (dcacheS : currentDCache s.regs = true)
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
      word' = w) :
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
      RegBind.Holds us s fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun x => s.mem[x]?) (fun x => fin.mem[x]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written) ∧
      (∀ x : Nat, (s.mem[x]?).isSome → (fin.mem[x]?).isSome) ∧
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
  -- the fetched-state context for the memory tail
  have memNoUpd : translated.mem = (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).mem :=
    (noUpdCond rawS (by
      rw [rawOf acc]
      exact HeapV2StepCerts.RawFetch.noUpd_read noUpdS acc (actual_ifetch_flags actualAcc).2.2.1)).2.2
  have finalMem : final.mem = s.mem := fmem.trans memNoUpd
  have gprFinal : final.regs.gpr = s.regs.gpr := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.gpr) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have spFinal : final.regs.SP_EL0 = s.regs.SP_EL0 := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have sysF : SysEq2 s.regs final.regs := EntryBranchPins.sysEq2_symm _ _ finput.sys
  have ctx : ShimCtx spec config rows mapping m p final :=
    { closed := closedFinal
      slot := fun n hn i hi => by rw [finalMem]; exact slotS n hn i hi
      spAt := spFinal.trans spS
      raw := by rw [finalMem]; exact rawS
      noUpd := fun wr acc hs => by rw [hostHAFT_eq sysF]; exact noUpdS wr acc hs
      post2 := HeapV2StepCerts.MemConfigFrame.post2 sysF.feat sysF.el sysF.nrw sysF.scr sysF.hcr sysF.sctlr sysF.spe post2S
      mode := HeapV2StepCerts.MemConfigFrame.mode sysF.feat sysF.el sysF.scr sysF.hcr modeS
      debug := HeapV2StepCerts.MemConfigFrame.debug sysF.mdscr sysF.hde edebugS
      feat := by rw [sysF.feat]; exact featS
      dcache := HeapV2StepCerts.MemConfigFrame.dcache sysF.sctlr dcacheS }
  obtain ⟨sp, a, fin, written, hook, tail, frame, finQuiet, finStep, sys, wo, sepT, inD, gic, pc, np, keep, holdsF⟩ :=
    tail final enc0 budget fpins finput guard fquiet it ss curFinal ctx
  have post := entry_spec_post final sp (budget + 1) fquiet hook
  have finPins := NativeEntryTail.EntryPins.of_scalar fin finStep
  have curFin := ArmBridge.CruxGenGuarded.EntryBtiNext.tail_current_writes _ _ _ final sp a fin curFinal post.frame frame sys np
    (finPins.el.trans fpins.el.symm) (finPins.nrw.trans fpins.nrw.symm) written wo sepT
  -- register-field chains fin ← a ← action ← sp ← final ← entry
  have toFinal64 : ∀ k : Bank_BitVec_64, (∀ x : Regs, (eraseE20 x).bank_BitVec_64 k = x.bank_BitVec_64 k) →
      a.regs.bank_BitVec_64 k = final.regs.bank_BitVec_64 k := by
    intro k hk
    rw [congrFun frame.b64 k]
    show sp.regs.bank_BitVec_64 k = _
    exact frame_pres_E20 (fun x => x.bank_BitVec_64 k) hk post.frame
  have mdscrFinal : final.regs.bank_BitVec_64 .MDSCR_EL1 = s.regs.bank_BitVec_64 .MDSCR_EL1 := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .MDSCR_EL1) _ _ s (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]
  have mdscr : fin.regs.bank_BitVec_64 .MDSCR_EL1 = s.regs.bank_BitVec_64 .MDSCR_EL1 := by
    rw [sys.mdscr, toFinal64 _ (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]), mdscrFinal]
  have hdeFinal : _get_EDSCR_Type_HDE (final.regs.bank_BitVec_32 ._EDSCR) =
      _get_EDSCR_Type_HDE (s.regs.bank_BitVec_32 ._EDSCR) := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR)) _ _ s
      (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne, RegMap.set_same]
    exact ArmBridge.CruxCore.hde_pipeadv _ _
  have hdeA : _get_EDSCR_Type_HDE (a.regs.bank_BitVec_32 ._EDSCR) =
      _get_EDSCR_Type_HDE (final.regs.bank_BitVec_32 ._EDSCR) := by
    rw [congrFun frame.b32 ._EDSCR]
    simp (disch := decide) only [actionState, RegMap.set_ne]
    exact frame_pres_E20 (fun x => _get_EDSCR_Type_HDE (x.bank_BitVec_32 ._EDSCR)) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) post.frame
  have featFin : fin.regs.FeatureImpl = s.regs.FeatureImpl := by
    rw [sys.feat, frame.feat]
    show sp.regs.FeatureImpl = _
    rw [frame_pres_E20 (fun x => x.FeatureImpl) (fun x => by
      simp (disch := decide) only [eraseE20]) post.frame, hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.FeatureImpl) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have gicFin : fin.regs.bank_Option_InterruptID .__GIC_Pending = none := by
    rw [gic, frame.gic]
    show sp.regs.bank_Option_InterruptID .__GIC_Pending = _
    rw [post.gic, hregs]
    rw [ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_Option_InterruptID .__GIC_Pending) _ _ s (fun _ _ => rfl)
      (fun _ => rfl) rfl]
    exact hGIC
  have closedFin := closed_tail _ _ _ final sp a fin closedFinal post.frame frame sys np
  have placedFin := HeapV2StepCerts.placed_class_writes wo
    (fun off pa hs hm hw => codeD off pa hs hm (inD pa hw)) placedFinal
  have bpFinal := EntryFetchedBranch.fetched_branch_pins acc (translateCurrent out) s final stepPins hregs bp
  have holdsS := RegBind.Holds.of_prefix gprFinal spFinal holdsF
  have sysS : SysEq2 s.regs fin.regs :=
    sysEq2_trans _ _ _ sysF
      (ClassNextV3.class_sys _ writes K final sp a fin budget fpins fquiet hook frame sys)
  have bpFin := ClassBranchPins.class_branch_pins _ writes K final sp a fin budget fpins fquiet hook frame sys np
    finStep bpFinal
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin,
    closed_before_fetch fin closedFin, placedFin, bpFin, holdsS,
    ⟨written, by rw [← finalMem]; exact wo, sepT⟩, fun x h => keep x (by rw [finalMem]; exact h), sysS⟩
  · rw [pc, nextPlaced]
  · rw [mdscr]; exact debug.mde
  · rw [sys.hde, hdeA, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩


#print axioms entry_shim_mem

/-- The slot's 16 bytes. -/
def slotBytes (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (a : Nat) : Prop :=
  ∃ n, mapping (BitVec.ofNat 64 p.sp) = some n ∧ n ≤ a ∧ a < n + 16

run_cmd do
  IO.eprintln "CURRENT_DECL RtShim2.ShimMem.memS_Stp"
  (← IO.getStderr).flush

/-- s3 tail: STP Rt, Rt2, [SP] over the shim context. -/
theorem memS_Stp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : RtShim.SlotPrem.ShimSlotStatic p mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0)
    (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Stp.selected Rt Rt2 0#7) 31 12 == 879088#20) = false)
    (source : NativeState) :
    MemTailVAt real spec config rows (ShimCtx spec config rows mapping (HeapV2E17.consumerMapShim S p base mapping table) p)
      (slotBytes p mapping) (NativeEntryBodyDispatch.Stp.selected Rt Rt2 0#7) NativeEntryBodyMem.Stp.writes 617 source
      (source.regs._PC + 4#64) [] := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, outside⟩ :=
    RtShim.SlotPrem.prem_shimStp fetched ctx.closed static ctx.post2 ctx.spAt spAligned
  have hva : ArmCertMem.LdpEval.ldpAddr fetched 0#7 = BitVec.ofNat 64 p.sp :=
    (RtShim.SlotPrem.shim_addr fetched).trans ctx.spAt
  have inD : ∀ i < 16, slotBytes p mapping (pa.toNat + i) := fun i hi =>
    ⟨pa.toNat, by rw [← hva]; exact mapped, by omega, by omega⟩
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Stp real spec config rows mapping source fetched enc0 0#7 Rt Rt2 hRt hRt2 noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio outside (slotBytes p mapping) inD ctx.raw
      (fun acc sh => ctx.noUpd true acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtShim2.ShimMem.memS_Ldp"
  (← IO.getStderr).flush

/-- s7 tail: LDP Rt, Rt2, [SP] over the shim context. -/
theorem memS_Ldp (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {S : Nat × Nat × Int × Nat × Bool → Prop} {p : HeapV2E17.Pins} {base : Nat} {table : Nat → Prop}
    (static : RtShim.SlotPrem.ShimSlotStatic p mapping (rowsFootprint spec.imageRows))
    (spAligned : (BitVec.ofNat 64 p.sp).toNat % 16 = 0)
    (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 0#7) 31 12 == 879088#20) = false)
    (source : NativeState) :
    MemTailVAt real spec config rows (ShimCtx spec config rows mapping (HeapV2E17.consumerMapShim S p base mapping table) p)
      (slotBytes p mapping) (NativeEntryBodyDispatch.Ldp.selected Rt Rt2 0#7) NativeEntryBodyMem.Ldp.writes 611 source
      (source.regs._PC + 4#64) (RegBind.updLdp Rt Rt2) := by
  intro fetched enc0 budget pins input guard quiet it ss current ctx
  obtain ⟨perAcc, hsp, hal, pa, mapped, mmio, data, bytes⟩ :=
    RtShim.SlotPrem.prem_shimLdp fetched ctx.closed static ctx.slot ctx.spAt spAligned
  obtain ⟨sp, a, fin, written, _, hook, run, frame, q, fp, sys, wo, sep, _, _, gic, pc, np, keep, holds, inW⟩ :=
    MemTail.mem_tailD_Ldp real spec config rows mapping source fetched enc0 0#7 Rt Rt2 hRt hRt2 hRtt noEret
      pins input guard budget quiet it ss current perAcc ctx.mode ctx.debug ctx.post2 ctx.feat.1 ctx.feat.2.1
      ctx.feat.2.2.1 ctx.feat.2.2.2 ctx.dcache hsp hal pa mapped mmio data bytes (slotBytes p mapping) ctx.raw
      (fun acc sh => ctx.noUpd false acc sh)
  exact ⟨sp, a, fin, written, hook, run, frame, q, fp, sys, wo, sep, inW, gic, pc, np, keep, holds⟩

run_cmd do
  IO.eprintln "CURRENT_DECL RtShim2.ShimMem.plan_shim_mem"
  (← IO.getStderr).flush

/-- One actual shim MEMORY step: ShimInv k → ShimInv (k+1), given the slot facts at x (slot present, SP = p.sp);
exports Holds us, the write frame (written ⊆ D, separated from the table), presence kept, SysEq2. -/
theorem plan_shim_mem (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (p : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (us : List (RegBind.Reg × RegBind.Upd))
    (next : NativeState → BitVec 64)
    (x : NativeState) (inv : RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset budget k x)
    (slotX : RtShim.SlotPrem.ShimSlotPresent p mapping x) (spX : x.regs.SP_EL0 = BitVec.ofNat 64 p.sp)
    (tail : MemTailVAt real spec config rows (ShimCtx spec config rows mapping m p) D w writes K x (next x) us)
    (nextPlaced : next x = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset budget (k + 1) fin ∧
      RegBind.Holds us x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written) ∧
      (∀ a : Nat, (x.mem[a]?).isSome → (fin.mem[a]?).isSome) ∧ SysEq2 x.regs fin.regs := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, holds, ⟨written, wo, sep⟩, keep, sys⟩ :=
    entry_shim_mem real spec config rows mapping w writes K x inv.v2.v1.pins (next x)
      (offset (k + 1)) us m p D tail inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
      inv.v2.v1.current inv.v2.closed scope image loadBase inv.v2.placed separated codeD inv.v2.branch
      inv.raw inv.noUpd slotX spX inv.post2 inv.mode inv.debug inv.feat inv.dcache
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩,
    RawFetch.raw_writes inv.raw wo sep, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩, holds, ⟨written, wo, sep⟩, keep, sys⟩
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms memS_Stp
#print axioms memS_Ldp
#print axioms plan_shim_mem
end RtShim2.ShimMem
