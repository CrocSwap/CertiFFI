-- Actual fetched memory continuation with default controls and bounded oracle transport.
import ArmCertMemPipe.EntryMemG
import TranslateSpan.DefaultClass
import TagCheckFrames.Fetch
import NativeTagCheck.BeforeFetch
import HeapV2StepCerts.Carry
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.RawFetch
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.MemConfigFrame
import Bridge.CruxGenGuarded.ChainInvV3
import HeapV2StepCerts.DataBytes
import HeapV2StepCerts.FetchFrames
import HeapV2StepCerts.MemNextV3
import HeapV2StepCerts.Flags
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace TranslateSpan.DefaultEntryMem
open ArmCertMemPipe NativeAccess ArmBridge.CruxGen NativeMteTagCheck
open HeapV2StepCerts HeapV2StepCerts.MemNext
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3

/-- The fetched-state context for program-generic memory tails: ChainInvG's program-independent fields + X. -/
structure DefaultFetchCtx {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (X : NativeState → Prop)
    (catalogue : ControlCatalogue) (x : NativeState) : Prop where
  closed : ClosedMembershipAt spec config rows mapping m x
  prog : X x
  raw : RawImageAt spec.imageRows x.mem
  noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
    NoUpdateRows {spec.params with haft := hostHAFT x.regs} acc spec.imageRows = true
  post : MemM1.MemReadD.PostRegs x.regs
  current : CurrentS1At spec config rows x
  controls : DefaultAt catalogue x
  allowed : TagStatusOK x
  mode : HostEL0ModeAt x.regs
  debug : ExistingE11DebugAt x.regs
  feat : x.regs.FeatureImpl[7] = true ∧ x.regs.FeatureImpl[3] = false ∧
    x.regs.FeatureImpl[227] = false ∧ x.regs.FeatureImpl[111] = true
  dcache : currentDCache x.regs = true

private theorem erase_tco (writes : NativeEntry.Effects.Writes) (p : ProcState) :
    (NativeEntryContract.erasePState writes p).TCO = p.TCO := by
  unfold NativeEntryContract.erasePState
  split <;> rfl

def MemTailAt (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (Ctx : NativeState → Prop) (D : Nat → Prop)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (source : NativeState) (next : BitVec 64)
    (us : List (RegBind.Reg × RegBind.Upd)) (Pay : NativeState → NativeState → Prop) (cost : Nat) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → NativeEntryInput.Input source fetched → MetadataGuard fetched →
    HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true →
    CurrentS1At spec config rows fetched → Ctx fetched →
    ∃ (sp a fin : NativeState) (written : Nat → Prop),
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source w enc0 fetched = .ok () fin ∧
      NativeEntryContract.Frame writes (actionState w sp K) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      WritesOnly written (fun x => fetched.mem[x]?) (fun x => fin.mem[x]?) ∧
      Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ x, written x → D x) ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = next ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs ∧
      (∀ x : Nat, (fetched.mem[x]?).isSome → (fin.mem[x]?).isSome) ∧
      RegBind.Holds us fetched fin ∧ Pay fetched fin ∧
      ∃ draws, ChoiceDelta fetched fin draws ∧ draws ≤ cost

set_option maxHeartbeats 200000 in
theorem entry_mem_next_choice (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (us : List (RegBind.Reg × RegBind.Upd))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (X : NativeState → Prop) (D : Nat → Prop)
    (Pay : NativeState → NativeState → Prop)
    (catalogue : ControlCatalogue) (cost : Nat)
    (Ctx : NativeState → Prop)
    (adapt : ∀ f, DefaultFetchCtx spec config rows mapping m X catalogue f →
      ChoiceDelta s f 0 → Ctx f)
    (tail : MemTailAt real spec config rows Ctx D w writes K s next us Pay cost)
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
    (rawS : RawImageAt spec.imageRows s.mem)
    (noUpdS : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (xferX : ∀ f : NativeState, f.regs.gpr = s.regs.gpr → f.regs.SP_EL0 = s.regs.SP_EL0 → f.mem = s.mem → X f)
    (xferPay : ∀ f g : NativeState, f.regs.gpr = s.regs.gpr → f.regs.SP_EL0 = s.regs.SP_EL0 → f.mem = s.mem →
      Flags.nzcv f.regs = Flags.nzcv s.regs → Pay f g → Pay s g)
    (postS : MemM1.MemReadD.PostRegs s.regs) (modeS : HostEL0ModeAt s.regs)
    (controlsS : DefaultAt catalogue s) (allowedS : TagStatusOK s)
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
      RegBind.Holds us s fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun x => s.mem[x]?) (fun x => fin.mem[x]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)) ∧ Pay s fin ∧
      (∀ x : Nat, (s.mem[x]?).isSome → (fin.mem[x]?).isSome) ∧
      SysEq2 s.regs fin.regs ∧ BrSysEq s.regs fin.regs ∧
      fin.regs.PSTATE.TCO = s.regs.PSTATE.TCO ∧
      fin.regs.bank_BitVec_64 .TPIDR_EL0 = s.regs.bank_BitVec_64 .TPIDR_EL0 ∧
      (writes.vector = false → fin.regs._Z = s.regs._Z) ∧
      (∃ draws, ChoiceDelta s fin draws ∧ draws ≤ cost) := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, actualAcc, run, clean, bytes, fregs,
      fmem, _fev, curFinal, _, fetchChoice, _info, _walk, _leaf, _middle, _len, _traffic, _tev, noUpdCond⟩ :=
    native_fetch_current_preserving_events_choice spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  have fetchedChoice : ChoiceDelta s final 0 := by
    simpa only [Nat.zero_add] using
      choice_delta_trans (NativeTagCheck.before_fetch_choice s) fetchChoice
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
  have nzcvFinal : Flags.nzcv final.regs = Flags.nzcv s.regs := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => Flags.nzcv r) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have tcoFetch : final.regs.PSTATE.TCO = s.regs.PSTATE.TCO := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.TCO)
      _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have ctx : DefaultFetchCtx spec config rows mapping m X catalogue final :=
    { closed := closedFinal
      prog := xferX final gprFinal spFinal finalMem
      raw := by rw [finalMem]; exact rawS
      noUpd := fun wr acc hs => by rw [hostHAFT_eq sysF]; exact noUpdS wr acc hs
      post := CurrentMTE2.post_of_sys sysF postS
      current := curFinal
      controls := DefaultMTE2.controls_of_sys controlsS sysF tcoFetch
      allowed := tag_status_transport fetchedChoice allowedS
      mode := HeapV2StepCerts.MemConfigFrame.mode sysF.feat sysF.el sysF.scr sysF.hcr modeS
      debug := HeapV2StepCerts.MemConfigFrame.debug sysF.mdscr sysF.hde edebugS
      feat := by rw [sysF.feat]; exact featS
      dcache := HeapV2StepCerts.MemConfigFrame.dcache sysF.sctlr dcacheS }
  obtain ⟨sp, a, fin, written, hook, tail, frame, finQuiet, finStep, sys, wo, sepT, inD, gic, pc, np, keep, holdsF, payF, traceF⟩ :=
    tail final enc0 budget fpins finput guard fquiet it ss curFinal (adapt final ctx fetchedChoice)
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
  have holdsS := RegBind.Holds.of_prefix gprFinal spFinal holdsF
  have sysS : SysEq2 s.regs fin.regs :=
    sysEq2_trans _ _ _ sysF
      (ClassNextV3.class_sys _ writes K final sp a fin budget fpins fquiet hook frame sys)
  have brFetch := EntryFetchedBranch.fetched_brSysEq acc (translateCurrent out) s final hregs
  have brPmu := EntryBranchPins.brSysEq_e20 _ _ post.frame
  have brMeta := EntryBranchPins.brSysEq_action w' sp K
  have brAct := ClassBranchPins.frame_branch writes _ a frame
  have brEpilogue := ClassBranchPins.npe_branch _ _ np
  have brFin := EntryBranchPins.brSysEq_trans _ _ _
    (EntryBranchPins.brSysEq_trans _ _ _
      (EntryBranchPins.brSysEq_trans _ _ _ (EntryBranchPins.brSysEq_trans _ _ _ brFetch brPmu) brMeta) brAct) brEpilogue
  have tcoAction : a.regs.PSTATE.TCO = (actionState w' sp K).regs.PSTATE.TCO := by
    have h := congrArg ProcState.TCO frame.pse
    rwa [erase_tco,erase_tco] at h
  have tcoPmu : (actionState w' sp K).regs.PSTATE.TCO = final.regs.PSTATE.TCO :=
    congrArg ProcState.TCO (PMUFrame.of_E20 post.frame).pstate
  have tcoFin := (CurrentMTE2.tco_of_nonProj np).trans (tcoAction.trans (tcoPmu.trans tcoFetch))
  have tls : fin.regs.bank_BitVec_64 .TPIDR_EL0 = s.regs.bank_BitVec_64 .TPIDR_EL0 := by
    rw [ClosedChain.np_b64 np .TPIDR_EL0 (by decide),
      toFinal64 _ (fun x => by simp (disch := decide) only [eraseE20,RegMap.set_ne]),hregs]
    exact EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .TPIDR_EL0) _ _ s
      (fun _ _ => rfl) (fun _ => rfl) rfl
  have vector : writes.vector = false → fin.regs._Z = s.regs._Z := by
    intro nv
    have zEpilogue := congrArg (fun r : Regs => r._Z) np
    change fin.regs._Z = a.regs._Z at zEpilogue
    have zAction : a.regs._Z = (actionState w' sp K).regs._Z := by
      have e := congrArg (fun r : Regs => r._Z) frame.nonProj
      simp only [NativeEntry.Effects.mask,NativeEntry.Effects.erase,nv,ite_false,Bool.false_eq_true] at e
      change a.regs._Z = (actionState w' sp K).regs._Z at e
      exact e
    have zPmu : (actionState w' sp K).regs._Z = final.regs._Z := by
      change sp.regs._Z = final.regs._Z
      exact frame_pres_E20 (fun r => r._Z) (fun r => by simp (disch := decide) only [eraseE20,RegMap.set_ne]) post.frame
    have zFetch : final.regs._Z = s.regs._Z := by
      rw [hregs]
      exact EntryBtiNext.fetched_field (fun r => r._Z) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
    exact zEpilogue.trans (zAction.trans (zPmu.trans zFetch))
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin,
    closed_before_fetch fin closedFin, placedFin, holdsS,
    ⟨written, by rw [← finalMem]; exact wo, sepT, inD⟩, xferPay final fin gprFinal spFinal finalMem nzcvFinal payF,
    fun x h => keep x (by rw [finalMem]; exact h), sysS,brFin,tcoFin,tls,vector,?_⟩
  · rw [pc, nextPlaced]
  · rw [mdscr]; exact debug.mde
  · rw [sys.hde, hdeA, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

  · obtain ⟨draws,delta,bound⟩ := traceF
    exact ⟨draws,by simpa only [Nat.zero_add] using choice_delta_trans fetchedChoice delta,bound⟩

theorem entry_mem_next (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (us : List (RegBind.Reg × RegBind.Upd))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (X : NativeState → Prop) (D : Nat → Prop)
    (Pay : NativeState → NativeState → Prop)
    (catalogue : ControlCatalogue) (cost : Nat)
    (Ctx : NativeState → Prop)
    (adapt : ∀ f, DefaultFetchCtx spec config rows mapping m X catalogue f → Ctx f)
    (tail : MemTailAt real spec config rows Ctx D w writes K s next us Pay cost)
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
    (rawS : RawImageAt spec.imageRows s.mem)
    (noUpdS : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT s.regs} acc spec.imageRows = true)
    (xferX : ∀ f : NativeState, f.regs.gpr = s.regs.gpr → f.regs.SP_EL0 = s.regs.SP_EL0 → f.mem = s.mem → X f)
    (xferPay : ∀ f g : NativeState, f.regs.gpr = s.regs.gpr → f.regs.SP_EL0 = s.regs.SP_EL0 → f.mem = s.mem →
      Flags.nzcv f.regs = Flags.nzcv s.regs → Pay f g → Pay s g)
    (postS : MemM1.MemReadD.PostRegs s.regs) (modeS : HostEL0ModeAt s.regs)
    (controlsS : DefaultAt catalogue s) (allowedS : TagStatusOK s)
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
      RegBind.Holds us s fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun x => s.mem[x]?) (fun x => fin.mem[x]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)) ∧ Pay s fin ∧
      (∀ x : Nat, (s.mem[x]?).isSome → (fin.mem[x]?).isSome) ∧
      SysEq2 s.regs fin.regs ∧ BrSysEq s.regs fin.regs ∧
      fin.regs.PSTATE.TCO = s.regs.PSTATE.TCO ∧
      fin.regs.bank_BitVec_64 .TPIDR_EL0 = s.regs.bank_BitVec_64 .TPIDR_EL0 ∧
      (writes.vector = false → fin.regs._Z = s.regs._Z) ∧
      (∃ draws, ChoiceDelta s fin draws ∧ draws ≤ cost) := by
  exact entry_mem_next_choice real spec config rows mapping w writes K s stepPins next nextOffset
    us m X D Pay catalogue cost Ctx (fun f ctx _ => adapt f ctx) tail hGIC features debug
    budget quiet base offset placed page word nextPlaced current closed scope image loadBase
    placedImg separated codeD rawS noUpdS xferX xferPay postS modeS controlsS allowedS
    edebugS featS dcacheS queryOf rawOf vaOf mmio present perAcc code

#print axioms entry_mem_next_choice
#print axioms entry_mem_next
end TranslateSpan.DefaultEntryMem
