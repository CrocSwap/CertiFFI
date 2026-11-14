-- Actual fetched branch continuation under the current profile.
-- Adapted from the signed RtBranch.BranchStepV3 route, with exact events and TCO.
import RtBranch.BranchStepV3
import RtB4.EvShapeBridge
import CurrentInv
import HeapControl
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace ReleaseProfile.DefaultBranchEvent
open HeapV2StepCerts.BranchStepV3
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

#check "CURRENT_DECL BranchTailEvent"
def BranchTailEvent (real : Type) [Sail.SailReal real] (w : BitVec 32) (K : Int) (source : NativeState)
    (next : BitVec 64) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → TranslateSpan.BranchMTE2.Pins fetched → NativeEntryInput.Input source fetched →
    MetadataGuard fetched → HookQuiet (budget + 1) fetched → fetched.regs.ShouldAdvanceIT = false →
    fetched.regs.ShouldAdvanceSS = true →
    ∃ sp a fin, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      nativeTail real source w enc0 fetched = .ok () fin ∧
      ArmBridge.CruxGenBr.ActFrameBr (actionState w sp K) a ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧ BrSysEq a.regs fin.regs ∧
      fin.mem = fetched.mem ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = fetched.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs._PC = next ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs ∧
      fin.regs.gpr = fetched.regs.gpr ∧ fin.regs.SP_EL0 = fetched.regs.SP_EL0 ∧
      fin.regs.PSTATE.N = fetched.regs.PSTATE.N ∧ fin.regs.PSTATE.Z = fetched.regs.PSTATE.Z ∧
      fin.regs.PSTATE.C = fetched.regs.PSTATE.C ∧ fin.regs.PSTATE.V = fetched.regs.PSTATE.V ∧
      fin.regs._Z = fetched.regs._Z ∧ fin.events = fetched.events ∧ NativeMteTagCheck.ChoiceDelta fetched fin 0

set_option maxHeartbeats 200000 in
theorem entry_branch_event (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (tail : BranchTailEvent real w K s next)
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
    (bp : TranslateSpan.BranchMTE2.Pins s)
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
      word' = w)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin,
      modelStep real s = .ok () fin ∧
      StepPins fin ∧ HookQuiet budget fin ∧
      CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState fin) ∧
      fin.regs._PC = base + nextOffset ∧
      E11Debug.E11CheckDebug fin.regs ∧ EntryFeatures fin.regs ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = none ∧
      ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState fin) ∧
      MemReloc.ImageOn scope image fin loadBase mapping ∧
      fin.regs.gpr = s.regs.gpr ∧ fin.regs.SP_EL0 = s.regs.SP_EL0 ∧ fin.mem = s.mem ∧ SysEq2 s.regs fin.regs ∧
      BrSysEq s.regs fin.regs ∧ fin.regs.PSTATE.TCO = s.regs.PSTATE.TCO ∧
      fin.regs.PSTATE.N = s.regs.PSTATE.N ∧ fin.regs.PSTATE.Z = s.regs.PSTATE.Z ∧
      fin.regs.PSTATE.C = s.regs.PSTATE.C ∧ fin.regs.PSTATE.V = s.regs.PSTATE.V ∧
      fin.regs._Z = s.regs._Z ∧ StepEvents.EvShape spec mapping [] s fin ∧
      fin.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 ∧ RtPremC.CtlRel spec s fin ∧
      NativeMteTagCheck.ChoiceDelta s fin 0 := by
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
  have bpFinal := TranslateSpan.BranchMTE2.pins_step s final bp (EntryBranchPins.sysEq2_symm _ _ finput.sys)
    fpins (EntryFetchedBranch.fetched_brSysEq acc (translateCurrent out) s final hregs)
  obtain ⟨sp, a, fin, hook, tail, frame, finQuiet, finStep, sys, _brsys, mem, gicF, pc, np, gprF, spF, nF, zF, cF, vF, vzF, ev, tailChoice⟩ :=
    tail final enc0 budget fpins bpFinal finput guard fquiet it ss
  have post := entry_spec_post final sp (budget + 1) fquiet hook
  have finPins := NativeEntryTail.EntryPins.of_scalar fin finStep
  have curFin := tail_current_br _ _ final sp a fin curFinal post.frame frame sys np
    (finPins.el.trans fpins.el.symm) (finPins.nrw.trans fpins.nrw.symm) (mem)
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
    rw [gicF, hregs]
    rw [ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_Option_InterruptID .__GIC_Pending) _ _ s (fun _ _ => rfl)
      (fun _ => rfl) rfl]
    exact hGIC
  have closedFin := closed_tail_br _ _ final sp a fin closedFinal post.frame frame sys np
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
  have sysS : SysEq2 s.regs fin.regs :=
    sysEq2_trans _ _ _ (EntryBranchPins.sysEq2_symm _ _ finput.sys)
      (class_sys_br _ K final sp a fin budget fpins fquiet hook frame sys)
  have brFin := EntryBranchPins.brSysEq_trans _ _ _
    (EntryBranchPins.brSysEq_trans _ _ _
      (EntryBranchPins.brSysEq_trans _ _ _
        (EntryBranchPins.brSysEq_trans _ _ _
          (EntryFetchedBranch.fetched_brSysEq acc (translateCurrent out) s final hregs)
          (EntryBranchPins.brSysEq_e20 _ _ post.frame)) (EntryBranchPins.brSysEq_action w' sp K))
      (frame_branch_br _ a frame)) (ClassBranchPins.npe_branch _ _ np)
  have tcoFetch : final.regs.PSTATE.TCO = s.regs.PSTATE.TCO := by
    rw [hregs]
    exact EntryBtiNext.fetched_field (fun r => r.PSTATE.TCO) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have tcoAction : a.regs.PSTATE.TCO = (actionState w' sp K).regs.PSTATE.TCO := by
    have h := congrArg ProcState.TCO frame.pse
    exact h
  have tcoPmu : (actionState w' sp K).regs.PSTATE.TCO = final.regs.PSTATE.TCO :=
    congrArg ProcState.TCO (PMUFrame.of_E20 post.frame).pstate
  have tcoEpilogue : fin.regs.PSTATE.TCO = a.regs.PSTATE.TCO := by
    have h := congrArg (fun r : Regs => r.PSTATE.TCO) np
    exact h
  have events := RtB4.EvShapeBridge.evShape_of_fetchRun spec config rows mapping _ s fin stepPins features debug current
      (pc_low_of_placement _ base offset placed page word) ⟨queryOf, rawOf, vaOf, mmio, present, perAcc, code⟩
      rawS noUpdS nodup ⟨final, _, run, ev⟩
  have gcs : fin.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 := by
    rw [ClosedChain.np_b64 np _ (by decide), toFinal64 _ (fun r => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]), hregs]
    exact EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .SCR_EL3) _ _ s
      (fun _ _ => rfl) (fun _ => rfl) (by simp (disch := decide) only [beforeFetchState, RegMap.set_ne])
  rw [hregs] at nF zF cF vF vzF
  have fetchedChoice := HeapControl.fetch_choice real spec config rows mapping w' s final
    stepPins features debug base offset placed page word current
    ⟨queryOf, rawOf, vaOf, mmio, present, perAcc, code⟩ ⟨_, run⟩
  have finalChoice : NativeMteTagCheck.ChoiceDelta s fin 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans fetchedChoice tailChoice
  have control : RtPremC.CtlRel spec s fin :=
    RtPremC.CtlRel.of_mem
      ((RtPremC.tailBr_ctl final sp a fin budget fquiet hook w' K frame np).trans
        (by rw [hregs]; exact RtPremC.ctl_fetched acc _ s)) finMem
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin, closed_before_fetch fin closedFin, placedFin,
    gprF.trans gprFinal, spF.trans spFinal, finMem, sysS, brFin,
    tcoEpilogue.trans (tcoAction.trans (tcoPmu.trans tcoFetch)),
    nF.trans (EntryBtiNext.fetched_field (fun r => r.PSTATE.N) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    zF.trans (EntryBtiNext.fetched_field (fun r => r.PSTATE.Z) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    cF.trans (EntryBtiNext.fetched_field (fun r => r.PSTATE.C) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    vF.trans (EntryBtiNext.fetched_field (fun r => r.PSTATE.V) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl),
    vzF.trans (EntryBtiNext.fetched_field (fun r => r._Z) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl), events, gcs, control, finalChoice⟩
  · rw [pc, nextPlaced]
  · rw [mdscr]; exact debug.mde
  · rw [sys.hde, hdeA, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

#print axioms entry_branch_event
end ReleaseProfile.DefaultBranchEvent
