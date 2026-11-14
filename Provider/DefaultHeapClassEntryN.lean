import HeapV2StepCerts.TailWF
import CurrentInv
import HeapControl
import RtB4.EvShapeBridge
import HeapV2StepCerts.ActionTransport
import HeapV2StepCerts.BodyHolds
import HeapV2StepCerts.CodeScope
import HeapV2StepCerts.MemHolds
import HeapV2StepCerts.RegBindCore
import HeapV2StepCerts.Straight
import HeapV2StepCerts.ValueTailDef
import Bridge.CruxGenGuarded.ClosedChain
import Bridge.CruxGenGuarded.EntryFetchedBranch
import Bridge.CruxGenGuarded.ClassBranchPins
import HeapV2StepCerts.Carry
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.TailW
import HeapV2StepCerts.TailWE
import HeapV2StepCerts.TailWN
import Bridge.CruxGenGuarded.ClassNextV3
import HeapV2StepCerts.RawFetch
import ArmCertWalk.NativeFetchPreservingEvents
import ArmCertWalk.AccessTransfer
import Bridge.CruxGenGuarded.BookkeepingTransport
import Bridge.CruxGenGuarded.FrameTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace ReleaseProfile.DefaultHeapClassEntryN
open HeapV2StepCerts
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/-! ChainInv v4 E class step (ClassNextV4 over Memory's TailWE.ClassTailWAt: also exports the
actual fetch run and the silent tail's fin.events = f.events, for EvShape). ChainInv v4 class step (GENERATED from ClassNextV3 with Memory's value-effect tail
TailW.ClassTailWAt; additionally exports ValBind.VEff kk s fin). ChainInv v3 step (GENERATED from ClassNextV2 by switching to the _events fetch and the
value-carrying ClassTailVAt): additionally carries the register-binding Holds, memory
equality fin.mem = s.mem and SysEq2 s fin. ChainInv v2 step
(GENERATED from ClosedChain.entry_class_next_closed by adding three
carried facts): the actual fixed-class step also preserves code placement
(Memory's HeapV2StepCerts.placed_fetch/placed_class over the ACTUAL fetch's clean
translation and the class tail's memory frame) and the PA-free branch platform profile
(fetched_branch_pins + class_branch_pins). -/

run_cmd do
  IO.eprintln "CURRENT_DECL ClassNextV4E.entry_class_next_v4e"
  (← IO.getStderr).flush

set_option maxHeartbeats 200000 in
private theorem erase_tco (writes : NativeEntry.Effects.Writes) (p : ProcState) :
    (NativeEntryContract.erasePState writes p).TCO = p.TCO := by
  unfold NativeEntryContract.erasePState
  split <;> rfl

#check "CURRENT_DECL entry_class_next_zn"
set_option maxHeartbeats 200000 in
theorem entry_class_next_zn (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (us : List (HeapV2StepCerts.RegBind.Reg × HeapV2StepCerts.RegBind.Upd))
    (kk : Nat) (tail : HeapV2StepCerts.TailWE.ClassTailWNAt real w writes K s next us kk)
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
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
      TranslateSpan.BranchMTE2.Pins fin ∧
      HeapV2StepCerts.RegBind.Holds us s fin ∧ fin.mem = s.mem ∧ SysEq2 s.regs fin.regs ∧
      HeapV2StepCerts.ValBind.VEff kk s fin ∧
      fin.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 ∧
      fin.regs._Z = s.regs._Z ∧ fin.regs.PSTATE.TCO = s.regs.PSTATE.TCO ∧
      StepEvents.EvShape spec mapping [] s fin ∧ RtPremC.CtlRel spec s fin ∧
      fin.regs.PSTATE.N = 0#1 ∧ fin.regs.PSTATE.C = 0#1 ∧ fin.regs.PSTATE.V = 0#1 := by
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
  obtain ⟨sp, a, fin, hook, tail, frame, finQuiet, finStep, sys, mem, gic, pc, np, evF, zF, holdsF, veffF, hnF, hcF, hvF⟩ :=
    tail final enc0 budget fpins finput guard fquiet it ss
  have post := entry_spec_post final sp (budget + 1) fquiet hook
  have finPins := NativeEntryTail.EntryPins.of_scalar fin finStep
  have curFin := ArmBridge.CruxGenGuarded.EntryBtiNext.tail_current _ _ _ final sp a fin curFinal post.frame frame sys np
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
  have gcsFinal : final.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .SCR_EL3) _ _ s (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]
  have gcs : fin.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 := by
    rw [ClosedChain.np_b64 np .SCR_EL3 (by decide),
      toFinal64 _ (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]), gcsFinal]
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
  have holdsS := HeapV2StepCerts.RegBind.Holds.of_prefix gprFinal spFinal holdsF
  have zFinal : final.regs._Z = s.regs._Z := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r._Z) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have veffS := HeapV2StepCerts.ValBind.VEff.of_prefix gprFinal veffF
  have sysS : SysEq2 s.regs fin.regs :=
    sysEq2_trans _ _ _ (EntryBranchPins.sysEq2_symm _ _ finput.sys)
      (ClassNextV3.class_sys _ writes K final sp a fin budget fpins fquiet hook frame sys)
  have brFetch := EntryFetchedBranch.fetched_brSysEq acc (translateCurrent out) s final hregs
  have brPmu := EntryBranchPins.brSysEq_e20 _ _ post.frame
  have brMeta := EntryBranchPins.brSysEq_action w' sp K
  have brAct := ClassBranchPins.frame_branch writes _ a frame
  have brEpilogue := ClassBranchPins.npe_branch _ _ np
  have brFin := EntryBranchPins.brSysEq_trans _ _ _
    (EntryBranchPins.brSysEq_trans _ _ _
      (EntryBranchPins.brSysEq_trans _ _ _ (EntryBranchPins.brSysEq_trans _ _ _ brFetch brPmu) brMeta) brAct) brEpilogue
  have tcoFetch : final.regs.PSTATE.TCO = s.regs.PSTATE.TCO := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.TCO)
      _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have tcoAction : a.regs.PSTATE.TCO = (actionState w' sp K).regs.PSTATE.TCO := by
    have h := congrArg ProcState.TCO frame.pse
    rwa [erase_tco,erase_tco] at h
  have tcoPmu : (actionState w' sp K).regs.PSTATE.TCO = final.regs.PSTATE.TCO :=
    congrArg ProcState.TCO (PMUFrame.of_E20 post.frame).pstate
  have tcoEpilogue : fin.regs.PSTATE.TCO = a.regs.PSTATE.TCO := by
    have h := congrArg (fun r : Regs => r.PSTATE.TCO) np
    exact h
  have tcoFin := tcoEpilogue.trans (tcoAction.trans (tcoPmu.trans tcoFetch))
  have bpFin := TranslateSpan.BranchMTE2.pins_step s fin bp sysS finStep brFin
  have events := RtB4.EvShapeBridge.evShape_of_fetchRun spec config rows mapping _ s fin stepPins features debug current
    (pc_low_of_placement _ base offset placed page word) ⟨queryOf, rawOf, vaOf, mmio, present, perAcc, code⟩
    rawS noUpdS nodup ⟨final, _, run, evF⟩
  have control : RtPremC.CtlRel spec s fin :=
    RtPremC.CtlRel.of_mem
      ((RtPremC.tail_ctl final sp a fin budget fquiet hook w' K frame np).trans
        (by rw [hregs]; exact RtPremC.ctl_fetched acc _ s)) finMem
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin, closed_before_fetch fin closedFin, placedFin, bpFin, holdsS, finMem, sysS, veffS, gcs, zF.trans zFinal, tcoFin, events, control, hnF, hcF, hvF⟩
  · rw [pc, nextPlaced]
  · rw [mdscr]; exact debug.mde
  · rw [sys.hde, hdeA, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

#print axioms entry_class_next_zn

#check "CURRENT_DECL entry_class_next_zf"
set_option maxHeartbeats 200000 in
theorem entry_class_next_zf (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (us : List (HeapV2StepCerts.RegBind.Reg × HeapV2StepCerts.RegBind.Upd))
    (kk : Nat) (tail : HeapV2StepCerts.TailWE.ClassTailWFAt real w writes K s next us kk)
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
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
      TranslateSpan.BranchMTE2.Pins fin ∧
      HeapV2StepCerts.RegBind.Holds us s fin ∧ fin.mem = s.mem ∧ SysEq2 s.regs fin.regs ∧
      HeapV2StepCerts.ValBind.VEff kk s fin ∧
      fin.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 ∧
      fin.regs._Z = s.regs._Z ∧ fin.regs.PSTATE.TCO = s.regs.PSTATE.TCO ∧
      StepEvents.EvShape spec mapping [] s fin ∧ RtPremC.CtlRel spec s fin ∧
      HeapV2StepCerts.Flags.nzcv fin.regs = HeapV2StepCerts.Flags.nzcv s.regs := by
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
  obtain ⟨sp, a, fin, hook, tail, frame, finQuiet, finStep, sys, mem, gic, pc, np, evF, zF, holdsF, veffF, flF⟩ :=
    tail final enc0 budget fpins finput guard fquiet it ss
  have post := entry_spec_post final sp (budget + 1) fquiet hook
  have finPins := NativeEntryTail.EntryPins.of_scalar fin finStep
  have curFin := ArmBridge.CruxGenGuarded.EntryBtiNext.tail_current _ _ _ final sp a fin curFinal post.frame frame sys np
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
  have gcsFinal : final.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .SCR_EL3) _ _ s (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]
  have gcs : fin.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 := by
    rw [ClosedChain.np_b64 np .SCR_EL3 (by decide),
      toFinal64 _ (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]), gcsFinal]
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
  have holdsS := HeapV2StepCerts.RegBind.Holds.of_prefix gprFinal spFinal holdsF
  have flFinal : HeapV2StepCerts.Flags.nzcv final.regs = HeapV2StepCerts.Flags.nzcv s.regs := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => HeapV2StepCerts.Flags.nzcv r) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have zFinal : final.regs._Z = s.regs._Z := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r._Z) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have veffS := HeapV2StepCerts.ValBind.VEff.of_prefix gprFinal veffF
  have sysS : SysEq2 s.regs fin.regs :=
    sysEq2_trans _ _ _ (EntryBranchPins.sysEq2_symm _ _ finput.sys)
      (ClassNextV3.class_sys _ writes K final sp a fin budget fpins fquiet hook frame sys)
  have brFetch := EntryFetchedBranch.fetched_brSysEq acc (translateCurrent out) s final hregs
  have brPmu := EntryBranchPins.brSysEq_e20 _ _ post.frame
  have brMeta := EntryBranchPins.brSysEq_action w' sp K
  have brAct := ClassBranchPins.frame_branch writes _ a frame
  have brEpilogue := ClassBranchPins.npe_branch _ _ np
  have brFin := EntryBranchPins.brSysEq_trans _ _ _
    (EntryBranchPins.brSysEq_trans _ _ _
      (EntryBranchPins.brSysEq_trans _ _ _ (EntryBranchPins.brSysEq_trans _ _ _ brFetch brPmu) brMeta) brAct) brEpilogue
  have tcoFetch : final.regs.PSTATE.TCO = s.regs.PSTATE.TCO := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.PSTATE.TCO)
      _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have tcoAction : a.regs.PSTATE.TCO = (actionState w' sp K).regs.PSTATE.TCO := by
    have h := congrArg ProcState.TCO frame.pse
    rwa [erase_tco,erase_tco] at h
  have tcoPmu : (actionState w' sp K).regs.PSTATE.TCO = final.regs.PSTATE.TCO :=
    congrArg ProcState.TCO (PMUFrame.of_E20 post.frame).pstate
  have tcoEpilogue : fin.regs.PSTATE.TCO = a.regs.PSTATE.TCO := by
    have h := congrArg (fun r : Regs => r.PSTATE.TCO) np
    exact h
  have tcoFin := tcoEpilogue.trans (tcoAction.trans (tcoPmu.trans tcoFetch))
  have bpFin := TranslateSpan.BranchMTE2.pins_step s fin bp sysS finStep brFin
  have events := RtB4.EvShapeBridge.evShape_of_fetchRun spec config rows mapping _ s fin stepPins features debug current
    (pc_low_of_placement _ base offset placed page word) ⟨queryOf, rawOf, vaOf, mmio, present, perAcc, code⟩
    rawS noUpdS nodup ⟨final, _, run, evF⟩
  have control : RtPremC.CtlRel spec s fin :=
    RtPremC.CtlRel.of_mem
      ((RtPremC.tail_ctl final sp a fin budget fquiet hook w' K frame np).trans
        (by rw [hregs]; exact RtPremC.ctl_fetched acc _ s)) finMem
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin, closed_before_fetch fin closedFin, placedFin, bpFin, holdsS, finMem, sysS, veffS, gcs, zF.trans zFinal, tcoFin, events, control, flF.trans flFinal⟩
  · rw [pc, nextPlaced]
  · rw [mdscr]; exact debug.mde
  · rw [sys.hde, hdeA, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

#print axioms entry_class_next_zf
end ReleaseProfile.DefaultHeapClassEntryN
