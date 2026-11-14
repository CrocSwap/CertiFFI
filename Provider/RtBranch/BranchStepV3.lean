-- one ACTUAL branch step (Cbz / B.cond / internal RET) of the heap-v2
-- plan over ChainInv v3. Branch variants of Core's class carries over ActFrameBr (the branch action frame:
-- PC/BranchTaken change, PSTATE mod NZCV, bbool mod PrevValid), Core's entry_class_next_v3 with the class tail
-- replaced by the actual branch tail (BranchTailsX = Core's native_tail + BranchFrame GPR/SP + GIC carry), and
-- plan_step3_branch with upds k = [] (all registers kept). Per-class instances: BranchStepV3Classes.
import Bridge.CruxGenGuarded.ChainInvV3
import RtBranch.BranchTailsX
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace HeapV2StepCerts.BranchStepV3
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/-- The branch action frame gives the system-register equalities SysEq2 needs. -/
theorem frame_sys_br (t u : NativeState) (h : ArmBridge.CruxGenBr.ActFrameBr t u) : SysEq2 t.regs u.regs := by
  have el : u.regs.PSTATE.EL = t.regs.PSTATE.EL := by
    have := congrArg ProcState.EL h.pse
    simpa using this
  have nrw : u.regs.PSTATE.nRW = t.regs.PSTATE.nRW := by
    have := congrArg ProcState.nRW h.pse
    simpa using this
  exact ⟨h.feat, el, nrw, congrFun h.b64 _, congrFun h.b64 _, congrFun h.b64 _, congrFun h.b64 _,
    congrFun h.b64 _, congrFun h.b64 _, congrFun h.b64 _, congrFun h.b64 _, congrFun h.b128 _,
    congrFun h.b128 _, by rw [h.b32], h.bbool _ (by decide), h.bbool _ (by decide), congrFun h.bint _⟩

theorem frame_branch_br (t u : NativeState) (h : ArmBridge.CruxGenBr.ActFrameBr t u) : BrSysEq t.regs u.regs :=
  ⟨congrFun h.bint _, congrFun h.bint _, congrFun h.bint _, congrFun h.b64 _⟩

theorem class_sys_br (w : BitVec 32) (K : Int)
    (fetched sp a fin : NativeState) (budget : Nat)
    (pins : StepPins fetched) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    (frame : ArmBridge.CruxGenBr.ActFrameBr (actionState w sp K) a)
    (sys : SysEq2 a.regs fin.regs) : SysEq2 fetched.regs fin.regs := by
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have entrySp := NativeEntryTail.EntryPins.after_E20 fetched sp
    (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame
  have btype : sp.regs.PSTATE.BTYPE = 0#2 := by
    rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have btn : sp.regs.BTypeNext = 0#2 := (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have spPins : StepPins sp := scalar_pins sp entrySp btype btn
  have s1 := sysEq2_trans _ _ _ (e20_sys _ _ post.frame) (metadata_sys w sp K spPins)
  exact sysEq2_trans _ _ _ (sysEq2_trans _ _ _ s1 (frame_sys_br _ a frame)) sys


theorem class_branch_pins_br (w : BitVec 32) (K : Int)
    (fetched sp a fin : NativeState) (budget : Nat)
    (pins : StepPins fetched) (quiet : HookQuiet (budget + 1) fetched)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp)
    (frame : ArmBridge.CruxGenBr.ActFrameBr (actionState w sp K) a)
    (sys : SysEq2 a.regs fin.regs)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs)
    (pinsFin : StepPins fin)
    (bp : Crypto.BranchV2.BranchPinsV2PA fetched) : Crypto.BranchV2.BranchPinsV2PA fin := by
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have entrySp := NativeEntryTail.EntryPins.after_E20 fetched sp
    (NativeEntryTail.EntryPins.of_scalar fetched pins) post.frame
  have btype : sp.regs.PSTATE.BTYPE = 0#2 := by
    rw [(PMUFrame.of_E20 post.frame).pstate]; exact pins.btype
  have btn : sp.regs.BTypeNext = 0#2 := (PMUFrame.of_E20 post.frame).btn.trans pins.btn
  have spPins : StepPins sp := scalar_pins sp entrySp btype btn
  have s1 := sysEq2_trans _ _ _ (e20_sys _ _ post.frame) (metadata_sys w sp K spPins)
  have s2 := sysEq2_trans _ _ _ (sysEq2_trans _ _ _ s1 (frame_sys_br _ a frame)) sys
  have b1 := EntryBranchPins.brSysEq_trans _ _ _ (EntryBranchPins.brSysEq_e20 _ _ post.frame)
    (EntryBranchPins.brSysEq_action w sp K)
  have b2 := EntryBranchPins.brSysEq_trans _ _ _
    (EntryBranchPins.brSysEq_trans _ _ _ b1 (frame_branch_br _ a frame)) (ClassBranchPins.npe_branch _ _ np)
  exact Crypto4.branchPinsV2_step_pa fetched fin bp s2 pinsFin b2

#print axioms class_branch_pins_br

theorem closed_tail_br {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    (word : BitVec 32) (K : Int)
    (fetched sp a fin : NativeState) (closed : ClosedMembershipAt spec config rows mapping m fetched)
    (e20 : E20Frame fetched.regs sp.regs)
    (frame : ArmBridge.CruxGenBr.ActFrameBr (actionState word sp K) a)
    (sys : SysEq2 a.regs fin.regs)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs) :
    ClosedMembershipAt spec config rows mapping m fin := by
  have b64 : ∀ k : Bank_BitVec_64, ArmBridge.CruxNonProj.bkHeap.b64 k = false →
      (∀ x : Regs, (eraseE20 x).bank_BitVec_64 k = x.bank_BitVec_64 k) →
      fin.regs.bank_BitVec_64 k = fetched.regs.bank_BitVec_64 k := by
    intro k hk he
    rw [ClosedChain.np_b64 np k hk, congrFun frame.b64 k]
    show sp.regs.bank_BitVec_64 k = _
    exact frame_pres_E20 (fun x => x.bank_BitVec_64 k) he e20
  have b128 : ∀ k : Bank_BitVec_128, (∀ x : Regs, (eraseE20 x).bank_BitVec_128 k = x.bank_BitVec_128 k) →
      fin.regs.bank_BitVec_128 k = fetched.regs.bank_BitVec_128 k := by
    intro k he
    rw [ClosedChain.np_b128 np k, congrFun frame.b128 k]
    show sp.regs.bank_BitVec_128 k = _
    exact frame_pres_E20 (fun x => x.bank_BitVec_128 k) he e20
  refine ClosedChain.closed_of_fields closed ?_ (b64 _ (by decide) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]))
    (b64 _ (by decide) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]))
    (b128 _ (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]))
    (b64 _ (by decide) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]))
    (b128 _ (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne])) ?_
  · rw [sys.feat, frame.feat]
    show sp.regs.FeatureImpl = _
    exact frame_pres_E20 (fun x => x.FeatureImpl) (fun x => by simp (disch := decide) only [eraseE20]) e20
  · rw [ClosedChain.np_int np _ (by decide), congrFun frame.bint .__block_bbm_implemented]
    simp (disch := decide) only [actionState, RegMap.set_ne]
    exact frame_pres_E20 (fun x => x.bank_Int .__block_bbm_implemented) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) e20


theorem tail_current_br {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow}
    (word : BitVec 32) (K : Int)
    (fetched sp a fin : NativeState) (current : CurrentS1At spec config rows fetched)
    (e20 : E20Frame fetched.regs sp.regs)
    (frame : ArmBridge.CruxGenBr.ActFrameBr (actionState word sp K) a)
    (sys : SysEq2 a.regs fin.regs)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs)
    (el : fin.regs.PSTATE.EL = fetched.regs.PSTATE.EL)
    (nrw : fin.regs.PSTATE.nRW = fetched.regs.PSTATE.nRW)
    (mem : fin.mem = fetched.mem) :
    CurrentS1At spec config rows fin := by
  have b64 : ∀ k : Bank_BitVec_64, fin.regs.bank_BitVec_64 k = a.regs.bank_BitVec_64 k →
      fin.regs.bank_BitVec_64 k = fetched.regs.bank_BitVec_64 k → True := fun _ _ _ => trivial
  have chain : ∀ k : Bank_BitVec_64, k ≠ .MDCCSR_EL0 → (∀ x : Regs, (eraseE20 x).bank_BitVec_64 k = x.bank_BitVec_64 k) →
      a.regs.bank_BitVec_64 k = fetched.regs.bank_BitVec_64 k := by
    intro k _ hk
    rw [congrFun frame.b64 k]
    show sp.regs.bank_BitVec_64 k = _
    exact frame_pres_E20 (fun x => x.bank_BitVec_64 k) hk e20
  have e20k : ∀ k : Bank_BitVec_64, (k = .TCR_EL2 ∨ k = .TCR2_EL2 ∨ k = .HCR_EL2 ∨ k = .SCR_EL3 ∨
      k = .SCTLR_EL2 ∨ k = .MAIR_EL2 ∨ k = .PIR_EL2 ∨ k = .PIRE0_EL2 ∨ k = .POR_EL0) →
      ∀ x : Regs, (eraseE20 x).bank_BitVec_64 k = x.bank_BitVec_64 k := by
    intro k hk x
    rcases hk with h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp (disch := decide) only [eraseE20, RegMap.set_ne]
  have ak : ∀ k : Bank_BitVec_64, (k = .TCR_EL2 ∨ k = .TCR2_EL2 ∨ k = .HCR_EL2 ∨ k = .SCR_EL3 ∨
      k = .SCTLR_EL2 ∨ k = .MAIR_EL2 ∨ k = .PIR_EL2 ∨ k = .PIRE0_EL2 ∨ k = .POR_EL0) →
      a.regs.bank_BitVec_64 k = fetched.regs.bank_BitVec_64 k := by
    intro k hk
    exact chain k (by rcases hk with h | h | h | h | h | h | h | h | h <;> subst h <;> decide) (e20k k hk)
  have feat : fin.regs.FeatureImpl = fetched.regs.FeatureImpl := by
    rw [sys.feat, frame.feat]
    show sp.regs.FeatureImpl = _
    exact frame_pres_E20 (fun x => x.FeatureImpl) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) e20
  refine current_s1_program_write current (fun _ => False) (EntryBtiNext.no_writes fetched fin mem)
    (EntryBtiNext.no_writes_separated _) feat el nrw ?tcr ?tcr2 ?hcr ?scr ?sctlr ?mair ?pa
    (fun _ => ?pir) (fun _ => ?pire0) (fun _ => ?por) ?tlb
  case tcr => rw [sys.tcr]; exact ak _ (by simp)
  case tcr2 => rw [sys.tcr2]; exact ak _ (by simp)
  case hcr => rw [sys.hcr]; exact ak _ (by simp)
  case scr => rw [sys.scr]; exact ak _ (by simp)
  case sctlr => rw [sys.sctlr]; exact ak _ (by simp)
  case mair => rw [sys.mair]; exact ak _ (by simp)
  case pir => rw [np.bank64 _ (by decide)]; exact ak _ (by simp)
  case pire0 => rw [np.bank64 _ (by decide)]; exact ak _ (by simp)
  case por => rw [np.bank64 _ (by decide)]; exact ak _ (by simp)
  case pa =>
    rw [sys.pa, congrFun frame.bint .__supported_pa_size]
    simp (disch := decide) only [actionState, RegMap.set_ne]
    exact frame_pres_E20 (fun x => x.bank_Int .__supported_pa_size) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) e20
  case tlb =>
    rw [sys.tlb, frame.bbool .__tlb_enabled (by decide)]
    simp (disch := decide) only [actionState, RegMap.set_ne]
    exact frame_pres_E20 (fun x => x.bank_Bool .__tlb_enabled) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) e20


/-- The actual branch tail from the post-fetch state, as the v3 chain consumes it: Core's class tail shape
over ActFrameBr, plus the GPR/SP and GIC-pending carries fetched → fin. -/
def BranchTailAt (real : Type) [Sail.SailReal real] (w : BitVec 32) (K : Int) (source : NativeState)
    (next : BitVec 64) : Prop :=
  ∀ (fetched : NativeState) (enc0 : __InstrEnc) (budget : Nat),
    StepPins fetched → Crypto.BranchV2.BranchPinsV2PA fetched → NativeEntryInput.Input source fetched →
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
      fin.regs.gpr = fetched.regs.gpr ∧ fin.regs.SP_EL0 = fetched.regs.SP_EL0

set_option maxHeartbeats 200000 in
theorem entry_class_next_v3_br (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (tail : BranchTailAt real w K s next)
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
      fin.regs.gpr = s.regs.gpr ∧ fin.regs.SP_EL0 = s.regs.SP_EL0 ∧ fin.mem = s.mem ∧ SysEq2 s.regs fin.regs := by
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
  obtain ⟨sp, a, fin, hook, tail, frame, finQuiet, finStep, sys, _brsys, mem, gicF, pc, np, gprF, spF⟩ :=
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
  have bpFin := class_branch_pins_br _ K final sp a fin budget fpins fquiet hook frame sys np
    finStep bpFinal
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin, closed_before_fetch fin closedFin, placedFin, bpFin, gprF.trans gprFinal, spF.trans spFinal, finMem, sysS⟩
  · rw [pc, nextPlaced]
  · rw [mdscr]; exact debug.mde
  · rw [sys.hde, hdeA, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

#print axioms entry_class_next_v3_br

/-- `upds k = []`: every register kept. -/
theorem keep_holds {k : Nat} {x y : NativeState} (upd0 : HeapV2StepCerts.RegBind.upds k = [])
    (gpr : y.regs.gpr = x.regs.gpr) (sp : y.regs.SP_EL0 = x.regs.SP_EL0) :
    HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) x y := by
  rw [upd0]
  exact HeapV2StepCerts.RegBind.holds_of_regs_eq (fun _ => Or.inl (by simp [HeapV2StepCerts.RegBind.updOf])) gpr sp

theorem plan_step3_branch (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int) (upd0 : HeapV2StepCerts.RegBind.upds k = [])
    (next : NativeState → BitVec 64)
    (tail : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      BranchTailAt real w K x (next x))
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping w x) :
    Uget.Chain.Step real (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)) := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, gprEq, spEq, finMem, sys⟩ :=
    entry_class_next_v3_br real spec config rows mapping w K x inv.v2.v1.pins (next x)
      (offset (k + 1)) (tail x inv) inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩,
    HeapV2StepCerts.RegBind.carry_step hk (keep_holds upd0 gprEq spEq) inv.regBind, ?_, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩⟩
  · intro e he n hn i hi; rw [finMem]; exact inv.present e he n hn i hi
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [ChainInvV3.hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms plan_step3_branch
end HeapV2StepCerts.BranchStepV3
