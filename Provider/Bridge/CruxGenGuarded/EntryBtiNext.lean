import Bridge.CruxGenGuarded.EntryBtiStep
import ArmCertTranslateModel.CurrentProgramTransport
import ArmCertWalk.NativeFetchPreserving
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.EntryBtiNext
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! Next-fetch invariant: the canonical current-S1 invariant on the ACTUAL
fetched state carries to `beforeFetchState fin` for the BTI c step's actual
final state, through the actual PMU event (E20 frame), the canonical action
metadata state, the class frame and the tail's SysEq2/bkHeap frames. BTI c
writes no memory, so the write set is empty. -/

theorem no_writes (m n : NativeState) (h : n.mem = m.mem) :
    WritesOnly (fun _ => False) (fun a => m.mem[a]?) (fun a => n.mem[a]?) := by
  intro a _; simp [h]

theorem no_writes_separated (table : Nat → Prop) : Separated table (fun _ => False) :=
  fun _ _ h => h

run_cmd do
  IO.eprintln "CURRENT_DECL EntryBtiNext.before_fetch_current"
  (← IO.getStderr).flush

/-- The prefix writes before fetch touch only EDSCR/MDCCSR/SEE/advance flags. -/
theorem before_fetch_current {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} (x : NativeState)
    (current : CurrentS1At spec config rows x) :
    CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState x) := by
  refine current_s1_program_write current (fun _ => False)
    (no_writes x _ rfl) (no_writes_separated _) rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl
    (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) rfl
  all_goals simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]

theorem frame_bint_pa {writes : NativeEntry.Effects.Writes} {word : BitVec 32} {K : Int}
    {sp a : NativeState} (frame : NativeEntryContract.Frame writes (actionState word sp K) a) :
    a.regs.bank_Int .__supported_pa_size = sp.regs.bank_Int .__supported_pa_size := by
  rw [congrFun frame.bint .__supported_pa_size]
  simp (disch := decide) only [actionState, RegMap.set_ne]

run_cmd do
  IO.eprintln "CURRENT_DECL EntryBtiNext.tail_current"
  (← IO.getStderr).flush

/-- One fixed-class step from the actual fetched state: PMU event (E20),
canonical action metadata, the class Frame and the tail's SysEq2/bkHeap NPE.
The write set is empty (memory equality); EL/nRW come from both sides' pins. -/
theorem tail_current {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow}
    (writes : NativeEntry.Effects.Writes) (word : BitVec 32) (K : Int)
    (fetched sp a fin : NativeState) (current : CurrentS1At spec config rows fetched)
    (e20 : E20Frame fetched.regs sp.regs)
    (frame : NativeEntryContract.Frame writes (actionState word sp K) a)
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
  refine current_s1_program_write current (fun _ => False) (no_writes fetched fin mem)
    (no_writes_separated _) feat el nrw ?tcr ?tcr2 ?hcr ?scr ?sctlr ?mair ?pa
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
    rw [sys.pa, frame_bint_pa frame]
    exact frame_pres_E20 (fun x => x.bank_Int .__supported_pa_size) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) e20
  case tlb =>
    rw [sys.tlb, congrFun frame.bbool .__tlb_enabled]
    simp (disch := decide) only [actionState, RegMap.set_ne]
    exact frame_pres_E20 (fun x => x.bank_Bool .__tlb_enabled) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) e20

/-- A register field read through the actual fetch: the fetched registers are
the prefix/wrapper/walk updates of the entry registers, none of which touch it. -/
theorem fetched_field {β : Type} (f : Regs → β) (acc : AccessDescriptor) (next : TTWState)
    (s : NativeState)
    (hf : ∀ r g, f (gpRegs (ArmCert.Eval.M1a.Fetch2.fetchRegs r) g) = f r)
    (hg : ∀ r, f (ArmCert.Eval.M1a.Fetch2.fetchRegs r) = f r)
    (hb : f (ArmBridge.CruxGenGuarded.beforeFetchState s).regs = f s.regs) :
    f (FetchedRegs acc next s) = f s.regs := by
  unfold FetchedRegs fetchGuardRegs
  split
  · rw [hf, hb]
  · rw [hg, hb]

run_cmd do
  IO.eprintln "CURRENT_DECL EntryBtiNext.entry_bti_next"
  (← IO.getStderr).flush

/-- Whole first entry step (actual fetch + BTI c) and EVERY input the next
actual fetch needs, on the actual final state: EntryPins, quiet budget, the
canonical invariant at its `beforeFetchState`, placed PC (offset + 4), E11
MDE/HDE, F6/VHE features and no pending GIC interrupt. -/
theorem entry_bti_next (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : NativeState) (pins : NativeEntryTail.EntryPins s)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (mmio : MappedNotMMIO mapping s.regs._PC)
    (present : MappedBytesPresent mapping s.regs._PC s.mem)
    (perAcc : ∀ acc, ActualIFetchAcc (ArmBridge.CruxGenGuarded.beforeFetchState s) acc →
      domain (queryOf acc) ∧ ∃ data : S1AccessData spec config rows (queryOf acc),
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data
          (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (code : ∀ acc leafLevel view faultOut (address : AddressDescriptor) translated (w : BitVec 32),
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view
        (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)) (faultOut, address) translated →
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? = some (w.extractLsb' (8 * i) 8)) →
      w = NativeEntryDispatch.BtiC.word) :
    ∃ fin,
      modelStep real s = .ok () fin ∧
      NativeEntryTail.EntryPins fin ∧ HookQuiet budget fin ∧
      CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState fin) ∧
      fin.regs._PC = base + (offset + 4#64) ∧
      E11Debug.E11CheckDebug fin.regs ∧ EntryFeatures fin.regs ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = none := by
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w, final, address, faultOut, translated, data, _actual, run, clean, bytes, fregs,
      _fmem, _fev, curFinal, _⟩ :=
    native_fetch_current_preserving spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  have hw := code acc data.leafLevel data.view faultOut address translated w clean bytes
  subst hw
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have hregs : final.regs = FetchedRegs acc (translateCurrent out) s := by
    rw [fregs, translatedRegs, rawOf acc]; rfl
  have emuFinal : final.regs.__emulator_termination_opcode = none := by
    rw [hregs]; unfold FetchedRegs fetchGuardRegs; split
    · exact emu0
    · exact emu0
  obtain ⟨enc0, hstep⟩ := entry_prefetch_boundary real s final _ pins hGIC run emuFinal
  have fpins := fetched_pins acc (translateCurrent out) s final pins hregs
  have finput := fetched_input acc (translateCurrent out) s final pins.el hregs
  obtain ⟨guard, fquiet, it, ss⟩ :=
    fetched_rest acc (translateCurrent out) s final (budget + 1) pins quiet hregs
  obtain ⟨sp, a, fin, hook, _, tail, _, frame, finQuiet, finStep, sys, _, _, mem, _, gic, _, pc, np⟩ :=
    ArmBridge.CruxGenGuarded.EntryBtiC.native_tail real s final enc0 fpins finput guard budget fquiet it ss
  have post := entry_spec_post final sp (budget + 1) fquiet hook
  have finPins := NativeEntryTail.EntryPins.of_scalar fin finStep
  have curFin := tail_current _ _ _ final sp a fin curFinal post.frame frame sys np
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
    refine fetched_field (fun r => r.bank_BitVec_64 .MDSCR_EL1) _ _ s (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]
  have mdscr : fin.regs.bank_BitVec_64 .MDSCR_EL1 = s.regs.bank_BitVec_64 .MDSCR_EL1 := by
    rw [sys.mdscr, toFinal64 _ (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]), mdscrFinal]
  have hdeFinal : _get_EDSCR_Type_HDE (final.regs.bank_BitVec_32 ._EDSCR) =
      _get_EDSCR_Type_HDE (s.regs.bank_BitVec_32 ._EDSCR) := by
    rw [hregs]
    refine fetched_field (fun r => _get_EDSCR_Type_HDE (r.bank_BitVec_32 ._EDSCR)) _ _ s
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
    exact fetched_field (fun r => r.FeatureImpl) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have gicFin : fin.regs.bank_Option_InterruptID .__GIC_Pending = none := by
    rw [gic, frame.gic]
    show sp.regs.bank_Option_InterruptID .__GIC_Pending = _
    rw [post.gic, hregs]
    rw [fetched_field (fun r => r.bank_Option_InterruptID .__GIC_Pending) _ _ s (fun _ _ => rfl)
      (fun _ => rfl) rfl]
    exact hGIC
  refine ⟨fin, hstep.trans tail, finPins, finQuiet,
    EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin⟩
  · rw [pc, placed, BitVec.add_assoc]
  · rw [mdscr]; exact debug.mde
  · rw [sys.hde, hdeA, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

run_cmd do
  IO.eprintln "CURRENT_DECL EntryBtiNext.tail_current_writes"
  (← IO.getStderr).flush

/-- Same chain for a class step that WRITES memory: the actual written byte
set must be separated from the descriptor-table footprint (an explicit
placement input, e.g. C9 ImageTableSeparated / heap-vs-table layout). -/
theorem tail_current_writes {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow}
    (writes : NativeEntry.Effects.Writes) (word : BitVec 32) (K : Int)
    (fetched sp a fin : NativeState) (current : CurrentS1At spec config rows fetched)
    (e20 : E20Frame fetched.regs sp.regs)
    (frame : NativeEntryContract.Frame writes (actionState word sp K) a)
    (sys : SysEq2 a.regs fin.regs)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs)
    (el : fin.regs.PSTATE.EL = fetched.regs.PSTATE.EL)
    (nrw : fin.regs.PSTATE.nRW = fetched.regs.PSTATE.nRW)
    (writtenBytes : Nat → Prop)
    (mem : WritesOnly writtenBytes (fun x => fetched.mem[x]?) (fun x => fin.mem[x]?))
    (separated : Separated (rowsFootprint spec.imageRows).byte writtenBytes) :
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
  refine current_s1_program_write current writtenBytes mem
    separated feat el nrw ?tcr ?tcr2 ?hcr ?scr ?sctlr ?mair ?pa
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
    rw [sys.pa, frame_bint_pa frame]
    exact frame_pres_E20 (fun x => x.bank_Int .__supported_pa_size) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) e20
  case tlb =>
    rw [sys.tlb, congrFun frame.bbool .__tlb_enabled]
    simp (disch := decide) only [actionState, RegMap.set_ne]
    exact frame_pres_E20 (fun x => x.bank_Bool .__tlb_enabled) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) e20

#print axioms before_fetch_current
#print axioms tail_current_writes
#print axioms entry_bti_next
#print axioms tail_current
end ArmBridge.CruxGenGuarded.EntryBtiNext
