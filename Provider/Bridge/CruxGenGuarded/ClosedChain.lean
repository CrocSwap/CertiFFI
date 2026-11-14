import Bridge.CruxGenGuarded.EntryClassNext
import ArmCertTranslateModel.ClosedMembershipTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.ClosedChain
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! E17 closed membership carried along the chain (eb6d6605): the actual
fetch keeps it (`closed_membership_after_fetch`); a fixed-class tail keeps it
because every access-check field (features, TCR/SCTLR/HTTBR, TTBR0/1, block BBM)
is unmasked by bkHeap and untouched by the PMU event and action metadata; the
prefix writes before the next fetch touch none of them. So ClosedMembershipAt
becomes part of the run invariant instead of a per-state input. -/

theorem closed_of_fields {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {before after : NativeState}
    (closed : ClosedMembershipAt spec config rows mapping m before)
    (features : after.regs.FeatureImpl = before.regs.FeatureImpl)
    (tcr : after.regs.bank_BitVec_64 .TCR_EL2 = before.regs.bank_BitVec_64 .TCR_EL2)
    (sctlr : after.regs.bank_BitVec_64 .SCTLR_EL2 = before.regs.bank_BitVec_64 .SCTLR_EL2)
    (ttbr0 : after.regs.bank_BitVec_128 ._TTBR0_EL2 = before.regs.bank_BitVec_128 ._TTBR0_EL2)
    (httbr : after.regs.bank_BitVec_64 .HTTBR = before.regs.bank_BitVec_64 .HTTBR)
    (ttbr1 : after.regs.bank_BitVec_128 .TTBR1_EL2 = before.regs.bank_BitVec_128 .TTBR1_EL2)
    (bbm : after.regs.bank_Int .__block_bbm_implemented = before.regs.bank_Int .__block_bbm_implemented) :
    ClosedMembershipAt spec config rows mapping m after := by
  intro va acc aligned size permitted
  obtain ⟨q, hva, hraw, hal, hsz, member, data, access⟩ := closed va acc aligned size permitted
  exact ⟨q, hva, hraw, hal, hsz, member, data,
    current_s1_access_registers access features tcr sctlr ttbr0 httbr ttbr1 (fun _ _ => bbm)⟩

theorem closed_before_fetch {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} (x : NativeState)
    (closed : ClosedMembershipAt spec config rows mapping m x) :
    ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState x) := by
  refine closed_of_fields closed rfl ?_ ?_ rfl ?_ rfl ?_
  all_goals simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]

theorem np_b64 {r r' : Regs} (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap r r')
    (k : Bank_BitVec_64) (hk : ArmBridge.CruxNonProj.bkHeap.b64 k = false) :
    r'.bank_BitVec_64 k = r.bank_BitVec_64 k := (np.bank64 k hk)

theorem np_b128 {r r' : Regs} (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap r r')
    (k : Bank_BitVec_128) : r'.bank_BitVec_128 k = r.bank_BitVec_128 k := by
  have h := congrFun (congrArg Regs.bank_BitVec_128 np) k
  simpa [ArmCertCT.CT2.mask, ArmCertCT.CT2.maskBank, ArmBridge.CruxNonProj.bkHeap] using h

theorem np_int {r r' : Regs} (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap r r')
    (k : Bank_Int) (hk : ArmBridge.CruxNonProj.bkHeap.int k = false) :
    r'.bank_Int k = r.bank_Int k := by
  have h := congrFun (congrArg Regs.bank_Int np) k
  simpa [ArmCertCT.CT2.mask, ArmCertCT.CT2.maskBank, hk] using h

theorem closed_tail {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    (writes : NativeEntry.Effects.Writes) (word : BitVec 32) (K : Int)
    (fetched sp a fin : NativeState) (closed : ClosedMembershipAt spec config rows mapping m fetched)
    (e20 : E20Frame fetched.regs sp.regs)
    (frame : NativeEntryContract.Frame writes (actionState word sp K) a)
    (sys : SysEq2 a.regs fin.regs)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs) :
    ClosedMembershipAt spec config rows mapping m fin := by
  have b64 : ∀ k : Bank_BitVec_64, ArmBridge.CruxNonProj.bkHeap.b64 k = false →
      (∀ x : Regs, (eraseE20 x).bank_BitVec_64 k = x.bank_BitVec_64 k) →
      fin.regs.bank_BitVec_64 k = fetched.regs.bank_BitVec_64 k := by
    intro k hk he
    rw [np_b64 np k hk, congrFun frame.b64 k]
    show sp.regs.bank_BitVec_64 k = _
    exact frame_pres_E20 (fun x => x.bank_BitVec_64 k) he e20
  have b128 : ∀ k : Bank_BitVec_128, (∀ x : Regs, (eraseE20 x).bank_BitVec_128 k = x.bank_BitVec_128 k) →
      fin.regs.bank_BitVec_128 k = fetched.regs.bank_BitVec_128 k := by
    intro k he
    rw [np_b128 np k, congrFun frame.b128 k]
    show sp.regs.bank_BitVec_128 k = _
    exact frame_pres_E20 (fun x => x.bank_BitVec_128 k) he e20
  refine closed_of_fields closed ?_ (b64 _ (by decide) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]))
    (b64 _ (by decide) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]))
    (b128 _ (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]))
    (b64 _ (by decide) (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]))
    (b128 _ (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne])) ?_
  · rw [sys.feat, frame.feat]
    show sp.regs.FeatureImpl = _
    exact frame_pres_E20 (fun x => x.FeatureImpl) (fun x => by simp (disch := decide) only [eraseE20]) e20
  · rw [np_int np _ (by decide), congrFun frame.bint .__block_bbm_implemented]
    simp (disch := decide) only [actionState, RegMap.set_ne]
    exact frame_pres_E20 (fun x => x.bank_Int .__block_bbm_implemented) (fun x => by
      simp (disch := decide) only [eraseE20, RegMap.set_ne]) e20

run_cmd do
  IO.eprintln "CURRENT_DECL ClosedChain.entry_class_next_closed"
  (← IO.getStderr).flush

theorem entry_class_next_closed (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (tail : ClassTailAt real w writes K s next)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (budget : Nat) (quiet : HookQuiet (budget + 1) s)
    (base offset : BitVec 64) (placed : s.regs._PC = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0)
    (nextPlaced : next = base + nextOffset)
    (current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState s))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState s))
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
      ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState fin) := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, _actual, run, clean, bytes, fregs,
      _fmem, _fev, curFinal, _⟩ :=
    native_fetch_current_preserving spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  have hw := code acc data.leafLevel data.view faultOut address translated w' clean bytes
  subst hw
  have closedFinal := closed_membership_after_fetch closed clean fregs
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
  obtain ⟨sp, a, fin, hook, tail, frame, finQuiet, finStep, sys, mem, gic, pc, np⟩ :=
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
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin, closed_before_fetch fin closedFin⟩
  · rw [pc, nextPlaced]
  · rw [mdscr]; exact debug.mde
  · rw [sys.hde, hdeA, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

#print axioms closed_before_fetch
#print axioms closed_tail
#print axioms entry_class_next_closed
end ArmBridge.CruxGenGuarded.ClosedChain
