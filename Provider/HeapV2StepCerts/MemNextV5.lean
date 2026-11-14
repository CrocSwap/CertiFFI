-- Memory (B1:,): ADDITIVE ChainInv v4 memory steps with events. MemRE = MemR plus
-- the SIMD frame, the NZCV frame and Core's StepEvents.EvShape spec mapping data s f (fetch traffic + ifetch + the
-- step's data events D with records data), GcsFrame last. entry_mem_next_v5 / plan_step4_memE are
-- entry_mem_next_v4 / plan_step4_mem over MemFactsE.MemTailEAt and FetchTiming's slots-keeping fetch, under nodup.
import HeapV2StepCerts.AccShape
import HeapV2StepCerts.ActionTransport
import HeapV2StepCerts.BodyHolds
import HeapV2StepCerts.BranchFrame
import HeapV2StepCerts.C3Byte
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.C3Pair
import HeapV2StepCerts.Carry
import HeapV2StepCerts.CodeScope
import HeapV2StepCerts.DataBytes
import HeapV2StepCerts.FetchFrames
import HeapV2StepCerts.FlagRoots
import HeapV2StepCerts.FlagTails
import HeapV2StepCerts.MemConfigFrame
import HeapV2StepCerts.MemRunD
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.MemStepsV3_00
import HeapV2StepCerts.MemStepsV3_01
import HeapV2StepCerts.MemStepsV3_02
import HeapV2StepCerts.MemStepsV3_03
import HeapV2StepCerts.MemStepsV3_04
import HeapV2StepCerts.MemStepsV3_05
import HeapV2StepCerts.MemTailD
import HeapV2StepCerts.MemTailLdrb
import HeapV2StepCerts.MemTailStrb
import HeapV2StepCerts.RawFetch
import HeapV2StepCerts.RegBind
import HeapV2StepCerts.RegBindCore
import HeapV2StepCerts.RegBindData
import HeapV2StepCerts.RegRootsB
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.Straight
import HeapV2StepCerts.StraightV2
import HeapV2StepCerts.ValBindCore
import HeapV2StepCerts.ValBindData
import HeapV2StepCerts.ValueTailDef
import HeapV2StepCerts.MemNextV3
import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemStepsV3
import HeapV2StepCerts.MemTailPair
import HeapV2StepCerts.BodyMemD
import HeapV2StepCerts.MemHolds
import HeapV2StepCerts.ValBind
import HeapV2StepCerts.TailW
import HeapV2StepCerts.CodeData
import RtSaved.MemFacts
import HeapV2StepCerts.MemNextV4
import HeapV2StepCerts.MemFactsE
import HeapV2StepCerts.FetchTiming
import HeapV2StepCerts.Flags
import Bridge.CruxGenGuarded.StepEvents
import Bridge.CruxGenGuarded.ChainInvV4
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace HeapV2StepCerts.MemNextE
open HeapV2StepCerts.MemNext
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option Elab.async false


/-- The memory R with events: MemR's register effect, value effect, write frame and payload, then the SIMD frame,
the NZCV frame and the step's event shape (fetch traffic + ifetch + data events with records data), GcsFrame last. -/
def MemRE {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (k : Nat) (D : Nat → Prop) (Pay : NativeState → NativeState → Prop)
    (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (s f : NativeState) : Prop :=
  RegBind.Holds (RegBind.upds k) s f ∧ ValBind.VEff k s f ∧
    (∃ written : Nat → Prop, WritesOnly written (fun y => s.mem[y]?) (fun y => f.mem[y]?) ∧ ∀ y, written y → D y) ∧
    Pay s f ∧ f.regs._Z = s.regs._Z ∧ Flags.nzcv f.regs = Flags.nzcv s.regs ∧
    ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping data s f ∧
    ArmBridge.CruxGenGuarded.ChainInvV4.GcsFrame s f

/-- Forgetting the extensions gives Memory's MemR. -/
theorem MemRE.toR {domain : QueryDomain} {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {k : Nat} {D : Nat → Prop} {Pay : NativeState → NativeState → Prop}
    {data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)} {s f : NativeState}
    (h : MemRE spec mapping k D Pay data s f) : MemNext.MemR k D Pay s f :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.2⟩

run_cmd do
  IO.eprintln "CURRENT_DECL MemNextE.entry_mem_next_v5"
  (← IO.getStderr).flush

set_option maxHeartbeats 200000 in
theorem entry_mem_next_v5 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (s : NativeState) (stepPins : StepPins s) (next nextOffset : BitVec 64)
    (us : List (RegBind.Reg × RegBind.Upd))
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (p : HeapV2E17.Pins) (k : Nat) (D : Nat → Prop)
    (Pay : NativeState → NativeState → Prop)
    (payT : ∀ f y, f.regs.gpr = s.regs.gpr → f.mem = s.mem → Pay f y → Pay s y)
    (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (tail : MemFactsE.MemTailEAt real spec config rows (FetchedCtx spec config rows mapping m p k) D w writes K s next us Pay data)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
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
    (regBindS : RegBind.RegBind p k s) (presentS : C3.DataPresent p mapping s)
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
        Separated (rowsFootprint spec.imageRows).byte written ∧ ∀ y, written y → D y) ∧
      (∀ x : Nat, (s.mem[x]?).isSome → (fin.mem[x]?).isSome) ∧
      SysEq2 s.regs fin.regs ∧ Pay s fin ∧ fin.regs._Z = s.regs._Z ∧ Flags.nzcv fin.regs = Flags.nzcv s.regs ∧
      ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping data s fin ∧
      ArmBridge.CruxGenGuarded.ChainInvV4.GcsFrame s fin := by
  have pins := NativeEntryTail.EntryPins.of_scalar s stepPins
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, w', final, address, faultOut, translated, data, actualAcc, run, clean, bytes, fregs,
      fmem, fev, curFinal, _, info, walk, leaf, middle, _len, traffic, endEv, cond⟩ :=
    HeapV2StepCerts.FetchTiming.fetch_events_slots spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s)
      step el (pc_low_of_placement _ base offset placed page word) il current mode step.b0
      ⟨e11.mde, e11.hde⟩ spe queryOf rawOf vaOf mmio present perAcc
  obtain ⟨noUpdCond, slots⟩ := cond
  have hw := code acc data.leafLevel data.view faultOut address translated w' clean bytes
  have mapResult : mapping s.regs._PC = some address.paddress.address.toNat := by
    have kept := clean
    obtain ⟨_, _, _, _, _, _, _, mr, _, _, _, _, _, _, _, _, _⟩ := kept
    rw [vaOf acc] at mr; exact mr
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
  have nuC := noUpdCond rawS (by
      rw [rawOf acc]
      exact HeapV2StepCerts.RawFetch.noUpd_read noUpdS acc (actual_ifetch_flags actualAcc).2.2.1)
  have memNoUpd : translated.mem = (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).mem := nuC.2.2
  have finalMem : final.mem = s.mem := fmem.trans memNoUpd
  obtain ⟨flagsT, leafF, _⟩ := nuC
  obtain ⟨T, hT, recsT⟩ := ArmCertWalk.noupdate_traffic_delta ⟨info, walk, leaf, middle, traffic, flagsT, leafF, slots, endEv⟩ nodup
  have pcB : (ArmBridge.CruxGenGuarded.beforeFetchState s).regs._PC = s.regs._PC := rfl
  have evB : (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)).events = s.events := rfl
  rw [pcB] at recsT
  have finalEv : final.events = s.events ++ T ++ #[ArmBridge.CruxGenGuarded.StepEvents.ifetchEv address.paddress.address.toNat s.regs._PC] := by
    rw [fev, hT, evB, Array.push_eq_append, pcB]; rfl
  have gprFinal : final.regs.gpr = s.regs.gpr := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.gpr) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have spFinal : final.regs.SP_EL0 = s.regs.SP_EL0 := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.SP_EL0) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have sysF : SysEq2 s.regs final.regs := EntryBranchPins.sysEq2_symm _ _ finput.sys
  have ctx : FetchedCtx spec config rows mapping m p k final :=
    { closed := closedFinal
      regBind := C3.regBind_of_regs gprFinal spFinal regBindS
      present := C3.DataPresent.carry (fun a h => by rw [finalMem]; exact h) presentS
      raw := by rw [finalMem]; exact rawS
      noUpd := fun wr acc hs => by rw [hostHAFT_eq sysF]; exact noUpdS wr acc hs
      post2 := HeapV2StepCerts.MemConfigFrame.post2 sysF.feat sysF.el sysF.nrw sysF.scr sysF.hcr sysF.sctlr sysF.spe post2S
      mode := HeapV2StepCerts.MemConfigFrame.mode sysF.feat sysF.el sysF.scr sysF.hcr modeS
      debug := HeapV2StepCerts.MemConfigFrame.debug sysF.mdscr sysF.hde edebugS
      feat := by rw [sysF.feat]; exact featS
      dcache := HeapV2StepCerts.MemConfigFrame.dcache sysF.sctlr dcacheS }
  obtain ⟨sp, a, fin, written, hook, tail, frame, finQuiet, finStep, sys, wo, sepT, inD, gic, pc, np, keep, holdsF, pay, ⟨delta, evD, recsD⟩, zT, flT⟩ :=
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
  have zFinal : final.regs._Z = s.regs._Z := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r._Z) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have flFinal : Flags.nzcv final.regs = Flags.nzcv s.regs := by
    rw [hregs]
    exact ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => Flags.nzcv r) _ _ s (fun _ _ => rfl) (fun _ => rfl) rfl
  have gcsFinal : final.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 := by
    rw [hregs]
    refine ArmBridge.CruxGenGuarded.EntryBtiNext.fetched_field (fun r => r.bank_BitVec_64 .SCR_EL3) _ _ s (fun _ _ => rfl) (fun _ => rfl) ?_
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]
  have gcs : fin.regs.bank_BitVec_64 .SCR_EL3 = s.regs.bank_BitVec_64 .SCR_EL3 := by
    rw [ClosedChain.np_b64 np .SCR_EL3 (by decide),
      toFinal64 _ (fun x => by simp (disch := decide) only [eraseE20, RegMap.set_ne]), gcsFinal]
  have sysS : SysEq2 s.regs fin.regs :=
    sysEq2_trans _ _ _ sysF
      (ClassNextV3.class_sys _ writes K final sp a fin budget fpins fquiet hook frame sys)
  have bpFin := ClassBranchPins.class_branch_pins _ writes K final sp a fin budget fpins fquiet hook frame sys np
    finStep bpFinal
  refine ⟨fin, hstep.trans tail, finStep, finQuiet,
    ArmBridge.CruxGenGuarded.EntryBtiNext.before_fetch_current fin curFin, ?_, ⟨?_, ?_⟩, ?_, gicFin,
    closed_before_fetch fin closedFin, placedFin, bpFin, holdsS,
    ⟨written, by rw [← finalMem]; exact wo, sepT, inD⟩, fun x h => keep x (by rw [finalMem]; exact h), sysS,
    payT final fin gprFinal finalMem pay, zT.trans zFinal, flT.trans flFinal,
    ⟨address.paddress.address.toNat, T, delta, by rw [evD, finalEv], recsT, mapResult, recsD nodup⟩, gcs⟩
  · rw [pc, nextPlaced]
  · rw [mdscr]; exact debug.mde
  · rw [sys.hde, hdeA, hdeFinal]; exact debug.hde
  · exact ⟨featFin ▸ features.a0, featFin ▸ features.a1, featFin ▸ features.a2, featFin ▸ features.a3,
      featFin ▸ features.b1, featFin ▸ features.b2, featFin ▸ features.b3, featFin ▸ features.vhe⟩

#print axioms entry_mem_next_v5

theorem plan_step4_memE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (Pay : NativeState → NativeState → Prop)
    (payT : ∀ s f y, f.regs.gpr = s.regs.gpr → f.mem = s.mem → Pay f y → Pay s y)
    (he : ValBind.effAt k = .none)
    (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (next : NativeState → BitVec 64)
    (tail : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      MemFactsE.MemTailEAt real spec config rows (FetchedCtx spec config rows mapping m p k) D w writes K x (next x)
        (RegBind.upds k) Pay data)
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping w x) :
    ArmBridge.CruxGenGuarded.ChainInvV4.RichStep real (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)) (MemRE spec mapping k D Pay data) := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, holds, ⟨written, wo, sep, inD⟩, keep, sys, pay, z, fl, ev, gcs⟩ :=
    MemNextE.entry_mem_next_v5 real spec config rows mapping w writes K x inv.v2.v1.pins (next x)
      (offset (k + 1)) (RegBind.upds k) m p k D Pay (payT x) data (tail x inv) nodup inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current inv.v2.closed scope image loadBase inv.v2.placed separated codeD inv.v2.branch
      inv.raw inv.noUpd inv.regBind inv.present inv.post2 inv.mode inv.debug inv.feat inv.dcache
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩,
    RegBind.carry_step hk holds inv.regBind, C3.DataPresent.carry keep inv.present,
    RawFetch.raw_writes inv.raw wo sep, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩,
    holds, ValBind.veff_none he _ _, ⟨written, wo, inD⟩, pay, z, fl, ev, gcs⟩
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms plan_step4_memE
end HeapV2StepCerts.MemNextE
