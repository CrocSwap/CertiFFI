-- Actual __FetchInstr (AArch64 branch) from current data: actual CreateAccDescIFetch,
-- SetBTypeCompatible, CheckSoftwareStep, PC alignment, PC_read, actual MemSingle_read4 through
-- native_mem_read_total (actual TranslateAddress incl. walk stores), CheckIllegalState.
-- Step/feature facts are the canonical Fetch2.StepFacts = existing F6 (FeatureImpl[0..3]=false,
-- [4..7]=true), E19 (FeatureImpl[232]=false), E1 (A64 nRW=0, NS, EL0, IL=0), E11 (MDSCR.SS=0).
-- NOTE: the actual IFETCH descriptor is ORACLE-dependent (occ 769 draws modop/cacheop/opscope/
-- cachetype/toplevel/varange/...), not a function of registers. Per-query walk data is therefore
-- required for every descriptor the actual source call can return, and the conclusion names
-- the actual one; no descriptor is pinned.
import ArmCertWalk.NativeMemReadTotal
import ArmCertWalk.FetchPost
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk
open ArmCert.Eval.M1a.Fetch2

/-- A descriptor the actual `CreateAccDescIFetch` returns on a state with these registers. -/
def ActualIFetchAcc (s : State) (acc : AccessDescriptor) : Prop :=
  ∃ t0 u0 : State, t0.regs = s.regs ∧ CreateAccDescIFetch () t0 = .ok acc u0

theorem pc_low_aligned (pc : BitVec 64) (low : Sail.BitVec.extractLsb pc 1 0 = 0#2) :
    pc.toNat % 4 = 0 := by
  have h := congrArg BitVec.toNat low
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'] at h
  omega

/-- Per-query current walk data for one actual IFETCH request (query-dependent part). -/
def FetchQueryWalkAt {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (pre : State) : Prop :=
  domain query ∧ query.request.raw.el = EL0 ∧ query.request.raw.ss = .SS_NonSecure ∧
  TranslateQueryChecks pre.regs spec.params query.va query.request.raw ∧
  OutputCacheAdmissible query.request.raw pre.regs ∧
  ∃ (leafLevel logical : Nat) (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat query.va spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root
      (.leaf leafLevel logical physical view)),
    Nonempty (PathPermissionUse spec config rows query path ⟨0#2, false, false⟩) ∧
    LeafMapAt mapping spec.physicalConfig pre.regs query leafLevel view

/-- COMPLETE actual `__FetchInstr pc` at EL0 AArch64 from current data. The
returned word is the actual current post-walk memory content at the actual PA,
for the ACTUAL oracle-drawn IFETCH descriptor `acc`. Query-independent walk
inputs are stated at the actual pre-read state `pre` (registers after the
wrapper's own two writes, same memory). No StepPins0/BTYPE0/BTN0/clrGP/
whole-memory equality/descriptor pin is used. -/
theorem native_fetch_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (step : StepFacts s.regs) (el : s.regs.PSTATE.EL = 0#2)
    (pcLow : Sail.BitVec.extractLsb s.regs._PC 1 0 = 0#2) (il : s.regs.PSTATE.IL = 0#1)
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (pre : State) (preRegs : pre.regs = fetchRegs s.regs) (preMem : pre.mem = s.mem)
    (lower : AArch64_GetVARange s.regs._PC = .VARange_LOWER)
    (current : HostWalkAt config spec.controls spec.physicalConfig pre)
    (mode : HostEL0ModeAt pre.regs)
    (aa64 : pre.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt pre.regs)
    (spe : pre.regs.bank_Bool .SPESampleInFlight = false)
    (bound : HostImageParamsAt pre.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (pre.regs.bank_BitVec_64 .TCR_EL2)})
    (geometry : spec.params.txsz = normalizeTxsz pre.regs
      (_get_TCR_EL2_Type_T0SZ (pre.regs.bank_BitVec_64 .TCR_EL2)))
    (layout : CurrentLayoutAt spec.layout spec.params s.regs._PC pre.regs)
    (images : CurrentImagesAt spec config rows pre)
    (guard : HostTranslateGuardAt pre.regs spec.params)
    (rawFault : sourceTxszFault pre.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (pre.regs.bank_BitVec_64 .TCR_EL2)} = false)
    (enabled : currentTranslationEnabled pre.regs = true)
    (cache : pre.regs.bank_Bool .__tlb_enabled = false)
    (epd : currentWalkEPD pre.regs s.regs._PC = 0#1)
    (mmio : MappedNotMMIO mapping s.regs._PC)
    (present : MappedBytesPresent mapping s.regs._PC s.mem)
    (perAcc : ∀ acc, ActualIFetchAcc s acc →
      FetchQueryWalkAt spec config rows mapping (queryOf acc) pre) :
    ∃ acc word final address faultOut translated leafLevel view,
      ActualIFetchAcc s acc ∧
      __FetchInstr s.regs._PC s = .ok (__InstrEnc.__A64, word) final ∧
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view pre
        (faultOut, address) translated ∧
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
        some (word.extractLsb' (8 * i) 8)) ∧
      final.regs = translated.regs ∧ final.mem = translated.mem ∧
      final.events = translated.events.push
        (.memRead address.paddress.address.toNat 4 (some s.regs._PC.toNat) (AK_ifetch ()) false) := by
  obtain ⟨acc, t, word, u, final, fetchCall, actual, tRegs, tMem, tEvents,
      ⟨address, faultOut, translated, leafLevel, view, clean, bytes, uEvents, uRegs, uMem⟩,
      fRegs, fMem, fEvents⟩ :=
    fetch_frame_post s step pcLow il
      (fun acc t word u => ∃ address faultOut translated leafLevel view,
        CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view pre
          (faultOut, address) translated ∧
        (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
          some (word.extractLsb' (8 * i) 8)) ∧
        u.events = translated.events.push
          (.memRead address.paddress.address.toNat 4 (some s.regs._PC.toNat) (AK_ifetch ()) false) ∧
        u.regs = translated.regs ∧ u.mem = translated.mem)
      (by
        intro t tRegs _ _
        obtain ⟨acc, after, call, _, frame⟩ :=
          MemM1.MemReadIF.createR t (by rw [tRegs]; exact step.rme) (by rw [tRegs]; exact step.nrw)
            (by rw [tRegs]; exact step.b3) (by rw [tRegs]; exact step.a3) (by rw [tRegs]; exact el)
            (by rw [tRegs]; exact step.ns)
        exact ⟨acc, after, call, frame⟩)
      (by
        intro acc actual t tRegs tMem _
        obtain ⟨t0, u0, t0Regs, t0Call⟩ := actual
        obtain ⟨acc0, after0, call0, shape0, _⟩ :=
          MemM1.MemReadIF.createR t0 (by rw [t0Regs]; exact step.rme) (by rw [t0Regs]; exact step.nrw)
            (by rw [t0Regs]; exact step.b3) (by rw [t0Regs]; exact step.a3) (by rw [t0Regs]; exact el)
            (by rw [t0Regs]; exact step.ns)
        have results := call0.symm.trans t0Call
        have same : acc0 = acc := by injection results
        subst same
        obtain ⟨member, accessEL, ss, checked, outputPolicy, leafLevel, logical, physical, view, path,
          ⟨binding⟩, map⟩ := perAcc acc0 ⟨t0, u0, t0Regs, t0Call⟩
        have va := vaOf acc0
        have raw := rawOf acc0
        have frameRegs : t.regs = pre.regs := tRegs.trans preRegs.symm
        have frameMem : t.mem = pre.mem := tMem.trans preMem.symm
        obtain ⟨address, faultOut, translated, word, final, clean, bytes, readCall, events, regs, mem⟩ :=
          native_mem_read_total spec config rows mapping (queryOf acc0) member leafLevel logical physical
            view path binding t (by rw [va]; exact lower)
            (host_walk_frame config spec.controls spec.physicalConfig pre t current frameRegs)
            (by simpa only [frameRegs] using mode) (by rw [frameRegs]; exact aa64)
            (by rw [frameRegs]; exact debug) (by rw [frameRegs]; exact spe)
            (by simpa only [frameRegs] using bound) (by simpa only [frameRegs] using geometry)
            (by rw [va]; exact layout.of_regs frameRegs) (images.frame frameRegs frameMem)
            (by simpa only [frameRegs] using guard) (by simpa only [frameRegs] using checked)
            (by simpa only [frameRegs] using rawFault) (by simpa only [frameRegs] using enabled)
            accessEL ss (by rw [frameRegs]; exact cache) (by rw [frameRegs, va]; exact epd)
            (by rw [frameRegs]; exact map) (by rw [frameRegs]; exact outputPolicy)
            (by rw [raw]; exact shape0) (by rw [va]; exact pc_low_aligned _ pcLow)
            (by rw [va]; exact mmio) (by rw [va, tMem]; exact present)
        have cleanPre := clean_translate_result_memory_frames spec config rows mapping (queryOf acc0)
          leafLevel view pre t translated translated (faultOut, address) frameRegs frameMem rfl rfl clean
        have kept := clean
        obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, registers, _⟩ := kept
        refine ⟨word, final, ?_, ?_, address, faultOut, translated, leafLevel, view, cleanPre, bytes,
          by rw [events, va], regs, mem⟩
        · rw [va, raw] at readCall; exact readCall
        · rw [regs, registers]
          unfold fetchGuardRegs
          split <;> rfl)
  exact ⟨acc, word, final, address, faultOut, translated, leafLevel, view, actual, fetchCall, clean,
    bytes, fRegs.trans uRegs, fMem.trans uMem, fEvents.trans uEvents⟩

#print axioms native_fetch_total
end ArmCertWalk
