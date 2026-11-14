import Bridge.CruxGenGuarded.EntryPrefetch
import Bridge.CruxGenGuarded.EntryE11Debug
import ArmCertWalk.NativeFetchTotal
import ArmCertWalk.NativeFetchCurrent
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.EntryActualFetch
open ArmCertWalk ArmCert.Eval.M1a.Fetch2
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! join of Memory's actual `__FetchInstr` (fetch-total 977e9a55,
`ArmCertWalk.native_fetch_total`) with Core's canonical
`entry_prefetch_boundary` at the SAME `beforeFetchState s`.

Core derives every register-side Memory input that EntryPins22, the approved
E11 MDE/HDE bits and the approved F6 feature bits already carry, transported
through the actual prefix writes. Walk/image/mapping data for the current
S1 regime remain explicit inputs at the actual pre-read state: they are the
same current-data obligations Memory states, not new public premises. No
StepPins0/BTYPE0/BTN0/clrGP/memory-equality/descriptor pin is used. -/

/-- Approved F6 / VHE feature bits at the entry state (unchanged by the
prefix and the fetch wrapper's own two writes). -/
structure EntryFeatures (r : Regs) : Prop where
  a0 : r.FeatureImpl[0] = false
  a1 : r.FeatureImpl[1] = false
  a2 : r.FeatureImpl[2] = false
  a3 : r.FeatureImpl[3] = false
  b1 : r.FeatureImpl[5] = true
  b2 : r.FeatureImpl[6] = true
  b3 : r.FeatureImpl[7] = true
  vhe : r.FeatureImpl[54] = true

run_cmd do
  IO.eprintln "CURRENT_DECL EntryActualFetch.before_fetch_facts"
  (← IO.getStderr).flush

/-- Register facts carried from the entry state to the actual fetch call. -/
theorem before_fetch_facts (s : ArmBridge.Draft.NativeState) (pins : NativeEntryTail.EntryPins s)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs) :
    StepFacts (ArmBridge.CruxGenGuarded.beforeFetchState s).regs ∧
    (ArmBridge.CruxGenGuarded.beforeFetchState s).regs.PSTATE.EL = 0#2 ∧
    (ArmBridge.CruxGenGuarded.beforeFetchState s).regs.PSTATE.IL = 0#1 ∧
    (ArmBridge.CruxGenGuarded.beforeFetchState s).regs._PC = s.regs._PC ∧
    (ArmBridge.CruxGenGuarded.beforeFetchState s).regs.__emulator_termination_opcode = none ∧
    E11Debug.E11CheckDebug (ArmBridge.CruxGenGuarded.beforeFetchState s).regs ∧
    HostEL0ModeAt (ArmBridge.CruxGenGuarded.beforeFetchState s).regs ∧
    (ArmBridge.CruxGenGuarded.beforeFetchState s).regs.bank_Bool .SPESampleInFlight = false := by
  have f4 : s.regs.FeatureImpl[4] = true := by simpa using pins.f4
  have rme : s.regs.FeatureImpl[232] = false := by simpa using pins.rme
  refine ⟨⟨features.a0, features.a1, features.a2, features.a3, f4, features.b1, features.b2,
      features.b3, pins.nrw, rme, ?_, ?_⟩, pins.el, pins.il, rfl, pins.emu, ⟨?_, ?_⟩,
      ⟨features.a2, features.b2, features.vhe, pins.el, ?_, ?_⟩, pins.spe⟩
  all_goals
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState,
      Sail.ConcurrencyInterfaceV1.RegMap.set_ne, Sail.ConcurrencyInterfaceV1.RegMap.set_same]
  · exact pins.scrns
  · exact pins.mdss
  · exact debug.mde
  · rw [ArmBridge.CruxCore.hde_pipeadv]; exact debug.hde
  · exact pins.scrns
  · exact pins.tge

run_cmd do
  IO.eprintln "CURRENT_DECL EntryActualFetch.entry_actual_fetch"
  (← IO.getStderr).flush

/-- Actual fetch at the canonical boundary: the model step from the entry
state is the native tail on the ACTUAL fetched state, whose word is the actual
post-walk bytes at the actual PA; fetched registers/memory are the actual
translated state and its events end with the actual ifetch read. -/
theorem entry_actual_fetch (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : ArmBridge.Draft.NativeState) (pins : NativeEntryTail.EntryPins s)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
    (pcLow : Sail.BitVec.extractLsb s.regs._PC 1 0 = 0#2)
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (pre : ArmBridge.Draft.NativeState)
    (preRegs : pre.regs = ArmCert.Eval.M1a.Fetch2.fetchRegs (ArmBridge.CruxGenGuarded.beforeFetchState s).regs)
    (preMem : pre.mem = s.mem)
    (lower : AArch64_GetVARange s.regs._PC = .VARange_LOWER)
    (current : HostWalkAt config spec.controls spec.physicalConfig pre)
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
    (perAcc : ∀ acc, ActualIFetchAcc (ArmBridge.CruxGenGuarded.beforeFetchState s) acc →
      FetchQueryWalkAt spec config rows mapping (queryOf acc) pre) :
    ∃ acc word fetched enc0 address faultOut translated leafLevel view,
      ActualIFetchAcc (ArmBridge.CruxGenGuarded.beforeFetchState s) acc ∧
      modelStep real s = nativeTail real s word enc0 fetched ∧
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view pre
        (faultOut, address) translated ∧
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
        some (word.extractLsb' (8 * i) 8)) ∧
      fetched.regs = translated.regs ∧ fetched.mem = translated.mem ∧
      fetched.events = translated.events.push
        (.memRead address.paddress.address.toNat 4 (some s.regs._PC.toNat) (AK_ifetch ()) false) := by
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  have modePre : HostEL0ModeAt pre.regs := by
    rw [preRegs]; exact ⟨mode.noEL2A32, mode.el2A64, mode.vhe, mode.el, mode.ns, mode.tge⟩
  have aa64Pre : pre.regs.FeatureImpl[4] = true := by
    rw [preRegs]; exact step.b0
  have debugPre : ExistingE11DebugAt pre.regs := by
    rw [preRegs]; exact ⟨e11.mde, e11.hde⟩
  have spePre : pre.regs.bank_Bool .SPESampleInFlight = false := by
    rw [preRegs]
    simp (disch := decide) only [ArmCert.Eval.M1a.Fetch2.fetchRegs, Register.__InstructionStep, Register.BTypeCompatible,
      Regs.ref_Bool, Sail.ConcurrencyInterfaceV1.RegMap.set_ne]
    exact spe
  obtain ⟨acc, word, final, address, faultOut, translated, leafLevel, view, actual, run, clean,
      bytes, fregs, fmem, fev⟩ :=
    native_fetch_total spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s) step el
      pcLow il queryOf rawOf vaOf pre preRegs preMem lower current modePre aa64Pre debugPre spePre
      bound geometry layout images guard rawFault enabled cache epd mmio present perAcc
  have emuFinal : final.regs.__emulator_termination_opcode = none := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
    rw [fregs, translatedRegs, fetchGuardRegs]
    split
    · simp only [gpRegs]; rw [preRegs]; exact emu0
    · rw [preRegs]; exact emu0
  obtain ⟨enc0, hstep⟩ := entry_prefetch_boundary real s final word pins hGIC run emuFinal
  exact ⟨acc, word, final, enc0, address, faultOut, translated, leafLevel, view, actual, hstep,
    clean, bytes, fregs, fmem, fev⟩

run_cmd do
  IO.eprintln "CURRENT_DECL EntryActualFetch.pc_low_of_placement"
  (← IO.getStderr).flush

/-- PC alignment for the fetch from the actual placement: entry PC = loader
base + declared semantic offset, the base page-aligned
(C7 loader-placement seam, still a producer obligation) and the offset 4-aligned.
No public PC-alignment answer. -/
theorem pc_low_of_placement (pc base offset : BitVec 64) (hpc : pc = base + offset)
    (page : base.toNat % 4096 = 0) (word : offset.toNat % 4 = 0) :
    Sail.BitVec.extractLsb pc 1 0 = 0#2 := by
  subst hpc
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_zero, BitVec.toNat_setWidth]
  omega

theorem heapv2_entry_offset_word : (0x10278#64 : BitVec 64).toNat % 4 = 0 := by decide

run_cmd do
  IO.eprintln "CURRENT_DECL EntryActualFetch.entry_fetch_current"
  (← IO.getStderr).flush

/-- Same join from Memory's `native_fetch_current` (c04cc28c): every walk input
is the canonical current-S1 invariant at the ACTUAL `beforeFetchState s`, with
per-actual-descriptor access data; no internal pre state. PC alignment comes
from placement; mapped-byte presence/NotMMIO remain the loader (C7) inputs. -/
theorem entry_fetch_current (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : ArmBridge.Draft.NativeState) (pins : NativeEntryTail.EntryPins s)
    (hGIC : s.regs.bank_Option_InterruptID .__GIC_Pending = none)
    (features : EntryFeatures s.regs) (debug : E11Debug.E11CheckDebug s.regs)
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
          (ArmBridge.CruxGenGuarded.beforeFetchState s)) :
    ∃ acc word fetched enc0 address faultOut translated leafLevel view,
      ActualIFetchAcc (ArmBridge.CruxGenGuarded.beforeFetchState s) acc ∧
      modelStep real s = nativeTail real s word enc0 fetched ∧
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view
        (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState s)) (faultOut, address) translated ∧
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
        some (word.extractLsb' (8 * i) 8)) ∧
      fetched.regs = translated.regs ∧ fetched.mem = translated.mem ∧
      fetched.events = translated.events.push
        (.memRead address.paddress.address.toNat 4 (some s.regs._PC.toNat) (AK_ifetch ()) false) := by
  obtain ⟨step, el, il, _pc, emu0, e11, mode, spe⟩ := before_fetch_facts s pins features debug
  obtain ⟨acc, word, final, address, faultOut, translated, leafLevel, view, actual, run, clean,
      bytes, fregs, fmem, fev⟩ :=
    native_fetch_current spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState s) step el
      (pc_low_of_placement _ base offset placed page word) il current mode step.b0 ⟨e11.mde, e11.hde⟩ spe
      queryOf rawOf vaOf mmio present perAcc
  have emuFinal : final.regs.__emulator_termination_opcode = none := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
    rw [fregs, translatedRegs, fetchGuardRegs]
    split
    · simp only [gpRegs]; exact emu0
    · exact emu0
  obtain ⟨enc0, hstep⟩ := entry_prefetch_boundary real s final word pins hGIC run emuFinal
  exact ⟨acc, word, final, enc0, address, faultOut, translated, leafLevel, view, actual, hstep,
    clean, bytes, fregs, fmem, fev⟩

#print axioms before_fetch_facts
#print axioms entry_fetch_current
#print axioms pc_low_of_placement
#print axioms entry_actual_fetch
end ArmBridge.CruxGenGuarded.EntryActualFetch
