import Bridge.CruxGenGuarded.EntryFetchedFacts
import Bridge.CruxGenGuarded.EntryBtiCTail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.EntryBtiStep
open ArmCertWalk ArmCert.Eval.M1a.Fetch2
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! entry template, first instruction: the WHOLE actual model step at the
public entry state runs Memory's actual fetch (current invariant at the actual
`beforeFetchState s`) and then the fixed BTI c class tail on the ACTUAL fetched
state. Current EntryPins/Input/MetadataGuard/HookQuiet/IT/SS at the fetched
state are derived (EntryFetchedFacts), not supplied.

`code` is the code-at-PC input: any word the actual walk exposes at the actual
translated PA is the BTI c encoding. It is to be discharged by C9
ImageOn binding (6c32 step 2); it is not a fetch-success or future answer.
Legal guarded landing (47d8fa2: BTYPE 00/01/10 action+check equations;
BTYPE 11 excluded by caller contract) remains a separate open composition:
the actual BTI step never invokes BranchTargetCheck. -/

run_cmd do
  IO.eprintln "CURRENT_DECL EntryBtiStep.entry_bti_step"
  (← IO.getStderr).flush

theorem entry_bti_step (real : Type) [Sail.SailReal real]
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
    ∃ fetched sp a fin,
      modelStep real s = .ok () fin ∧
      (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      NativeEntry.BtiC.projection a =
        NativeEntry.BtiC.expected (actionState (NativeEntryDispatch.BtiC.word) sp 97) ∧
      HookQuiet budget fin ∧ StepPins fin ∧ SysEq2 a.regs fin.regs ∧
      fin.mem = fetched.mem ∧ fin.events = fetched.events ∧
      fin.regs._PC = s.regs._PC + 4#64 ∧ fin.regs.PSTATE.DIT = a.regs.PSTATE.DIT := by
  obtain ⟨acc, w, fetched, enc0, address, faultOut, translated, leafLevel, view, _actual, hstep,
      clean, bytes, fregs, _fmem, _fev⟩ :=
    entry_fetch_current real spec config rows mapping s pins hGIC features debug base offset placed
      page word current queryOf rawOf vaOf mmio present perAcc
  have hw := code acc leafLevel view faultOut address translated w clean bytes
  subst hw
  obtain ⟨_, out, _, _, _, _, _, _, _, _, _, _, _, translatedRegs, _⟩ := clean
  have hregs : fetched.regs = FetchedRegs acc (translateCurrent out) s := by
    rw [fregs, translatedRegs, rawOf acc]; rfl
  have fpins := fetched_pins acc (translateCurrent out) s fetched pins hregs
  have finput := fetched_input acc (translateCurrent out) s fetched pins.el hregs
  obtain ⟨guard, fquiet, it, ss⟩ := fetched_rest acc (translateCurrent out) s fetched (budget + 1) pins quiet hregs
  obtain ⟨sp, a, fin, hook, _, tail, projection, _, finQuiet, finPins, sys, _, _, mem, events, _,
      dit, pc, _⟩ :=
    ArmBridge.CruxGenGuarded.EntryBtiC.native_tail real s fetched enc0 fpins finput guard budget fquiet it ss
  exact ⟨fetched, sp, a, fin, hstep.trans tail, hook, projection, finQuiet, finPins, sys, mem, events,
    pc, dit⟩
#print axioms entry_bti_step
end ArmBridge.CruxGenGuarded.EntryBtiStep
