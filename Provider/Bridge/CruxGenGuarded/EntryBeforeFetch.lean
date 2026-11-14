import Bridge.CruxGenGuarded.EntryPrefetch
import Bridge.CruxGenGuarded.Metadata
import Bridge.CruxGenGuarded.QuietTransport
import NativeEntryInput.Input
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxNonProj ArmCertCT.CT2
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/- Actual prefix state, before any fetch/walk: no memory or event update.
All helpers concern the unchanged imported canonical state constructor.
Fetch still must derive its own result, register/control frame and raw traffic. -/
run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.entry_before_fetch_input"
  (← IO.getStderr).flush

theorem entry_before_fetch_input (s : NativeState) (el : s.regs.PSTATE.EL = 0#2) :
    NativeEntryInput.Input s (beforeFetchState s) := by
  have nonProj : NonProjRegsEq bkHeap s.regs (beforeFetchState s).regs := by
    simp (disch := decide) only [NonProjRegsEq, mask, beforeFetchState, maskBank_set]
  constructor
  all_goals first
    | rfl
    | exact el
    | exact ⟨nonProj, rfl⟩
    | (constructor <;> simp (disch := decide) only [beforeFetchState, RegMap.set_ne,
        RegMap.set_same, hde_pipeadv])

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.entry_before_fetch_pins"
  (← IO.getStderr).flush

theorem entry_before_fetch_pins (s : NativeState) (hp : NativeEntryTail.EntryPins s) :
    NativeEntryTail.EntryPins (beforeFetchState s) := by
  constructor
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.f4
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.rme
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.spe
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.el
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.nrw
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.edecr
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.cti
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.st
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.edesr
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.btt
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.emu
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.e2h
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.tge
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.scrns
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.pmbe
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.mdss
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.pmbs
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.da
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.di
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.df
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.il
  · simpa (disch := decide) only [beforeFetchState, RegMap.set_ne,
      RegMap.set_same, _get_EDSCR_Type_STATUS, status_pipeadv] using hp.pss

theorem entry_before_fetch_metadata (s : NativeState) (hp : NativeEntryTail.EntryPins s) :
    MetadataGuard (beforeFetchState s) := by
  have p := entry_before_fetch_pins s hp
  exact ⟨p.f4, p.rme, p.el, p.nrw, p.e2h, p.tge, p.scrns, p.pmbe, p.st, rfl⟩

theorem entry_before_fetch_quiet (s : NativeState) (ticks : Nat) (q : HookQuiet ticks s) :
    HookQuiet ticks (beforeFetchState s) := by
  apply quiet_of_fields ticks s _ q
  constructor
  all_goals first
    | rfl
    | (intro k hk
       simp (disch := first | assumption | exact Ne.symm hk | decide) only
         [beforeFetchState, RegMap.set_ne])
    | (simp (disch := decide) only [beforeFetchState, RegMap.set_ne])

theorem entry_before_fetch_raw (s : NativeState) :
    (beforeFetchState s).mem = s.mem ∧ (beforeFetchState s).events = s.events ∧
    (beforeFetchState s).regs.ShouldAdvanceIT = false ∧
    (beforeFetchState s).regs.ShouldAdvanceSS = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms entry_before_fetch_input
#print axioms entry_before_fetch_pins
#print axioms entry_before_fetch_metadata
#print axioms entry_before_fetch_quiet
#print axioms entry_before_fetch_raw
end ArmBridge.CruxGenGuarded
