import NativeEntry.IsbSy
import NativeEntry.Effects
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
import NativeEntryAdapters.PreludeInput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryAdapters.IsbSy
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- GENERATED class-fixed register permission. No caller chooses Writes. -/
def writes : Effects.Writes := {}

structure Profile (s : NativeState) : Prop where
  aa32el2 : s.regs.FeatureImpl[2]! = false
  aa32el3 : s.regs.FeatureImpl[3]! = false
  aa64el2 : s.regs.FeatureImpl[6]! = true
  aa64el3 : s.regs.FeatureImpl[7]! = true
  brbe : s.regs.FeatureImpl[230]! = false


/- Internal guard producer: current pins/Q are derived by the canonical actual
prelude, and word is its actual metadata equality. Profile reads only source
features transported by ControlInput. There is NO source/current memory equation.
These are not new caller-facing admission answers or a landing-domain theorem. -/
theorem guard_of_context (source current : NativeState) 
    (profile : Profile source) (input : Effects.ControlInput source current)
    (hp : StepPins current) (ticks : Nat) (hq : HookQuiet ticks current)
      : IsbSy.Guard current where
  el := by exact hp.el
  a64 := by exact hp.nrw
  aa64 := by exact hp.f4
  aa32el2 := by rw [input.features]; exact profile.aa32el2
  aa32el3 := by rw [input.features]; exact profile.aa32el3
  aa64el2 := by rw [input.features]; exact profile.aa64el2
  aa64el3 := by rw [input.features]; exact profile.aa64el3
  rme := by exact hp.rme
  e2h := by exact hp.e2h
  tge := by exact hp.tge
  ns := by exact hp.scrns
  brbe := by rw [input.features]; exact profile.brbe
  spe := by exact hp.spe

#print axioms guard_of_context

/- Direct connection to the existing canonical metadata state. Its quietness,
pins, source control transport and instruction word are DERIVED here. Actual
afterSpec and its Q/pins come from the constructed native prelude/hook proof.
No metadata-state guess or future guard is requested from a public caller. -/
theorem guard_at_metadata (source afterSpec : NativeState) 
    (w : BitVec 32) (K : Int) (profile : Profile source)
    (input : Effects.ControlInput source afterSpec) (hp : StepPins afterSpec)
    (ticks : Nat) (hq : HookQuiet ticks afterSpec)  :
    IsbSy.Guard (actionState (w) afterSpec K) := by
  have metadata_input : Effects.ControlInput afterSpec (actionState (w) afterSpec K) :=
    ⟨BookkeepingGuard.GuardedBookkeepingNonProj.actionState_nonProj (w) afterSpec K, rfl⟩
  exact guard_of_context source (actionState (w) afterSpec K)
    profile (input.trans metadata_input)
    (metadata_pins (w) afterSpec K hp) ticks
    (actionState_quiet (w) afterSpec K ticks hq)

#print axioms guard_at_metadata


/- Actual SAME decoder successor, not execution of an expected-state function.
quiet_of_fields is the existing canonical Q transport, reused without a clone.
All choices/counters and actual input memory remain those of the original run. -/
theorem run (s : NativeState)  (g : IsbSy.Guard s)
    (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4 : SailM Unit) s = .ok () t ∧
      IsbSy.projection t = IsbSy.expected s ∧
      Effects.Frame writes s.regs t.regs ∧ HookQuiet ticks t := by
  obtain ⟨t, success, projection⟩ := IsbSy.effect s g
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  have fields : GuardFieldsEq s t := by
    constructor
    all_goals first
      | (rw [regs]; rfl)
      | (intro k hk; rw [regs]; rfl)
  refine ⟨t, success, projection, ?_, quiet_of_fields ticks s t hq fields⟩
  change Effects.mask writes t.regs = Effects.mask writes s.regs
  rw [regs]
  rfl

#print axioms run

/- Composition consumes the guard internally. This is still selected-decoder
progress at canonical metadata, not outer DecodeA64 dispatch/modelStep. -/
theorem run_at_metadata (source afterSpec : NativeState) 
    (w : BitVec 32) (K : Int) (profile : Profile source)
    (input : Effects.ControlInput source afterSpec) (hp : StepPins afterSpec)
    (ticks : Nat) (hq : HookQuiet ticks afterSpec)  :
    ∃ t, (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4 : SailM Unit) (actionState (w) afterSpec K) = .ok () t ∧
      IsbSy.projection t = IsbSy.expected (actionState (w) afterSpec K) ∧
      Effects.Frame writes (actionState (w) afterSpec K).regs t.regs ∧ HookQuiet ticks t :=
  run (actionState (w) afterSpec K) (guard_at_metadata source afterSpec w K profile input hp ticks hq) ticks
    (actionState_quiet (w) afterSpec K ticks hq)

#print axioms run_at_metadata

/- The constructed spec hook and metadata guards are both internal to this
adapter. The final common pipeline must establish the actual fetched input
relation/pins/Q; no initial-memory identity is imposed here. -/
theorem run_after_spec (source fetched : NativeState) 
    (w : BitVec 32) (K : Int) (profile : Profile source)
    (input : Effects.ControlInput source fetched) (hp : StepPins fetched)
    (ticks : Nat) (hq : HookQuiet ticks fetched)  :
    ∃ sp t, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      sp.mem = fetched.mem ∧ sp.events = fetched.events ∧
      (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4 : SailM Unit) (actionState (w) sp K) = .ok () t ∧
      IsbSy.projection t = IsbSy.expected (actionState (w) sp K) ∧
      Effects.Frame writes (actionState (w) sp K).regs t.regs ∧
      HookQuiet ticks t := by
  obtain ⟨sp, hook, controls, pins, quiet, mem, events⟩ :=
    PreludeInput.after_spec source fetched input hp ticks hq
  obtain ⟨t, action, projection, frame, finalQuiet⟩ :=
    run_at_metadata source sp w K profile controls pins ticks quiet
  exact ⟨sp, t, hook, mem, events, action, projection, frame, finalQuiet⟩

#print axioms run_after_spec

end NativeEntryAdapters.IsbSy
