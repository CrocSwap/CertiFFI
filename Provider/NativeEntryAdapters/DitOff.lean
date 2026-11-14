import NativeEntry.DitOff
import NativeEntry.Effects
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
import NativeEntryAdapters.PreludeInput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryAdapters.DitOff
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- GENERATED class-fixed register permission. No caller chooses Writes. -/
def writes : Effects.Writes := { dit := true }

structure Profile (s : NativeState) : Prop where
  dit : s.regs.FeatureImpl[103]! = true
  bti : s.regs.FeatureImpl[123]! = true
  tme : s.regs.FeatureImpl[227]! = false


/- Internal guard producer: current pins/Q are derived by the canonical actual
prelude, and word is its actual metadata equality. Profile reads only source
features transported by ControlInput. There is NO source/current memory equation.
These are not new caller-facing admission answers or a landing-domain theorem. -/
theorem guard_of_context (source current : NativeState) 
    (profile : Profile source) (input : Effects.ControlInput source current)
    (hp : StepPins current) (ticks : Nat) (hq : HookQuiet ticks current)
     (word : current.regs.bank_BitVec_32 .__ThisInstr = 0xd503405f#32) : DitOff.Guard current where
  el := by exact hp.el
  a64 := by exact hp.nrw
  aa64 := by exact hp.f4
  btype := by exact hp.btype
  word := by exact word
  dit := by rw [input.features]; exact profile.dit
  bti := by rw [input.features]; exact profile.bti
  tme := by rw [input.features]; exact profile.tme

#print axioms guard_of_context

/- Direct connection to the existing canonical metadata state. Its quietness,
pins, source control transport and instruction word are DERIVED here. Actual
afterSpec and its Q/pins come from the constructed native prelude/hook proof.
No metadata-state guess or future guard is requested from a public caller. -/
theorem guard_at_metadata (source afterSpec : NativeState) 
     (K : Int) (profile : Profile source)
    (input : Effects.ControlInput source afterSpec) (hp : StepPins afterSpec)
    (ticks : Nat) (hq : HookQuiet ticks afterSpec)  :
    DitOff.Guard (actionState (0xd503405f#32) afterSpec K) := by
  have metadata_input : Effects.ControlInput afterSpec (actionState (0xd503405f#32) afterSpec K) :=
    ⟨BookkeepingGuard.GuardedBookkeepingNonProj.actionState_nonProj (0xd503405f#32) afterSpec K, rfl⟩
  exact guard_of_context source (actionState (0xd503405f#32) afterSpec K)
    profile (input.trans metadata_input)
    (metadata_pins (0xd503405f#32) afterSpec K hp) ticks
    (actionState_quiet (0xd503405f#32) afterSpec K ticks hq) (by simp only [actionState, RegMap.set_same])

#print axioms guard_at_metadata


/- Actual SAME decoder successor, not execution of an expected-state function.
quiet_of_fields is the existing canonical Q transport, reused without a clone.
All choices/counters and actual input memory remain those of the original run. -/
theorem run (s : NativeState)  (g : DitOff.Guard s)
    (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 0#4 3#3 : SailM Unit) s = .ok () t ∧
      DitOff.projection t = DitOff.expected s ∧
      Effects.Frame writes s.regs t.regs ∧ HookQuiet ticks t := by
  obtain ⟨t, success, projection⟩ := DitOff.effect s g
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
     (K : Int) (profile : Profile source)
    (input : Effects.ControlInput source afterSpec) (hp : StepPins afterSpec)
    (ticks : Nat) (hq : HookQuiet ticks afterSpec)  :
    ∃ t, (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 0#4 3#3 : SailM Unit) (actionState (0xd503405f#32) afterSpec K) = .ok () t ∧
      DitOff.projection t = DitOff.expected (actionState (0xd503405f#32) afterSpec K) ∧
      Effects.Frame writes (actionState (0xd503405f#32) afterSpec K).regs t.regs ∧ HookQuiet ticks t :=
  run (actionState (0xd503405f#32) afterSpec K) (guard_at_metadata source afterSpec K profile input hp ticks hq) ticks
    (actionState_quiet (0xd503405f#32) afterSpec K ticks hq)

#print axioms run_at_metadata

/- The constructed spec hook and metadata guards are both internal to this
adapter. The final common pipeline must establish the actual fetched input
relation/pins/Q; no initial-memory identity is imposed here. -/
theorem run_after_spec (source fetched : NativeState) 
     (K : Int) (profile : Profile source)
    (input : Effects.ControlInput source fetched) (hp : StepPins fetched)
    (ticks : Nat) (hq : HookQuiet ticks fetched)  :
    ∃ sp t, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) fetched = .ok () sp ∧
      sp.mem = fetched.mem ∧ sp.events = fetched.events ∧
      (decode_msr_imm_aarch64_instrs_system_register_cpsr 2#3 0#4 3#3 : SailM Unit) (actionState (0xd503405f#32) sp K) = .ok () t ∧
      DitOff.projection t = DitOff.expected (actionState (0xd503405f#32) sp K) ∧
      Effects.Frame writes (actionState (0xd503405f#32) sp K).regs t.regs ∧
      HookQuiet ticks t := by
  obtain ⟨sp, hook, controls, pins, quiet, mem, events⟩ :=
    PreludeInput.after_spec source fetched input hp ticks hq
  obtain ⟨t, action, projection, frame, finalQuiet⟩ :=
    run_at_metadata source sp K profile controls pins ticks quiet
  exact ⟨sp, t, hook, mem, events, action, projection, frame, finalQuiet⟩

#print axioms run_after_spec

end NativeEntryAdapters.DitOff
