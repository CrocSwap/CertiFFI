import NativeEntry.BtiC
import NativeEntry.Effects
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
import NativeEntryAdapters.PreludeInput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryAdapters.BtiC
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/- GENERATED class-fixed register permission. No caller chooses Writes. -/
def writes : Effects.Writes := {}




/- Actual SAME decoder successor, not execution of an expected-state function.
quiet_of_fields is the existing canonical Q transport, reused without a clone.
All choices/counters and actual input memory remain those of the original run. -/
theorem run (s : NativeState)  
    (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_bti_aarch64_instrs_system_hints 2#3 4#4 : SailM Unit) s = .ok () t ∧
      BtiC.projection t = BtiC.expected s ∧
      Effects.Frame writes s.regs t.regs ∧ HookQuiet ticks t := by
  obtain ⟨t, success, projection⟩ := BtiC.effect s
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

end NativeEntryAdapters.BtiC
