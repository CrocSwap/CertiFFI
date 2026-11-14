import NativeEntryContract.Core
import NativeEntryAdapters.IsbSy
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace IsbSy

/- Fixed class producer derives the new contract from the SAME actual result. -/
theorem run (s : NativeState)  (g : NativeEntry.IsbSy.Guard s)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4 : SailM Unit) s = .ok () t ∧
      NativeEntry.IsbSy.projection t = NativeEntry.IsbSy.expected s ∧
      Frame NativeEntryAdapters.IsbSy.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryAdapters.IsbSy.run s g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end IsbSy
end NativeEntryContract
