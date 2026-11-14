import NativeEntryContract.Core
import NativeEntryAdapters.MrsDit
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace MrsDit

/- Fixed class producer derives the new contract from the SAME actual result. -/
theorem run (s : NativeState) (Rt : BitVec 5) (g : NativeEntry.MrsDit.Guard s Rt)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_mrs_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 1#1 : SailM Unit) s = .ok () t ∧
      NativeEntry.MrsDit.projection t = NativeEntry.MrsDit.expected s Rt ∧
      Frame NativeEntryAdapters.MrsDit.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryAdapters.MrsDit.run s Rt g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end MrsDit
end NativeEntryContract
