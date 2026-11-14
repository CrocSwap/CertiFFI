import NativeEntryContract.Core
import NativeEntryAdapters.MsrDit
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace MsrDit

/- Fixed class producer derives the new contract from the SAME actual result. -/
theorem run (s : NativeState) (Rt : BitVec 5) (g : NativeEntry.MsrDit.Guard s Rt)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1 : SailM Unit) s = .ok () t ∧
      NativeEntry.MsrDit.projection t = NativeEntry.MsrDit.expected s Rt ∧
      Frame NativeEntryAdapters.MsrDit.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryAdapters.MsrDit.run s Rt g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end MsrDit
end NativeEntryContract
