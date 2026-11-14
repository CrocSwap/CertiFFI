import NativeEntryContract.Core
import NativeEntryBodyAdapters.OrrImm32_0
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry NativeEntryContract
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace OrrImm32_0

/- GENERATED. Fixed class producer derives the canonical contract Frame from the
SAME actual selected-decoder result (NativeEntryBodyAdapters.OrrImm32_0.run). -/
set_option maxHeartbeats 1000000 in
theorem run (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (g : NativeEntryBody.OrrImm32_0.Guard s Rd Rn)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 0#6 32#6 1#1 1#2 1#1 : SailM Unit) s = .ok () t ∧
      NativeEntryBody.OrrImm32_0.projection t = NativeEntryBody.OrrImm32_0.expected s Rd Rn ∧
      Frame NativeEntryBodyAdapters.OrrImm32_0.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryBodyAdapters.OrrImm32_0.run s Rd Rn g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end OrrImm32_0
end NativeEntryBodyContract
