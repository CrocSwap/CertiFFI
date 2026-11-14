-- Vendored from loops ws/LoopNative/SubImm64/Contract.lean, renamed LoopNative.SubImm64 -> Route7Sub (route 7 unit 3,).
import NativeEntryContract.Core
import Route7Sub.Adapter
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry NativeEntryContract
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace Route7Sub.Contract

/- GENERATED. Fixed class producer derives the canonical contract Frame from the
SAME actual selected-decoder result (Route7Sub.Adapter.run). -/
set_option maxHeartbeats 200000 in
theorem run (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) (g : Route7Sub.Guard s Rd Rn imm12)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 0#1 1#1 1#1 : SailM Unit) s = .ok () t ∧
      Route7Sub.projection t = Route7Sub.expected s Rd Rn imm12 ∧
      Frame Route7Sub.Adapter.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    Route7Sub.Adapter.run s Rd Rn imm12 g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end Route7Sub.Contract
