import NativeEntryContract.Core
import NativeEntryBodyAdapters.Movz64z
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry NativeEntryContract
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace Movz64z

/- GENERATED. Fixed class producer derives the canonical contract Frame from the
SAME actual selected-decoder result (NativeEntryBodyAdapters.Movz64z.run). -/
set_option maxHeartbeats 1000000 in
theorem run (s : NativeState) (Rd : BitVec 5) (imm16 : BitVec 16) (g : NativeEntryBody.Movz64z.Guard s Rd imm16)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 0#2 2#2 1#1 : SailM Unit) s = .ok () t ∧
      NativeEntryBody.Movz64z.projection t = NativeEntryBody.Movz64z.expected s Rd imm16 ∧
      Frame NativeEntryBodyAdapters.Movz64z.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryBodyAdapters.Movz64z.run s Rd imm16 g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end Movz64z
end NativeEntryBodyContract
