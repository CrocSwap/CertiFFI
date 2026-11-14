import NativeEntryContract.Core
import NativeEntryBodyAdapters.OrrMov64
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry NativeEntryContract
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace OrrMov64

/- GENERATED. Fixed class producer derives the canonical contract Frame from the
SAME actual selected-decoder result (NativeEntryBodyAdapters.OrrMov64.run). -/
set_option maxHeartbeats 1000000 in
theorem run (s : NativeState) (Rd : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (g : NativeEntryBody.OrrMov64.Guard s Rd imm6 Rm)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd 31#5 imm6 Rm 0#1 0#2 1#2 1#1 : SailM Unit) s = .ok () t ∧
      NativeEntryBody.OrrMov64.projection t = NativeEntryBody.OrrMov64.expected s Rd imm6 Rm ∧
      Frame NativeEntryBodyAdapters.OrrMov64.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryBodyAdapters.OrrMov64.run s Rd imm6 Rm g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end OrrMov64
end NativeEntryBodyContract
