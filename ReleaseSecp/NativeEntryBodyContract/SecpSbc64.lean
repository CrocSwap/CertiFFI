import NativeEntryContract.Core
import NativeEntryBodyAdapters.SecpSbc64
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry NativeEntryContract
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace SecpSbc64

/- GENERATED. Fixed class producer derives the canonical contract Frame from the
SAME actual selected-decoder result (NativeEntryBodyAdapters.SecpSbc64.run). -/
set_option maxHeartbeats 1000000 in
theorem run (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (g : NativeEntryBody.SecpSbc64.Guard s Rd Rn Rm)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 1#1 1#1 : SailM Unit) s = .ok () t ∧
      NativeEntryBody.SecpSbc64.projection t = NativeEntryBody.SecpSbc64.expected s Rd Rn Rm ∧
      Frame NativeEntryBodyAdapters.SecpSbc64.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryBodyAdapters.SecpSbc64.run s Rd Rn Rm g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end SecpSbc64
end NativeEntryBodyContract
