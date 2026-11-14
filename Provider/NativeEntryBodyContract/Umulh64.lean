import NativeEntryContract.Core
import NativeEntryBodyAdapters.Umulh64
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry NativeEntryContract
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace Umulh64

/- GENERATED. Fixed class producer derives the canonical contract Frame from the
SAME actual selected-decoder result (NativeEntryBodyAdapters.Umulh64.run). -/
set_option maxHeartbeats 1000000 in
theorem run (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (g : NativeEntryBody.Umulh64.Guard s Rd Rn Rm)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) s = .ok () t ∧
      NativeEntryBody.Umulh64.projection t = NativeEntryBody.Umulh64.expected s Rd Rn Rm ∧
      Frame NativeEntryBodyAdapters.Umulh64.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryBodyAdapters.Umulh64.run s Rd Rn Rm g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end Umulh64
end NativeEntryBodyContract
