import NativeEntryContract.Core
import NativeEntryBodyAdapters.Adc64ZRm
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry NativeEntryContract
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace Adc64ZRm

/- GENERATED. Fixed class producer derives the canonical contract Frame from the
SAME actual selected-decoder result (NativeEntryBodyAdapters.Adc64ZRm.run). -/
set_option maxHeartbeats 1000000 in
theorem run (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (g : NativeEntryBody.Adc64ZRm.Guard s Rd Rn)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 0#1 0#1 1#1 : SailM Unit) s = .ok () t ∧
      NativeEntryBody.Adc64ZRm.projection t = NativeEntryBody.Adc64ZRm.expected s Rd Rn ∧
      Frame NativeEntryBodyAdapters.Adc64ZRm.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryBodyAdapters.Adc64ZRm.run s Rd Rn g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end Adc64ZRm
end NativeEntryBodyContract
