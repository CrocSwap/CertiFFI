import NativeEntryContract.Core
import NativeEntryBodyAdapters.AddSp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry NativeEntryContract
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace AddSp

/- GENERATED. Fixed class producer derives the canonical contract Frame from the
SAME actual selected-decoder result (NativeEntryBodyAdapters.AddSp.run). -/
set_option maxHeartbeats 1000000 in
theorem run (s : NativeState) (Rd : BitVec 5) (imm12 : BitVec 12) (g : NativeEntryBody.AddSp.Guard s Rd imm12)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd 31#5 imm12 0#1 0#1 0#1 1#1 : SailM Unit) s = .ok () t ∧
      NativeEntryBody.AddSp.projection t = NativeEntryBody.AddSp.expected s Rd imm12 ∧
      Frame NativeEntryBodyAdapters.AddSp.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryBodyAdapters.AddSp.run s Rd imm12 g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end AddSp
end NativeEntryBodyContract
