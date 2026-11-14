import NativeEntryContract.Core
import NativeEntryBodyAdapters.SecpLsr63
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry NativeEntryContract
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace SecpLsr63

/- GENERATED. Fixed class producer derives the canonical contract Frame from the
SAME actual selected-decoder result (NativeEntryBodyAdapters.SecpLsr63.run). -/
set_option maxHeartbeats 1000000 in
theorem run (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (g : NativeEntryBody.SecpLsr63.Guard s Rd Rn)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 63#6 1#1 2#2 1#1 : SailM Unit) s = .ok () t ∧
      NativeEntryBody.SecpLsr63.projection t = NativeEntryBody.SecpLsr63.expected s Rd Rn ∧
      Frame NativeEntryBodyAdapters.SecpLsr63.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryBodyAdapters.SecpLsr63.run s Rd Rn g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end SecpLsr63
end NativeEntryBodyContract
