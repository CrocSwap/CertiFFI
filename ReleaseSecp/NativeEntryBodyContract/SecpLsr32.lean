import NativeEntryContract.Core
import NativeEntryBodyAdapters.SecpLsr32
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry NativeEntryContract
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace SecpLsr32

/- GENERATED. Fixed class producer derives the canonical contract Frame from the
SAME actual selected-decoder result (NativeEntryBodyAdapters.SecpLsr32.run). -/
set_option maxHeartbeats 1000000 in
theorem run (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (g : NativeEntryBody.SecpLsr32.Guard s Rd Rn)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 32#6 1#1 2#2 1#1 : SailM Unit) s = .ok () t ∧
      NativeEntryBody.SecpLsr32.projection t = NativeEntryBody.SecpLsr32.expected s Rd Rn ∧
      Frame NativeEntryBodyAdapters.SecpLsr32.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryBodyAdapters.SecpLsr32.run s Rd Rn g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end SecpLsr32
end NativeEntryBodyContract
