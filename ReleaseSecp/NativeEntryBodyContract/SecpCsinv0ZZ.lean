import NativeEntryContract.Core
import NativeEntryBodyAdapters.SecpCsinv0ZZ
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyContract
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen NativeEntry NativeEntryContract
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace SecpCsinv0ZZ

/- GENERATED. Fixed class producer derives the canonical contract Frame from the
SAME actual selected-decoder result (NativeEntryBodyAdapters.SecpCsinv0ZZ.run). -/
set_option maxHeartbeats 1000000 in
theorem run (s : NativeState) (Rd : BitVec 5) (g : NativeEntryBody.SecpCsinv0ZZ.Guard s Rd)
    (ticks : Nat) (hq : ArmCert.HookQuiet.V0.HookQuiet ticks s) :
    ∃ t, (decode_csinv_aarch64_instrs_integer_conditional_select Rd 31#5 0#1 0#4 31#5 1#1 1#1 : SailM Unit) s = .ok () t ∧
      NativeEntryBody.SecpCsinv0ZZ.projection t = NativeEntryBody.SecpCsinv0ZZ.expected s Rd ∧
      Frame NativeEntryBodyAdapters.SecpCsinv0ZZ.writes s t ∧
      ArmCert.HookQuiet.V0.HookQuiet ticks t := by
  obtain ⟨t, action, projection, nonProj, quiet⟩ :=
    NativeEntryBodyAdapters.SecpCsinv0ZZ.run s Rd g ticks hq
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  refine ⟨t, action, projection, ?_, quiet⟩
  constructor
  all_goals first
    | exact nonProj
    | (rw [regs]; rfl)

#print axioms run
end SecpCsinv0ZZ
end NativeEntryBodyContract
