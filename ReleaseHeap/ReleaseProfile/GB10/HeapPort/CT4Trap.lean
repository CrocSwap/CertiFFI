import ReleaseProfile.GB10.HeapPort.CT4C2
import ReleaseProfile.GB10.HeapPort.Initial4Trap

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-! Heap CT4 (TrapPath 8, two callers) positive C2 at the trap world `HeapTrapWorld.world 4`.
Both entries are the trap world at callers.first / callers.second; the spec is pinned at callers.first; the
e2 attribute-config atoms transfer by `sourceAttributes_caller`. -/

namespace ReleaseProfile.GB10.Heap.Trap.CT4

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Normal
open ReleaseProfile.GB10.Heap.TrapInst (Wt Et)
open ReleaseProfile.GB10.Heap.Trap.T4 (t)

#check "CURRENT_DECL GB10.Heap.Trap.CT4.ct4_c2"
theorem ct4_c2 (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho) : CT4C2 rho callers :=
  ct4_c2_reduce rho callers worldSemantics worldSemantics (worldPayload (Wt t)) (worldPayload (Wt t)) (fun _ => rfl)
    (fun _ => rfl) HeapTrapTables.tables HeapWorldData.oracle (Wt t).rows (Wt t).mapping (Wt t).pins (Wt t).scope
    (Wt t).image (Wt t).loadBase (Wt t).base (Wt t).offS (Wt t).budget (Wt t).tablePlan (Wt t).tablePlan (fun _ => timers_disabled) (fun _ => timers_disabled)
    (fun p1 p2 spec sspec hlay hlr hir timers1 timers2 =>
      have imgs1 := T4.images rho callers.first p1 sspec hir
      have imgs2 : ArmCert.Translate.Model.CurrentImagesAt spec (sourceAttributes rho callers.first) (Wt t).rows
          (ArmBridge.CruxGenGuarded.beforeFetchState (Et rho callers.second t p2)) ∧
          ArmCertWalk.RawImageAt spec.imageRows (ArmBridge.CruxGenGuarded.beforeFetchState (Et rho callers.second t p2)).mem := by
        rw [sourceAttributes_caller rho callers.first callers.second]
        exact T4.images rho callers.second p2 sspec hir
      have closed2 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/closed"
          (ArmCert.Translate.Model.ClosedMembershipAt spec (sourceAttributes rho callers.first) (Wt t).rows (Wt t).mapping
            (ArmBridge.CruxGenGuarded.Release.shimMap spec (Wt t).mapping (Wt t).base (Wt t).pins)
            (ArmBridge.CruxGenGuarded.beforeFetchState (Et rho callers.second t p2))) := by
        rw [sourceAttributes_caller rho callers.first callers.second]
        exact HeapTrapClosed.a122 rho callers.second t p2 sspec hlay hlr hir
      {
        timers1 := timers1, timers2 := timers2,
        a17 := a16, a18 := a17, a19 := a18, a20 := a19,
        a21 := TrapInst.a20 t,
        a56 := ⟨imgs1.1.covered⟩, a57 := ⟨imgs1.1.topology⟩, a58 := ⟨imgs1.1.attributes⟩,
        a59 := ⟨imgs1.1.writeback⟩, a60 := ⟨imgs1.1.permissions⟩,
        a122 := T4.a121 rho callers.first p1,
        a123 := HeapTrapClosed.a122 rho callers.first t p1 sspec hlay hlr hir,
        a124 := TrapInst.a123 rho callers.first t p1,
        a211 := ⟨imgs1.2⟩,
        a212 := Variant.a211_tw rho callers.first p1 (Wt t) HeapTrapTables.tables (fun wr => by cases wr <;> decide) sspec hir,
        a244 := ⟨world_tagStatusRows rho callers.first (Wt t) p1 1⟩,
        a245 := TrapInst.a245 t hir,
        a246 := a245, a247 := a246,
        a257 := TrapInst.a257 rho callers.first t p1,
        a258 := T4.a257 rho callers.first p1,
        a259 := TrapInst.a259 t hir,
        a260 := a259,
        a263 := ⟨ReleaseProfile.GB10.CodeStaticR.ofFull (TrapInst.a262 t hir).holds⟩,
        a264 := TrapInst.a263all t,
        a265 := TrapInst.a264 t,
        a266 := TrapInst.a265 t,
        a267 := Normal.a261,
        a268 := TrapInst.a267 rho callers.first t p1,
        a269 := T4.a267 rho callers.first p1,
        a270 := T4.a268 rho callers.first p1,
        a271 := TrapInst.a270 rho callers.first t p1,
        a272 := TrapInst.a271 t,
        a273 := TrapInst.a272 t,
        a274 := TrapInst.a273 t,
        a275 := TrapInst.a274 t hir,
        a276 := TrapInst.a275 t hir,
        a277 := TrapInst.a276 hlr,
        a278 := T4.a276 rho callers.first p1,
        a313 := ⟨imgs2.1.covered⟩, a314 := ⟨imgs2.1.topology⟩, a315 := ⟨imgs2.1.attributes⟩,
        a316 := ⟨imgs2.1.writeback⟩, a317 := ⟨imgs2.1.permissions⟩,
        a379 := T4.a121 rho callers.second p2,
        a380 := closed2,
        a381 := TrapInst.a123 rho callers.second t p2,
        a468 := ⟨imgs2.2⟩,
        a469 := Variant.a211_tw rho callers.second p2 (Wt t) HeapTrapTables.tables (fun wr => by cases wr <;> decide) sspec hir,
        a501 := ⟨world_tagStatusRows rho callers.second (Wt t) p2 1⟩,
        a511 := TrapInst.a257 rho callers.second t p2,
        a512 := T4.a257 rho callers.second p2,
        a513 := ⟨ReleaseProfile.GB10.CodeStaticR.ofFull (TrapInst.a262 t hir).holds⟩,
        a514 := TrapInst.a263all t,
        a515 := TrapInst.a264 t,
        a516 := TrapInst.a265 t,
        a517 := Normal.a261,
        a518 := TrapInst.a267 rho callers.second t p2,
        a519 := T4.a267 rho callers.second p2,
        a520 := T4.a268 rho callers.second p2,
        a521 := TrapInst.a270 rho callers.second t p2,
        a522 := TrapInst.a271 t,
        a523 := TrapInst.a272 t,
        a524 := TrapInst.a273 t,
        a525 := TrapInst.a274 t hir,
        a526 := TrapInst.a275 t hir,
        a527 := T4.a276 rho callers.second p2
      })

end ReleaseProfile.GB10.Heap.Trap.CT4

#print axioms ReleaseProfile.GB10.Heap.Trap.CT4.ct4_c2
