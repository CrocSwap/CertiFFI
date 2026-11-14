import ReleaseProfile.GB10.HeapPort.CTC2
import ReleaseProfile.GB10.HeapC2Normal

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

/-!
# Worked Heap CT positive C2 at the concrete clean world

Every CT residual atom is normal atom (ReleaseProfile.GB10.Heap.Normal, HeapC2Normal) at the
matching entry: e1 atoms at `callers.first`/`p1`, e2 atoms at `callers.second`/`p2`, shared program atoms
once. The shared catalogue/attribute configuration of the CT card is built from `callers.first`; e2 atoms
stated over it are transported with `sourceAttributes_caller`. Remaining hypothesis: the Translate static atoms
(`StaticsAt`, at either admitted caller, with the spec pinned at `callers.first`). `world_images`/`a211`
accept a spec pinned at any admitted caller (1b42bc72), so no SourceSpec transfer is needed.

CT -> normal index map (all 56 retained CT atoms; none relates both entries):
shared 17-21->16-20, 56->55, 245-247->244-246, 259-263->258-262, 268-269->267-268, 306->55, 506-508->260-262;
e1 57-60->56-59, 122-124->121-123, 211-212->210-211, 244->243, 257-258->256-257, 264-267->263-266, 270-271->269-270;
e2 307-310->56-59, 372-374->121-123, 461-462->210-211, 494->243, 504-505->256-257, 509-512->263-266, 513-514->269-270.
-/

namespace ReleaseProfile.GB10.Heap.CT

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Normal

/-- The tables' query domain. -/
abbrev Dom : ArmCert.Translate.Model.QueryDomain :=
  fun q => ∃ q0 ∈ HeapWorldTables.queries, ArmCertWalk.SamePage q0.va q.va

#check "CURRENT_DECL GB10.Heap.CT.heap_ct_c2_of_statics"
/-- Positive CT C2 for the worked Heap CT card at every admissible completion and admitted CT caller pair,
given the Translate static atoms at the clean world (for either admitted caller, spec pinned at the first). Every other residual atom is normal atom at the matching entry. -/
theorem heap_ct_c2_of_statics (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
    (statics : ∀ (caller : AdmissibleCaller rho) (pcount : BitVec 88)
      (spec : ArmCert.Translate.Model.TopologyImageSpec Dom),
      SourceSpec rho callers.first spec → spec.layout = HeapWorldTables.tables.layout →
      spec.logicalRows = HeapWorldTables.tables.logicalRows →
      spec.imageRows = HeapWorldTables.tables.imageRows → StaticsAt rho caller pcount spec) :
    CTC2 rho callers :=
  ct_c2_of_worlds rho callers worldSemantics worldSemantics W W timers_disabled timers_disabled HeapWorldTables.tables
    HeapWorldData.oracle
    (fun p1 p2 spec sspec hlay hlr hir timers1 timers2 =>
      have imgs1 := world_images rho callers.first p1 sspec hir
      have imgs2 := world_images rho callers.second p2 sspec hir
      have st1 := statics callers.first p1 spec sspec hlay hlr hir
      have st2 := statics callers.second p2 spec sspec hlay hlr hir
      have attr : sourceAttributes rho callers.second = sourceAttributes rho callers.first :=
        sourceAttributes_caller rho callers.second callers.first
      {
        timers1 := timers1,
        timers2 := timers2,
        a17 := a16, a18 := a17, a19 := a18, a20 := a19,
        a21 := st1.a20,
        a56 := ⟨imgs1.1.covered⟩,
        a57 := ⟨imgs1.1.topology⟩,
        a58 := ⟨imgs1.1.attributes⟩,
        a59 := ⟨imgs1.1.writeback⟩,
        a60 := ⟨imgs1.1.permissions⟩,
        a122 := a121 rho callers.first p1,
        a123 := st1.a122,
        a124 := st1.a123,
        a211 := ⟨imgs1.2⟩,
        a212 := a211 rho callers.first p1 sspec hir,
        a244 := a243 rho callers.first p1,
        a245 := st1.a244,
        a246 := a245, a247 := a246,
        a257 := st1.a256,
        a258 := a257 rho callers.first p1,
        a259 := st1.a258,
        a260 := a259,
        a261 := ⟨ReleaseProfile.GB10.BodyStaticR.ofFull st1.a260.holds⟩,
        a262 := a261,
        a263 := st1.a262,
        a264 := st1.a263,
        a265 := a264 rho callers.first p1,
        a266 := a265 rho callers.first p1,
        a267 := a266 rho callers.first p1,
        a268 := st1.a267,
        a269 := st1.a268,
        a270 := a269 rho callers.first p1,
        a271 := a270 rho callers.first p1,
        a306 := ⟨imgs1.1.covered⟩,
        a307 := ⟨imgs2.1.topology⟩,
        a308 := ⟨by have h := imgs2.1.attributes; rw [attr] at h; exact h⟩,
        a309 := ⟨by have h := imgs2.1.writeback; (try rw [attr] at h); exact h⟩,
        a310 := ⟨by have h := imgs2.1.permissions; (try rw [attr] at h); exact h⟩,
        a372 := a121 rho callers.second p2,
        a373 := ⟨by have h := st2.a122.holds; rw [attr] at h; exact h⟩,
        a374 := st2.a123,
        a461 := ⟨imgs2.2⟩,
        a462 := a211 rho callers.second p2 sspec hir,
        a494 := a243 rho callers.second p2,
        a504 := st2.a256,
        a505 := a257 rho callers.second p2,
        a506 := ⟨ReleaseProfile.GB10.BodyStaticR.ofFull st1.a260.holds⟩,
        a507 := a261,
        a508 := st1.a262,
        a509 := st2.a263,
        a510 := a264 rho callers.second p2,
        a511 := a265 rho callers.second p2,
        a512 := a266 rho callers.second p2,
        a513 := a269 rho callers.second p2,
        a514 := a270 rho callers.second p2
      })

end ReleaseProfile.GB10.Heap.CT

#print axioms ReleaseProfile.GB10.Heap.CT.heap_ct_c2_of_statics
