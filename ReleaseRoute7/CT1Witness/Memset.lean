-- CT1 M4: distinct-secret non-vacuity witness for route-7 memset CT0.
-- Two entries on loops' route-7 C2 world, same completion / caller / tables / mapping / base / d / n / returnPC,
-- differing ONLY in the secret fill (x1 = 0x5a vs 0xa5). Every Lean premise of Route7Root.memsetCT0FromSource is
-- discharged in the concrete world, including the tag-status rows (the world oracle is zeroOracle), and the CT0
-- conclusion is then obtained for this distinct-secret pair.
import Route7GB10.C2
import Route7Root.CT0Set
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace CT1Witness.Memset
open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.MachineSource ReleaseProfile.GB10
open ArmCertLoop ArmCertLoop.ContractDraft Route7GB10 Route7GB10.Closed CertiFFI.Claim ArmBridge.CruxGenGuarded

def fill1 : BitVec 64 := 0x5a#64
def fill2 : BitVec 64 := 0xa5#64

/-- The world's oracle answers every tag-status draw with 0 (tag check OK). -/
theorem status_rows (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (x1 : BitVec 64) (n : Nat) :
    NativeMteTagCheck.TagStatusRows (E rho caller (gprsOf x1) Generated.armcert_memset_entry 0#88)
      ((E rho caller (gprsOf x1) Generated.armcert_memset_entry 0#88).choiceOcc.getD 1354 0) n := by
  intro i _
  rfl

/-- The memset rows at a world entry with fill x1 (loops' memset_c2 rows, generalised from fillA to any fill). -/
theorem rows_at (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (x1 : BitVec 64)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (hir : spec.imageRows = World.imageRows) (hlr : spec.logicalRows = World.logicalRows) :
    Route7Root.MemsetRows spec World.mapping Plan.B dA x1 retA 1
      (E rho caller (gprsOf x1) Generated.armcert_memset_entry 0#88) := by
  have hss : ∀ span ∈ [destSpan dA 1], span.length = 1 ∧ (span.base = sA ∨ span.base = dA) := by
    intro span hs
    simp only [destSpan, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs; simp
  refine ⟨⟨by decide⟩, ⟨by decide⟩, ⟨by decide⟩, ⟨by unfold SpanMap.NoWrap destSpan dA; decide⟩,
    ⟨Plan.codeGeometry⟩, ⟨codeWrite⟩, ⟨?_⟩, ⟨injective_spans _ hss⟩,
    ⟨by rw [hir]; exact Plan.separatedAt⟩, ⟨?_⟩, ⟨by rw [hlr]; exact World.keys_nodup⟩⟩
  · intro i hi
    rw [hir]
    exact dataGeom_spans _ hss (destSpan dA 1) (by simp) i hi
  · simp only [gprs_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [gprsOf, HeapV2StepCerts.RegBind.regVal]

theorem residual_at (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (x1 : BitVec 64)
    {domain : QueryDomain} (spec : TopologyImageSpec domain) (sspec : SourceSpec rho caller spec)
    (hlr : spec.logicalRows = World.logicalRows) (hir : spec.imageRows = World.imageRows)
    (hlay : spec.layout = World.layout)
    (hdom : ∀ q : AccessQuery, (∃ q0 ∈ World.queries, ArmCertWalk.SamePage q0.va q.va) → domain q)
    (rws : Route7Root.MemsetRows spec World.mapping Plan.B dA x1 retA 1
      (E rho caller (gprsOf x1) Generated.armcert_memset_entry 0#88)) :
    Route7Entry.EntryResidual spec World.permissionRows World.mapping
      (Route7Root.memsetConsumer spec World.mapping Plan.B dA 1) codeScope image Plan.B
      (SetNative.offset (rws.context (sourceAttributes rho caller) World.permissionRows)) rho caller
      (E rho caller (gprsOf x1) Generated.armcert_memset_entry 0#88) := by
  have hss : ∀ span ∈ [destSpan dA 1], span.length = 1 ∧ (span.base = sA ∨ span.base = dA) := by
    intro span hs
    simp only [destSpan, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs; simp
  exact residual rho caller (gprsOf x1) Generated.armcert_memset_entry 0#88 spec sspec hlr hir hlay
    hdom _ hss _ (by
      show (Plan.B + BitVec.ofNat 64 Generated.armcert_memset_entry : BitVec 64) =
        Plan.B + SetNative.offset (rws.context (sourceAttributes rho caller) World.permissionRows) 0
      simp only [SetNative.offset, Route7Root.MemsetRows.context]
      decide)

/-- **memset CT0 distinct-secret witness.** There are a completion, a CT caller pair, and two entries e1 / e2 that
    satisfy EVERY Lean premise of `Route7Root.memsetCT0FromSource` (agreement, SourceSpec, timers, memset rows, entry
    residual, tag-status rows) with the same public binders and DIFFERENT secret fills (decided: 0x5a ≠ 0xa5); for this
 pair the CT0 conclusion holds. -/
theorem memset_ct0_witness (real : Type) [Sail.SailReal real] :
    ∃ (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
      (cfg1 : Configuration rho callers.first) (cfg2 : Configuration rho callers.second)
      (domain : QueryDomain) (spec : TopologyImageSpec domain) (rows : List PermissionRow)
      (mapping : BitVec 64 → Option Nat) (base d f1 f2 returnPC : BitVec 64) (n : Nat) (e1 e2 : ArmBridge.Draft.NativeState)
      (ag1 : AgreesAt cfg1 e1.regs) (ag2 : AgreesAt cfg2 e2.regs)
      (sspec1 : SourceSpec rho callers.first spec) (sspec2 : SourceSpec rho callers.second spec)
      (timers1 : TimersQuiet e1.regs (Schedule.setSteps n)) (timers2 : TimersQuiet e2.regs (Schedule.setSteps n))
      (rws1 : Route7Root.MemsetRows spec mapping base d f1 returnPC n e1)
      (rws2 : Route7Root.MemsetRows spec mapping base d f2 returnPC n e2)
      (res1 : Route7Entry.EntryResidual spec rows mapping (Route7Root.memsetConsumer spec mapping base d n) codeScope image
        base (SetNative.offset (rws1.context (sourceAttributes rho callers.first) rows)) rho callers.first e1)
      (res2 : Route7Entry.EntryResidual spec rows mapping (Route7Root.memsetConsumer spec mapping base d n) codeScope image
        base (SetNative.offset (rws2.context (sourceAttributes rho callers.second) rows)) rho callers.second e2)
      (statusRows1 : DeploymentObligation "loop:memset:tag-status-rows"
        (NativeMteTagCheck.TagStatusRows e1 (e1.choiceOcc.getD 1354 0) n))
      (statusRows2 : DeploymentObligation "loop:memset:tag-status-rows"
        (NativeMteTagCheck.TagStatusRows e2 (e2.choiceOcc.getD 1354 0) n)),
      f1 ≠ f2 ∧
      PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.setSteps n))
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.setSteps n)) := by
  obtain ⟨⟨rho⟩, callerOf, -, -⟩ := sourceDomainWitness
  obtain ⟨c⟩ := callerOf rho
  let callers : AdmissibleCTCallers rho := AdmissibleCTCallers.ofCallers c c
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho c tables oracle
    (Plan.payload (gprsOf fill1) Generated.armcert_memset_entry 0#88).data
    (E rho c (gprsOf fill1) Generated.armcert_memset_entry 0#88) rfl
  have hir' : spec.imageRows = World.imageRows := hir
  have hlr' : spec.logicalRows = World.logicalRows := hlr
  have hlay' : spec.layout = World.layout := hl
  have rws1 := rows_at rho c fill1 spec hir' hlr'
  have rws2 := rows_at rho c fill2 spec hir' hlr'
  have t1 := model_timersQuiet worldSemantics rho c (Plan.payload (gprsOf fill1) Generated.armcert_memset_entry 0#88)
    (Plan.timers_disabled _ _ _) (Schedule.setSteps 1)
  have t2 := model_timersQuiet worldSemantics rho c (Plan.payload (gprsOf fill2) Generated.armcert_memset_entry 0#88)
    (Plan.timers_disabled _ _ _) (Schedule.setSteps 1)
  have ag1 := makeModelEntry_agrees worldSemantics rho c (Plan.payload (gprsOf fill1) Generated.armcert_memset_entry 0#88)
  have ag2 := makeModelEntry_agrees worldSemantics rho c (Plan.payload (gprsOf fill2) Generated.armcert_memset_entry 0#88)
  have res1 := residual_at rho c fill1 spec sspec hlr' hir' hlay' (fun _ h => h) rws1
  have res2 := residual_at rho c fill2 spec sspec hlr' hir' hlay' (fun _ h => h) rws2
  have st1 : DeploymentObligation "loop:memset:tag-status-rows" _ := ⟨status_rows rho c fill1 1⟩
  have st2 : DeploymentObligation "loop:memset:tag-status-rows" _ := ⟨status_rows rho c fill2 1⟩
  refine ⟨rho, callers, Configuration.ofSource rho c, Configuration.ofSource rho c, _, spec, World.permissionRows,
    World.mapping, Plan.B, dA, fill1, fill2, retA, 1, _, _, ag1, ag2, sspec, sspec, t1, t2, rws1, rws2, res1, res2,
    st1, st2, by decide, ?_⟩
  exact (Route7Root.memsetCT0FromSource real spec World.permissionRows World.mapping Plan.B dA fill1 fill2 retA 1 rho
    callers _ _ _ _ ag1 ag2 sspec sspec t1 t2 rws1 rws2 res1 res2 st1 st2).1

end CT1Witness.Memset
#print axioms CT1Witness.Memset.memset_ct0_witness
