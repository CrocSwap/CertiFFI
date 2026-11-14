-- CT1 M4: route-7 memset CT1 witness. As CT1Witness.Memset, with a caller whose PSTATE.DIT = 1, so the CT1 root's
-- caller-DIT premises (card:ct1-caller-dit) are discharged too, and the CT1 conclusion (CT0 ∧ P1 both runs ∧ ...)
-- holds for a distinct-secret pair.
import CT1Witness.Memset
import CT1Route7.Memset
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace CT1Witness.MemsetDit
open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.MachineSource ReleaseProfile.GB10
open ArmCertLoop ArmCertLoop.ContractDraft Route7GB10 Route7GB10.Closed CertiFFI.Claim ArmBridge.CruxGenGuarded
open CT1Witness.Memset

/-- The DIT-setting witness caller, DERIVED from a canonical admissible caller (ruling;: no synthetic
    configuration factory): the given caller with only its entry PSTATE.DIT changed to 1. Normality is inherited from `c`
    (DIT is not a NormalCallerDomain field). -/
def ditCallerOf {rho : AdmissibleSourceCompletion} (c : AdmissibleCaller rho) : AdmissibleCaller rho :=
  ⟨{ c.caller with pstate := { c.caller.pstate with DIT := 1#1 } },
    ⟨c.normal.el, c.normal.nrw, c.normal.alignment, c.normal.irq, c.normal.fiq, c.normal.illegal, c.normal.singleStep,
      c.normal.branchType, c.normal.tagCheckOverride⟩⟩

/-- **memset CT1 distinct-secret witness** (check_witness form): an ∃ over EVERY binder of
    `Route7Root.memsetCT1FromSource` (the 29 CT0 binders + dit1 / dit2), each premise proved in the world, with the
    secret fills different (decided), and the CT1 conclusion's CT0 ∧ P1 parts for this pair. -/
theorem memset_ct1_witness (real : Type) [Sail.SailReal real] :
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
        (NativeMteTagCheck.TagStatusRows e2 (e2.choiceOcc.getD 1354 0) n))
      (dit1 : CallerContract "card:ct1-caller-dit" (e1.regs.PSTATE.DIT = 1#1))
      (dit2 : CallerContract "card:ct1-caller-dit" (e2.regs.PSTATE.DIT = 1#1)),
      f1 ≠ f2 ∧
      PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.setSteps n))
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.setSteps n)) ∧
      (∀ j, j ≤ Schedule.setSteps n → (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).regs.PSTATE.DIT = 1#1) ∧
      (∀ j, j ≤ Schedule.setSteps n → (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).regs.PSTATE.DIT = 1#1) := by
  obtain ⟨⟨rho⟩, callerOf, -, -⟩ := sourceDomainWitness
  obtain ⟨c0⟩ := callerOf rho
  let c : AdmissibleCaller rho := ditCallerOf c0
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
  have d1 : CallerContract "card:ct1-caller-dit"
      ((E rho c (gprsOf fill1) Generated.armcert_memset_entry 0#88).regs.PSTATE.DIT = 1#1) := ⟨rfl⟩
  have d2 : CallerContract "card:ct1-caller-dit"
      ((E rho c (gprsOf fill2) Generated.armcert_memset_entry 0#88).regs.PSTATE.DIT = 1#1) := ⟨rfl⟩
  obtain ⟨ct0, p1, p2, -⟩ := Route7Root.memsetCT1FromSource real spec World.permissionRows World.mapping Plan.B dA fill1
    fill2 retA 1 rho callers _ _ _ _ ag1 ag2 sspec sspec t1 t2 rws1 rws2 res1 res2 st1 st2 d1 d2
  exact ⟨rho, callers, Configuration.ofSource rho c, Configuration.ofSource rho c, _, spec, World.permissionRows,
    World.mapping, Plan.B, dA, fill1, fill2, retA, 1, _, _, ag1, ag2, sspec, sspec, t1, t2, rws1, rws2, res1, res2,
    st1, st2, d1, d2, by decide, ct0.1, p1, p2⟩

end CT1Witness.MemsetDit
#print axioms CT1Witness.MemsetDit.memset_ct1_witness
