-- CT1 M4: route-7 memmove distinct-secret witness (source byte 0x5a vs 0xa5; public path backward, s < d).
import CT1Witness.Memcpy
import Route7Root.CT0Move
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace CT1Witness.Memmove
open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.MachineSource ReleaseProfile.GB10
open ArmCertLoop ArmCertLoop.ContractDraft Route7GB10 Route7GB10.Closed CertiFFI.Claim ArmBridge.CruxGenGuarded
open CT1Witness.Memcpy

theorem rowsM (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (b : BitVec 8)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (hir : spec.imageRows = World.imageRows) (hlr : spec.logicalRows = World.logicalRows) :
    Route7Root.MemmoveRows spec World.mapping Plan.B dA sA retA 1
      (EB rho caller (gprsOf sA) Generated.armcert_memmove_entry 0#88 b) := by
  refine ⟨⟨by decide⟩, ⟨by decide⟩, ⟨by decide⟩, ⟨by unfold SpanMap.NoWrap sourceSpan sA; decide⟩,
    ⟨by unfold SpanMap.NoWrap destSpan dA; decide⟩, ⟨Plan.codeGeometry⟩, ⟨codeWrite⟩,
    ⟨by rw [hir]; exact dataGeom_spans _ hss⟩, ⟨injective_spans _ hss⟩,
    ⟨by rw [hir]; exact Plan.separatedAt⟩, ⟨?_⟩, ⟨?_⟩, ⟨by rw [hlr]; exact World.keys_nodup⟩⟩
  · simp only [Args, HeapV2StepCerts.RegBind.regVal, regs_eq, gprs_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  · intro i hi
    have : i = 0 := by omega
    subst this
    exact ⟨b, srcB rho caller _ _ 0#88 b⟩

/-- **memmove CT0 distinct-secret witness** (as memcpy_ct0_witness, for Route7Root.memmoveCT0FromSource). -/
theorem memmove_ct0_witness (real : Type) [Sail.SailReal real] :
    ∃ (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
      (cfg1 : Configuration rho callers.first) (cfg2 : Configuration rho callers.second)
      (domain : QueryDomain) (spec : TopologyImageSpec domain) (rows : List PermissionRow)
      (mapping : BitVec 64 → Option Nat) (base d s returnPC : BitVec 64) (n : Nat) (e1 e2 : ArmBridge.Draft.NativeState)
      (ag1 : AgreesAt cfg1 e1.regs) (ag2 : AgreesAt cfg2 e2.regs)
      (sspec1 : SourceSpec rho callers.first spec) (sspec2 : SourceSpec rho callers.second spec)
      (timers1 : TimersQuiet e1.regs (Schedule.moveSteps (Route7Move.movePath d s n) n))
      (timers2 : TimersQuiet e2.regs (Schedule.moveSteps (Route7Move.movePath d s n) n))
      (rws1 : Route7Root.MemmoveRows spec mapping base d s returnPC n e1)
      (rws2 : Route7Root.MemmoveRows spec mapping base d s returnPC n e2)
      (res1 : Route7Entry.EntryResidual spec rows mapping (Route7Root.memmoveConsumer spec mapping base d s n) codeScope
        image base (Route7Move.offset (rws1.context (sourceAttributes rho callers.first) rows)) rho callers.first e1)
      (res2 : Route7Entry.EntryResidual spec rows mapping (Route7Root.memmoveConsumer spec mapping base d s n) codeScope
        image base (Route7Move.offset (rws2.context (sourceAttributes rho callers.second) rows)) rho callers.second e2)
      (statusRows1 : DeploymentObligation "loop:memmove:tag-status-rows"
        (NativeMteTagCheck.TagStatusRows e1 (e1.choiceOcc.getD 1354 0) (2 * n)))
      (statusRows2 : DeploymentObligation "loop:memmove:tag-status-rows"
        (NativeMteTagCheck.TagStatusRows e2 (e2.choiceOcc.getD 1354 0) (2 * n))),
      e1.regs = e2.regs ∧
      readByte mapping e1 (s + BitVec.ofNat 64 0) = some b1 ∧ readByte mapping e2 (s + BitVec.ofNat 64 0) = some b2 ∧
      b1 ≠ b2 ∧
      PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.moveSteps (Route7Move.movePath d s n) n))
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.moveSteps (Route7Move.movePath d s n) n)) := by
  obtain ⟨⟨rho⟩, callerOf, -, -⟩ := sourceDomainWitness
  obtain ⟨c⟩ := callerOf rho
  let callers : AdmissibleCTCallers rho := AdmissibleCTCallers.ofCallers c c
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho c tables oracle
    (Plan.payload (gprsOf sA) Generated.armcert_memmove_entry 0#88).data
    (E rho c (gprsOf sA) Generated.armcert_memmove_entry 0#88) rfl
  have hir' : spec.imageRows = World.imageRows := hir
  have hlr' : spec.logicalRows = World.logicalRows := hlr
  have hlay' : spec.layout = World.layout := hl
  have t := model_timersQuiet worldSemantics rho c (Plan.payload (gprsOf sA) Generated.armcert_memmove_entry 0#88)
    (Plan.timers_disabled _ _ _) (Schedule.moveSteps (Route7Move.movePath dA sA 1) 1)
  have ag := makeModelEntry_agrees worldSemantics rho c (Plan.payload (gprsOf sA) Generated.armcert_memmove_entry 0#88)
  have rws1 := rowsM rho c b1 spec hir' hlr'
  have rws2 := rowsM rho c b2 spec hir' hlr'
  have res : ∀ b (rws : Route7Root.MemmoveRows spec World.mapping Plan.B dA sA retA 1
      (EB rho c (gprsOf sA) Generated.armcert_memmove_entry 0#88 b)),
      Route7Entry.EntryResidual spec World.permissionRows World.mapping
        (Route7Root.memmoveConsumer spec World.mapping Plan.B dA sA 1) codeScope image Plan.B
        (Route7Move.offset (rws.context (sourceAttributes rho c) World.permissionRows)) rho c
        (EB rho c (gprsOf sA) Generated.armcert_memmove_entry 0#88 b) := fun b rws =>
    residualB rho c (gprsOf sA) Generated.armcert_memmove_entry 0#88 b spec sspec hlr' hir' hlay' (fun _ h => h)
      _ hss _ (by
        rw [Route7Move.offset_zero]
        show (Plan.B + BitVec.ofNat 64 Generated.armcert_memmove_entry : BitVec 64) = Plan.B + 484#64
        decide)
  have st : ∀ b, DeploymentObligation "loop:memmove:tag-status-rows" (NativeMteTagCheck.TagStatusRows
      (EB rho c (gprsOf sA) Generated.armcert_memmove_entry 0#88 b)
      ((EB rho c (gprsOf sA) Generated.armcert_memmove_entry 0#88 b).choiceOcc.getD 1354 0) (2 * 1)) := fun b =>
    ⟨status_rowsB rho c _ _ _ b _⟩
  refine ⟨rho, callers, Configuration.ofSource rho c, Configuration.ofSource rho c, _, spec, World.permissionRows,
    World.mapping, Plan.B, dA, sA, retA, 1, EB rho c (gprsOf sA) Generated.armcert_memmove_entry 0#88 b1,
    EB rho c (gprsOf sA) Generated.armcert_memmove_entry 0#88 b2, ag, ag, sspec, sspec, t, t, rws1, rws2,
    res b1 rws1, res b2 rws2, st b1, st b2, rfl, srcB rho c _ _ 0#88 b1, srcB rho c _ _ 0#88 b2, by decide, ?_⟩
  exact (Route7Root.memmoveCT0FromSource real spec World.permissionRows World.mapping Plan.B dA sA retA 1 rho callers
    (Configuration.ofSource rho c) (Configuration.ofSource rho c)
    (EB rho c (gprsOf sA) Generated.armcert_memmove_entry 0#88 b1) (EB rho c (gprsOf sA) Generated.armcert_memmove_entry 0#88 b2)
    ag ag sspec sspec t t rws1 rws2 (res b1 rws1) (res b2 rws2) (st b1) (st b2)).1

end CT1Witness.Memmove
#print axioms CT1Witness.Memmove.memmove_ct0_witness
