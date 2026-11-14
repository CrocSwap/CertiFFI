-- CT1 M4: distinct-secret non-vacuity witness for route-7 memcpy CT0.
-- loops' route-7 C2 world with the source byte made a parameter b (planB b: same keys as Route7GB10.Plan.plan, the
-- data entry (0x80600000, b)). Two entries with b = 0x5a and b = 0xa5, identical in every public binder (completion,
-- caller pair, tables, mapping, base, d, s, n, returnPC, registers); every Lean premise of
-- Route7Root.memcpyCT0FromSource is discharged in the world, including tag-status rows (zeroOracle).
import Route7GB10.C2
import Route7Root.CT0
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace CT1Witness.Memcpy
open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.MachineSource ReleaseProfile.GB10
open ArmCertLoop ArmCertLoop.ContractDraft Route7GB10 Route7GB10.Closed CertiFFI.Claim ArmBridge.CruxGenGuarded

def b1 : BitVec 8 := 0x5a#8
def b2 : BitVec 8 := 0xa5#8

def dataPlanB (b : BitVec 8) : NativeSourceInit.Plan := [(0x80600000, b), (0x80601000, 0#8)]
def planB (b : BitVec 8) : NativeSourceInit.Plan := Plan.codePlan ++ Plan.tableRows ++ dataPlanB b

theorem planB_keys_eq (b : BitVec 8) : (planB b).map (·.1) = Plan.plan.map (·.1) := by
  simp [planB, Plan.plan, dataPlanB, Plan.dataPlan]

theorem planB_keys (b : BitVec 8) : (planB b).Pairwise (fun a c => (a.1 == c.1) = false) := by
  have nd : ((planB b).map (·.1)).Nodup := by rw [planB_keys_eq]; exact Plan.plan_nodup
  have h := List.pairwise_map.1 (List.nodup_iff_pairwise_ne.1 nd)
  exact h.imp fun {a c} ne => by simpa [beq_eq_false_iff_ne] using ne

def payloadB (gprs : Vector (BitVec 64) 31) (entry : Nat) (pcount : BitVec 88) (b : BitVec 8) : ModelPayload :=
  ⟨{ Plan.entryData gprs entry with PhysicalCount := pcount }, Std.ExtHashMap.ofList (planB b)⟩

noncomputable abbrev EB (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (gprs : Vector (BitVec 64) 31)
    (entry : Nat) (pcount : BitVec 88) (b : BitVec 8) : ArmBridge.Draft.NativeState :=
  makeModelEntry worldSemantics rho caller (payloadB gprs entry pcount b)

section
variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (gprs : Vector (BitVec 64) 31)
  (entry : Nat) (pcount : BitVec 88) (b : BitVec 8)

theorem regs_eq : (EB rho caller gprs entry pcount b).regs = (E rho caller gprs entry pcount).regs := rfl

theorem satB : NativeSourceInit.Satisfies (planB b) (EB rho caller gprs entry pcount b).mem :=
  fun ⟨_, _⟩ mem => Std.ExtHashMap.getElem?_ofList_of_mem (BEq.refl _) (planB_keys b) mem

/-- Every non-source-byte entry of loops' plan is in planB b. -/
theorem mem_planB {x : Nat × BitVec 8} (h : x ∈ Plan.plan) (ne : x.1 ≠ 0x80600000) : x ∈ planB b := by
  simp only [Plan.plan, planB, dataPlanB, Plan.dataPlan, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at h ⊢
  rcases h with (h | h) | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact absurd (by rw [h]) ne
  · exact Or.inr (Or.inr h)

theorem placedB : MemReloc.ImageOn ContractDraft.codeScope ContractDraft.image (EB rho caller gprs entry pcount b)
    Plan.B World.mapping := by
  intro off h
  have ok := Plan.code_at off h
  simp only [Plan.codeByteOK, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at ok
  obtain ⟨⟨⟨⟨⟨⟨some_, map⟩, mem⟩, _⟩, _⟩, _⟩, _⟩ := ok
  obtain ⟨byte, hb⟩ := Option.isSome_iff_exists.1 some_
  refine ⟨byte, Plan.codePA + off, hb, map, ?_⟩
  have hl : Generated.imageWords.length = 43 := by decide
  have small : off < 0x500000 := by unfold ContractDraft.codeScope at h; rw [hl] at h; unfold Generated.imageStart at h; omega
  have := satB rho caller gprs entry pcount b _ (mem_planB b mem (by unfold Plan.codePA; omega))
  simpa [hb] using this

theorem srcB : readByte World.mapping (EB rho caller gprs entry pcount b) (sA + BitVec.ofNat 64 0) = some b := by
  have hm := satB rho caller gprs entry pcount b (0x80600000, b) (by simp [planB, dataPlanB])
  simp only [readByte, map_s, Option.bind_some]
  exact hm

theorem world_imagesB {domain : QueryDomain} {spec : TopologyImageSpec domain}
    (sspec : SourceSpec rho caller spec) (hir : spec.imageRows = World.imageRows) :
    CurrentImagesAt spec (sourceAttributes rho caller) World.permissionRows
        (ArmBridge.CruxGenGuarded.beforeFetchState (EB rho caller gprs entry pcount b)) ∧
      ArmCertWalk.RawImageAt spec.imageRows (ArmBridge.CruxGenGuarded.beforeFetchState (EB rho caller gprs entry pcount b)).mem := by
  obtain ⟨ha, hd, pie, -, -, -, -, -, -, cpie, -⟩ :=
    sourceSpec_walkLiterals rho caller sspec (Plan.payload gprs entry pcount).data
  have wxn := wxn_lit rho caller sspec (Plan.payload gprs entry pcount).data
  have cha := controls_ha_lit rho caller sspec (Plan.payload gprs entry pcount).data
  have chd := controls_hd_lit rho caller sspec (Plan.payload gprs entry pcount).data
  have cov := (sspec.overlay (Plan.payload gprs entry pcount).data).trans (overlay_source rho caller _)
  have nv1 := nv1Mode_el20 spec.controls sspec.regime
  refine images_of_checks spec (sourceAttributes rho caller) World.permissionRows _
    (plan := planB b) (satB rho caller gprs entry pcount b) ?_ ?_ ?_ ?_ ?_ ?_ _
    (off_before rho caller gprs entry pcount) (off_before rho caller gprs entry pcount) ?_
  · intro x hx
    rw [hir] at hx
    exact List.mem_append_left _ (List.mem_append_right _ hx)
  · rw [hir]; unfold PermissionRowsDeclared; decide
  · rw [hir]; decide
  · rw [hir, pie, ha, hd]; decide
  · rw [hir]; exact checkAttr_world rho caller
  · rw [hir]; exact checkWB_world rho caller
  · rw [checkPermissionImagePure_noOverlay _ _ _ _ (off_before rho caller gprs entry pcount)]
    simp only [checkPermissionImageNoOverlay, permissionParamsView, ha, hd, pie, wxn,
      ArmCertWalk.descriptorPermissionView, S1LogicalReference.leafPermissions,
      S1LogicalReference.classicPermissions, nv1, cpie, cha, chd, cov, Bool.false_eq_true, ↓reduceIte]
    decide

theorem residualB {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (sspec : SourceSpec rho caller spec) (hlr : spec.logicalRows = World.logicalRows)
    (hir : spec.imageRows = World.imageRows) (hlay : spec.layout = World.layout)
    (hdom : ∀ q : AccessQuery, (∃ q0 ∈ World.queries, ArmCertWalk.SamePage q0.va q.va) → domain q)
    (ss : List SpanMap.Span) (hss : ∀ span ∈ ss, span.length = 1 ∧ (span.base = sA ∨ span.base = dA))
    (offset : Nat → BitVec 64) (pc : (EB rho caller gprs entry pcount b).regs._PC = Plan.B + offset 0) :
    Route7Entry.EntryResidual spec World.permissionRows World.mapping
      (SpanMap.consumerMap ss (Image.codeVAs Plan.B Generated.imageStart Generated.imageWords) World.mapping
        (rowsFootprint spec.imageRows).byte) codeScope image Plan.B offset rho caller (EB rho caller gprs entry pcount b) := by
  have imgs := world_imagesB rho caller gprs entry pcount b sspec hir
  refine ⟨⟨imgs.1.covered⟩, ⟨imgs.1.topology⟩, ⟨imgs.1.attributes⟩, ⟨imgs.1.writeback⟩, ⟨imgs.1.permissions⟩, ⟨pc⟩,
    ⟨?_⟩, ⟨placedB rho caller gprs entry pcount b⟩, ⟨?_⟩, ⟨noUpd rho caller gprs entry pcount sspec hir⟩⟩
  · rw [hir]
    exact closed_spans (worldSpec_of_source sspec (Plan.payload gprs entry pcount).data hlr hir hlay) hdom _
      (worldRegs_before (worldRegs rho caller gprs entry pcount)) ss hss
  · exact imgs.2

theorem status_rowsB (n : Nat) :
    NativeMteTagCheck.TagStatusRows (EB rho caller gprs entry pcount b)
      ((EB rho caller gprs entry pcount b).choiceOcc.getD 1354 0) n := by
  intro i _
  rfl
end

theorem hss : ∀ span ∈ spans dA sA 1, span.length = 1 ∧ (span.base = sA ∨ span.base = dA) := by
  intro span hs
  simp only [spans, sourceSpan, destSpan, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> simp

theorem rowsB (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (b : BitVec 8)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (hir : spec.imageRows = World.imageRows) (hlr : spec.logicalRows = World.logicalRows) :
    Route7Root.MemcpyRows spec World.mapping Plan.B dA sA retA 1
      (EB rho caller (gprsOf sA) Generated.armcert_memcpy_entry 0#88 b) := by
  refine ⟨⟨by decide⟩, ⟨by decide⟩, ⟨by decide⟩, ⟨by unfold SpanMap.NoWrap sourceSpan sA; decide⟩,
    ⟨by unfold SpanMap.NoWrap destSpan dA; decide⟩, ⟨by decide⟩,
    ⟨Plan.codeGeometry⟩, ⟨codeWrite⟩,
    ⟨by rw [hir]; exact dataGeom_spans _ (fun span hs => hss span (List.mem_append_left _ hs))⟩,
    ⟨injective_spans _ (fun span hs => hss span (List.mem_append_left _ hs))⟩,
    ⟨by rw [hir]; exact Plan.separatedAt⟩, ⟨?_⟩, ⟨?_⟩, ⟨by rw [hlr]; exact World.keys_nodup⟩⟩
  · simp only [Args, HeapV2StepCerts.RegBind.regVal, regs_eq, gprs_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  · intro i hi
    have : i = 0 := by omega
    subst this
    exact ⟨b, srcB rho caller _ _ 0#88 b⟩

/-- **memcpy CT0 distinct-secret witness.** Two entries that agree on every public binder and satisfy EVERY Lean
    premise of `Route7Root.memcpyCT0FromSource`, whose source byte (the secret) differs (decided: 0x5a ≠ 0xa5), and for
    which the CT0 conclusion holds. -/
theorem memcpy_ct0_witness (real : Type) [Sail.SailReal real] :
    ∃ (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
      (cfg1 : Configuration rho callers.first) (cfg2 : Configuration rho callers.second)
      (domain : QueryDomain) (spec : TopologyImageSpec domain) (rows : List PermissionRow)
      (mapping : BitVec 64 → Option Nat) (base d s returnPC : BitVec 64) (n : Nat) (e1 e2 : ArmBridge.Draft.NativeState)
      (ag1 : AgreesAt cfg1 e1.regs) (ag2 : AgreesAt cfg2 e2.regs)
      (sspec1 : SourceSpec rho callers.first spec) (sspec2 : SourceSpec rho callers.second spec)
      (timers1 : TimersQuiet e1.regs (Schedule.copySteps n)) (timers2 : TimersQuiet e2.regs (Schedule.copySteps n))
      (rws1 : Route7Root.MemcpyRows spec mapping base d s returnPC n e1)
      (rws2 : Route7Root.MemcpyRows spec mapping base d s returnPC n e2)
      (res1 : Route7Entry.EntryResidual spec rows mapping (Route7Root.memcpyConsumer spec mapping base d s n) codeScope
        image base (offset base returnPC n) rho callers.first e1)
      (res2 : Route7Entry.EntryResidual spec rows mapping (Route7Root.memcpyConsumer spec mapping base d s n) codeScope
        image base (offset base returnPC n) rho callers.second e2)
      (statusRows1 : DeploymentObligation "loop:memcpy:tag-status-rows"
        (NativeMteTagCheck.TagStatusRows e1 (e1.choiceOcc.getD 1354 0) (2 * n)))
      (statusRows2 : DeploymentObligation "loop:memcpy:tag-status-rows"
        (NativeMteTagCheck.TagStatusRows e2 (e2.choiceOcc.getD 1354 0) (2 * n))),
      e1.regs = e2.regs ∧
      readByte mapping e1 (s + BitVec.ofNat 64 0) = some b1 ∧ readByte mapping e2 (s + BitVec.ofNat 64 0) = some b2 ∧
      b1 ≠ b2 ∧
      PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.copySteps n))
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.copySteps n)) := by
  obtain ⟨⟨rho⟩, callerOf, -, -⟩ := sourceDomainWitness
  obtain ⟨c⟩ := callerOf rho
  let callers : AdmissibleCTCallers rho := AdmissibleCTCallers.ofCallers c c
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho c tables oracle
    (Plan.payload (gprsOf sA) Generated.armcert_memcpy_entry 0#88).data
    (E rho c (gprsOf sA) Generated.armcert_memcpy_entry 0#88) rfl
  have hir' : spec.imageRows = World.imageRows := hir
  have hlr' : spec.logicalRows = World.logicalRows := hlr
  have hlay' : spec.layout = World.layout := hl
  have t := model_timersQuiet worldSemantics rho c (Plan.payload (gprsOf sA) Generated.armcert_memcpy_entry 0#88)
    (Plan.timers_disabled _ _ _) (Schedule.copySteps 1)
  have ag := makeModelEntry_agrees worldSemantics rho c (Plan.payload (gprsOf sA) Generated.armcert_memcpy_entry 0#88)
  have pc : ∀ b, (EB rho c (gprsOf sA) Generated.armcert_memcpy_entry 0#88 b).regs._PC =
      Plan.B + offset Plan.B retA 1 0 := fun b => by
    show (Plan.B + BitVec.ofNat 64 Generated.armcert_memcpy_entry : BitVec 64) = Plan.B + offset Plan.B retA 1 0
    decide
  have res : ∀ b, Route7Entry.EntryResidual spec World.permissionRows World.mapping
      (Route7Root.memcpyConsumer spec World.mapping Plan.B dA sA 1) codeScope image Plan.B (offset Plan.B retA 1) rho c
      (EB rho c (gprsOf sA) Generated.armcert_memcpy_entry 0#88 b) := fun b =>
    residualB rho c (gprsOf sA) Generated.armcert_memcpy_entry 0#88 b spec sspec hlr' hir' hlay' (fun _ h => h)
      _ (fun span hs => hss span (List.mem_append_left _ hs)) _ (pc b)
  have st : ∀ b, DeploymentObligation "loop:memcpy:tag-status-rows" (NativeMteTagCheck.TagStatusRows
      (EB rho c (gprsOf sA) Generated.armcert_memcpy_entry 0#88 b)
      ((EB rho c (gprsOf sA) Generated.armcert_memcpy_entry 0#88 b).choiceOcc.getD 1354 0) (2 * 1)) := fun b =>
    ⟨status_rowsB rho c _ _ _ b _⟩
  have rws1 := rowsB rho c b1 spec hir' hlr'
  have rws2 := rowsB rho c b2 spec hir' hlr'
  refine ⟨rho, callers, Configuration.ofSource rho c, Configuration.ofSource rho c, _, spec, World.permissionRows,
    World.mapping, Plan.B, dA, sA, retA, 1, EB rho c (gprsOf sA) Generated.armcert_memcpy_entry 0#88 b1,
    EB rho c (gprsOf sA) Generated.armcert_memcpy_entry 0#88 b2, ag, ag, sspec, sspec, t, t, rws1, rws2,
    res b1, res b2, st b1, st b2, rfl, srcB rho c _ _ 0#88 b1, srcB rho c _ _ 0#88 b2, by decide, ?_⟩
  exact (Route7Root.memcpyCT0FromSource real spec World.permissionRows World.mapping Plan.B dA sA retA 1 rho callers
    (Configuration.ofSource rho c) (Configuration.ofSource rho c)
    (EB rho c (gprsOf sA) Generated.armcert_memcpy_entry 0#88 b1) (EB rho c (gprsOf sA) Generated.armcert_memcpy_entry 0#88 b2)
    ag ag sspec sspec t t rws1 rws2 (res b1) (res b2) (st b1) (st b2)).1

end CT1Witness.Memcpy
#print axioms CT1Witness.Memcpy.memcpy_ct0_witness
