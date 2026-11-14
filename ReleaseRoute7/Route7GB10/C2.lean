-- Route 7 / positive C2 (loops): MemcpyC2 / MemsetC2 / MemmoveC2 at every admissible completion and caller, on
-- the route-7 world (memory.elf code page at 0x400000, s = 0x30000, d = 0x31000, n = 1, returnPC = 0x500000). The
-- entry is makeModelEntry over the world payload; SourceSpec from the world tables; TimersQuiet from disabled timers.
import Route7GB10.Data
import Route7Root.C2Spec
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace Route7GB10
open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.MachineSource ReleaseProfile.GB10
open ArmCertLoop ArmCertLoop.ContractDraft Route7GB10.Closed CertiFFI.Claim

/-- The ten entry-residual atoms at a world entry, for a consumer map over one-byte spans at s / d. -/
theorem residual (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (gprs : Vector (BitVec 64) 31)
    (entry : Nat) (pcount : BitVec 88) {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (sspec : SourceSpec rho caller spec) (hlr : spec.logicalRows = World.logicalRows)
    (hir : spec.imageRows = World.imageRows) (hlay : spec.layout = World.layout)
    (hdom : ∀ q : AccessQuery, (∃ q0 ∈ World.queries, ArmCertWalk.SamePage q0.va q.va) → domain q)
    (ss : List SpanMap.Span) (hss : ∀ span ∈ ss, span.length = 1 ∧ (span.base = sA ∨ span.base = dA))
    (offset : Nat → BitVec 64) (pc : (E rho caller gprs entry pcount).regs._PC = Plan.B + offset 0) :
    Route7Entry.EntryResidual spec World.permissionRows World.mapping
      (SpanMap.consumerMap ss (Image.codeVAs Plan.B Generated.imageStart Generated.imageWords) World.mapping
        (rowsFootprint spec.imageRows).byte) codeScope image Plan.B offset rho caller (E rho caller gprs entry pcount) := by
  have imgs := world_images rho caller gprs entry pcount sspec hir
  refine ⟨⟨imgs.1.covered⟩, ⟨imgs.1.topology⟩, ⟨imgs.1.attributes⟩, ⟨imgs.1.writeback⟩, ⟨imgs.1.permissions⟩, ⟨pc⟩,
    ⟨?_⟩, ⟨Plan.placedAt _ (sat rho caller gprs entry pcount)⟩, ⟨?_⟩, ⟨noUpd rho caller gprs entry pcount sspec hir⟩⟩
  · rw [hir]
    exact closed_spans (worldSpec_of_source sspec (Plan.payload gprs entry pcount).data hlr hir hlay) hdom _
      (worldRegs_before (worldRegs rho caller gprs entry pcount)) ss hss
  · exact imgs.2

def gprsOf (x1 : BitVec 64) : Vector (BitVec 64) 31 := Vector.ofFn fun i =>
  if i.val = 0 then dA else if i.val = 1 then x1 else if i.val = 2 then 1#64 else if i.val = 30 then retA else 0#64

theorem gprs_eq (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (x1 : BitVec 64) (entry : Nat)
    (pcount : BitVec 88) : (E rho caller (gprsOf x1) entry pcount).regs.gpr = gprsOf x1 := rfl

/-- **Positive C2 for route-7 memcpy** at every admissible completion and caller. -/
theorem memcpy_c2 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : Route7Root.MemcpyC2 rho caller := by
  have timers := model_timersQuiet worldSemantics rho caller (Plan.payload (gprsOf sA) Generated.armcert_memcpy_entry 0#88)
    (Plan.timers_disabled _ _ _) (Schedule.copySteps 1)
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho caller tables oracle
    (Plan.payload (gprsOf sA) Generated.armcert_memcpy_entry 0#88).data
    (E rho caller (gprsOf sA) Generated.armcert_memcpy_entry 0#88) rfl
  have hir' : spec.imageRows = World.imageRows := hir
  have hlr' : spec.logicalRows = World.logicalRows := hlr
  have hlay' : spec.layout = World.layout := hl
  have hss : ∀ span ∈ spans dA sA 1 ++ [], span.length = 1 ∧ (span.base = sA ∨ span.base = dA) := by
    intro span hs
    simp only [spans, sourceSpan, destSpan, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp
  refine ⟨_, spec, World.permissionRows, World.mapping, Plan.B, dA, sA, retA, 1,
    E rho caller (gprsOf sA) Generated.armcert_memcpy_entry 0#88,
    makeModelEntry_agrees worldSemantics rho caller _, sspec, timers, ?_, ?_⟩
  · refine ⟨⟨by decide⟩, ⟨by decide⟩, ⟨by decide⟩, ⟨by unfold SpanMap.NoWrap sourceSpan sA; decide⟩,
      ⟨by unfold SpanMap.NoWrap destSpan dA; decide⟩, ⟨by decide⟩,
      ⟨Plan.codeGeometry⟩, ⟨codeWrite⟩,
      ⟨by rw [hir']; exact dataGeom_spans _ (fun span hs => hss span (List.mem_append_left _ hs))⟩,
      ⟨injective_spans _ (fun span hs => hss span (List.mem_append_left _ hs))⟩,
      ⟨by rw [hir']; exact Plan.separatedAt⟩, ⟨?_⟩, ⟨?_⟩, ⟨by rw [hlr']; exact World.keys_nodup⟩⟩
    · simp only [Args, HeapV2StepCerts.RegBind.regVal, gprs_eq]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
    · intro i hi
      have : i = 0 := by omega
      subst this
      exact ⟨Plan.srcByte, src_byte worldSemantics rho caller _ _ 0#88⟩
  · exact residual rho caller (gprsOf sA) Generated.armcert_memcpy_entry 0#88 spec sspec hlr' hir' hlay'
      (fun _ h => h) _ hss _ (by
        show (Plan.B + BitVec.ofNat 64 Generated.armcert_memcpy_entry : BitVec 64) = Plan.B + offset Plan.B retA 1 0
        decide)

def fillA : BitVec 64 := 0x5a#64

/-- **Positive C2 for route-7 memset** at every admissible completion and caller. -/
theorem memset_c2 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : Route7Root.MemsetC2 rho caller := by
  have timers := model_timersQuiet worldSemantics rho caller (Plan.payload (gprsOf fillA) Generated.armcert_memset_entry 0#88)
    (Plan.timers_disabled _ _ _) (Schedule.setSteps 1)
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho caller tables oracle
    (Plan.payload (gprsOf fillA) Generated.armcert_memset_entry 0#88).data
    (E rho caller (gprsOf fillA) Generated.armcert_memset_entry 0#88) rfl
  have hir' : spec.imageRows = World.imageRows := hir
  have hlr' : spec.logicalRows = World.logicalRows := hlr
  have hlay' : spec.layout = World.layout := hl
  have hss : ∀ span ∈ [destSpan dA 1], span.length = 1 ∧ (span.base = sA ∨ span.base = dA) := by
    intro span hs
    simp only [destSpan, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs; simp
  have rws : Route7Root.MemsetRows spec World.mapping Plan.B dA fillA retA 1
      (E rho caller (gprsOf fillA) Generated.armcert_memset_entry 0#88) := by
    refine ⟨⟨by decide⟩, ⟨by decide⟩, ⟨by decide⟩, ⟨by unfold SpanMap.NoWrap destSpan dA; decide⟩,
      ⟨Plan.codeGeometry⟩, ⟨codeWrite⟩, ⟨?_⟩, ⟨injective_spans _ hss⟩,
      ⟨by rw [hir']; exact Plan.separatedAt⟩, ⟨?_⟩, ⟨by rw [hlr']; exact World.keys_nodup⟩⟩
    · intro i hi
      rw [hir']
      exact dataGeom_spans _ hss (destSpan dA 1) (by simp) i hi
    · simp only [gprs_eq]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  refine ⟨_, spec, World.permissionRows, World.mapping, Plan.B, dA, fillA, retA, 1,
    E rho caller (gprsOf fillA) Generated.armcert_memset_entry 0#88,
    makeModelEntry_agrees worldSemantics rho caller _, sspec, timers, rws, ?_⟩
  exact residual rho caller (gprsOf fillA) Generated.armcert_memset_entry 0#88 spec sspec hlr' hir' hlay'
    (fun _ h => h) _ hss _ (by
      show (Plan.B + BitVec.ofNat 64 Generated.armcert_memset_entry : BitVec 64) =
        Plan.B + SetNative.offset (rws.context (sourceAttributes rho caller) World.permissionRows) 0
      simp only [SetNative.offset, Route7Root.MemsetRows.context]
      decide)

/-- **Positive C2 for route-7 memmove** at every admissible completion and caller (public path: backward, s < d). -/
theorem memmove_c2 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : Route7Root.MemmoveC2 rho caller := by
  have timers := model_timersQuiet worldSemantics rho caller (Plan.payload (gprsOf sA) Generated.armcert_memmove_entry 0#88)
    (Plan.timers_disabled _ _ _) (Schedule.moveSteps (Route7Move.movePath dA sA 1) 1)
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho caller tables oracle
    (Plan.payload (gprsOf sA) Generated.armcert_memmove_entry 0#88).data
    (E rho caller (gprsOf sA) Generated.armcert_memmove_entry 0#88) rfl
  have hir' : spec.imageRows = World.imageRows := hir
  have hlr' : spec.logicalRows = World.logicalRows := hlr
  have hlay' : spec.layout = World.layout := hl
  have hss : ∀ span ∈ spans dA sA 1, span.length = 1 ∧ (span.base = sA ∨ span.base = dA) := by
    intro span hs
    simp only [spans, sourceSpan, destSpan, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp
  have rws : Route7Root.MemmoveRows spec World.mapping Plan.B dA sA retA 1
      (E rho caller (gprsOf sA) Generated.armcert_memmove_entry 0#88) := by
    refine ⟨⟨by decide⟩, ⟨by decide⟩, ⟨by decide⟩, ⟨by unfold SpanMap.NoWrap sourceSpan sA; decide⟩,
      ⟨by unfold SpanMap.NoWrap destSpan dA; decide⟩, ⟨Plan.codeGeometry⟩, ⟨codeWrite⟩,
      ⟨by rw [hir']; exact dataGeom_spans _ hss⟩, ⟨injective_spans _ hss⟩,
      ⟨by rw [hir']; exact Plan.separatedAt⟩, ⟨?_⟩, ⟨?_⟩, ⟨by rw [hlr']; exact World.keys_nodup⟩⟩
    · simp only [Args, HeapV2StepCerts.RegBind.regVal, gprs_eq]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
    · intro i hi
      have : i = 0 := by omega
      subst this
      exact ⟨Plan.srcByte, src_byte worldSemantics rho caller _ _ 0#88⟩
  refine ⟨_, spec, World.permissionRows, World.mapping, Plan.B, dA, sA, retA, 1,
    E rho caller (gprsOf sA) Generated.armcert_memmove_entry 0#88,
    makeModelEntry_agrees worldSemantics rho caller _, sspec, timers, rws, ?_⟩
  exact residual rho caller (gprsOf sA) Generated.armcert_memmove_entry 0#88 spec sspec hlr' hir' hlay'
    (fun _ h => h) _ hss _ (by
      rw [Route7Move.offset_zero]
      show (Plan.B + BitVec.ofNat 64 Generated.armcert_memmove_entry : BitVec 64) = Plan.B + 484#64
      decide)

end Route7GB10
#print axioms Route7GB10.residual
#print axioms Route7GB10.memcpy_c2
#print axioms Route7GB10.memset_c2
#print axioms Route7GB10.memmove_c2
