import ReleaseProfile.GB10.HeapPort.Initial4
import ReleaseProfile.GB10.HeapC2World

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-! Heap Initial4 positive C2 target and reduction (generated; mirrors normal_c2_reduce). No existential
configuration: entry registers agree with the canonical source; the spec is source-pinned. -/

namespace ReleaseProfile.GB10.Heap

open ReleaseProfile.MachineSource ReleaseProfile.GB10

#check "CURRENT_DECL GB10.Heap.Initial4C2"
def Initial4C2 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : Prop :=
  ∃ (domain : ArmCert.Translate.Model.QueryDomain) (spec : ArmCert.Translate.Model.TopologyImageSpec domain) (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : ArmCert.Translate.Model.HeapV2E17.Pins) (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word) (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (tableRows : NativeSourceInit.Plan) (e : ArmBridge.Draft.NativeState),
    AgreesAt (Configuration.ofSource rho caller) e.regs ∧ SourceSpec rho caller spec ∧
    Initial4Residual spec rows mapping pins scope image loadBase base offS budget tableRows rho caller e

#check "CURRENT_DECL GB10.Heap.initial4_c2_reduce"
theorem initial4_c2_reduce (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (sem : ModelSemantics) (payloadOf : BitVec 88 → ModelPayload)
    (sameCount : ∀ pcount, (payloadOf pcount).data.PhysicalCount = pcount)
    {domain : ArmCert.Translate.Model.QueryDomain} (tables : TopologyTables domain) (oracle : OracleChoice)
    (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : ArmCert.Translate.Model.HeapV2E17.Pins) (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word) (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (tableRows : NativeSourceInit.Plan) (disabled : ∀ pcount, TimersDisabled (payloadOf pcount).data.timers)
    (residual : ∀ (pcount : BitVec 88) (spec : ArmCert.Translate.Model.TopologyImageSpec domain),
      SourceSpec rho caller spec →
      spec.layout = tables.layout → spec.logicalRows = tables.logicalRows →
      spec.imageRows = tables.imageRows →
      TimersQuiet (makeModelEntry sem rho caller (payloadOf pcount)).regs budget →
      Initial4Residual spec rows mapping pins scope image loadBase base offS budget tableRows rho caller (makeModelEntry sem rho caller (payloadOf pcount))) :
    Initial4C2 rho caller := by
  obtain ⟨pcount, -⟩ : ∃ _ : BitVec 88, True := ⟨0#88, trivial⟩
  have timers := model_timersQuiet sem rho caller (payloadOf pcount) (disabled pcount) budget
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho caller tables oracle (payloadOf pcount).data
    (makeModelEntry sem rho caller (payloadOf pcount)) rfl
  exact ⟨domain, spec, rows, mapping, pins, scope, image, loadBase, base, offS, budget, tableRows,
    makeModelEntry sem rho caller (payloadOf pcount), makeModelEntry_agrees sem rho caller (payloadOf pcount),
    sspec, residual pcount spec sspec hl hlr hir timers⟩

end ReleaseProfile.GB10.Heap

#print axioms ReleaseProfile.GB10.Heap.initial4_c2_reduce
