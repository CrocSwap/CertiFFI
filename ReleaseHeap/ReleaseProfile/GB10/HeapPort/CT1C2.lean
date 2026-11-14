import ReleaseProfile.GB10.HeapPort.CT1
import ReleaseProfile.GB10.HeapC2World

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-! Heap CT1 positive C2 target and reduction (generated; mirrors normal_c2_reduce). No existential
configuration: entry registers agree with the canonical source; the spec is source-pinned. -/

namespace ReleaseProfile.GB10.Heap

open ReleaseProfile.MachineSource ReleaseProfile.GB10

#check "CURRENT_DECL GB10.Heap.CT1C2"
def CT1C2 (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho) : Prop :=
  ∃ (domain : ArmCert.Translate.Model.QueryDomain) (spec : ArmCert.Translate.Model.TopologyImageSpec domain) (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : ArmCert.Translate.Model.HeapV2E17.Pins) (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word) (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (tableRows1 : NativeSourceInit.Plan) (tableRows2 : NativeSourceInit.Plan) (e1 e2 : ArmBridge.Draft.NativeState),
    AgreesAt (Configuration.ofSource rho callers.first) e1.regs ∧
    AgreesAt (Configuration.ofSource rho callers.second) e2.regs ∧ SourceSpec rho callers.first spec ∧
    CT1Residual spec rows mapping pins scope image loadBase base offS budget tableRows1 tableRows2 rho callers e1 e2

#check "CURRENT_DECL GB10.Heap.ct1_c2_reduce"
theorem ct1_c2_reduce (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
    (sem1 sem2 : ModelSemantics) (payloadOf1 payloadOf2 : BitVec 88 → ModelPayload)
    (sameCount1 : ∀ pcount, (payloadOf1 pcount).data.PhysicalCount = pcount)
    (sameCount2 : ∀ pcount, (payloadOf2 pcount).data.PhysicalCount = pcount)
    {domain : ArmCert.Translate.Model.QueryDomain} (tables : TopologyTables domain) (oracle : OracleChoice)
    (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : ArmCert.Translate.Model.HeapV2E17.Pins) (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word) (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (tableRows1 : NativeSourceInit.Plan) (tableRows2 : NativeSourceInit.Plan) (disabled1 : ∀ pcount, TimersDisabled (payloadOf1 pcount).data.timers)
    (disabled2 : ∀ pcount, TimersDisabled (payloadOf2 pcount).data.timers)
    (residual : ∀ (p1 p2 : BitVec 88) (spec : ArmCert.Translate.Model.TopologyImageSpec domain),
      SourceSpec rho callers.first spec →
      spec.layout = tables.layout → spec.logicalRows = tables.logicalRows →
      spec.imageRows = tables.imageRows →
      TimersQuiet (makeModelEntry sem1 rho callers.first (payloadOf1 p1)).regs budget →
      TimersQuiet (makeModelEntry sem2 rho callers.second (payloadOf2 p2)).regs budget →
      CT1Residual spec rows mapping pins scope image loadBase base offS budget tableRows1 tableRows2 rho callers
        (makeModelEntry sem1 rho callers.first (payloadOf1 p1))
        (makeModelEntry sem2 rho callers.second (payloadOf2 p2))) :
    CT1C2 rho callers := by
  obtain ⟨p1, -⟩ : ∃ _ : BitVec 88, True := ⟨0#88, trivial⟩
  obtain ⟨p2, -⟩ : ∃ _ : BitVec 88, True := ⟨0#88, trivial⟩
  have timers1 := model_timersQuiet sem1 rho callers.first (payloadOf1 p1) (disabled1 p1) budget
  have timers2 := model_timersQuiet sem2 rho callers.second (payloadOf2 p2) (disabled2 p2) budget
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho callers.first tables oracle (payloadOf1 p1).data
    (makeModelEntry sem1 rho callers.first (payloadOf1 p1)) rfl
  exact ⟨domain, spec, rows, mapping, pins, scope, image, loadBase, base, offS, budget, tableRows1, tableRows2,
    makeModelEntry sem1 rho callers.first (payloadOf1 p1), makeModelEntry sem2 rho callers.second (payloadOf2 p2),
    makeModelEntry_agrees sem1 rho callers.first (payloadOf1 p1),
    makeModelEntry_agrees sem2 rho callers.second (payloadOf2 p2),
    sspec, residual p1 p2 spec sspec hl hlr hir timers1 timers2⟩

end ReleaseProfile.GB10.Heap

#print axioms ReleaseProfile.GB10.Heap.ct1_c2_reduce
