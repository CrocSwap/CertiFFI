import ReleaseProfile.GB10.HeapCT
import ReleaseProfile.GB10.HeapC2World

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-!
# Worked Heap CT positive C2: target and reduction interface

`CTC2 rho callers` is the positive model-feasibility target for the worked Heap CT card at an admissible
completion and an admitted CT caller pair: program data, a source-pinned spec (first caller) and two
source-built model entries, one per caller, satisfying every retained original CT input. No existential
configuration: each entry's registers agree with the canonical source for its own caller.

`ct_c2_reduce` reduces it to the residual at the two source-built entries for every source-pinned spec
carrying the given tables; the timers facts at both entries are discharged from the source
restriction, exactly as `normal_c2_reduce` does for one entry. `ct_c2_of_worlds` instantiates the payload
families with two `HeapWorld`s; program data (rows, mapping, pins, scope, image, base, offsets, budget)
comes from the first world.
-/

namespace ReleaseProfile.GB10.Heap

open ReleaseProfile.MachineSource ReleaseProfile.GB10

#check "CURRENT_DECL GB10.Heap.CTC2"
/-- Positive C2 target for the worked Heap CT card. -/
def CTC2 (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho) : Prop :=
  ∃ (domain : ArmCert.Translate.Model.QueryDomain) (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : ArmCert.Translate.Model.HeapV2E17.Pins) (scope : Nat → Prop) (image : MemReloc.Image)
    (loadBase : MemReloc.Word) (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat)
    (e1 e2 : ArmBridge.Draft.NativeState),
    AgreesAt (Configuration.ofSource rho callers.first) e1.regs ∧
    AgreesAt (Configuration.ofSource rho callers.second) e2.regs ∧
    SourceSpec rho callers.first spec ∧
    CTResidual spec rows mapping pins scope image loadBase base offS budget rho callers e1 e2

#check "CURRENT_DECL GB10.Heap.ct_c2_reduce"
/-- Reduction: it suffices to prove the CT residual at the two source-built entries (first caller,
second caller) for every source-pinned spec carrying the given tables, given the timers facts at
both entries. Each payload family has the given PhysicalCount; the budget is within `timersBudget`. -/
theorem ct_c2_reduce (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
    (sem1 sem2 : ModelSemantics) (payloadOf1 payloadOf2 : BitVec 88 → ModelPayload)
    (sameCount1 : ∀ pcount, (payloadOf1 pcount).data.PhysicalCount = pcount)
    (sameCount2 : ∀ pcount, (payloadOf2 pcount).data.PhysicalCount = pcount)
    {domain : ArmCert.Translate.Model.QueryDomain} (tables : TopologyTables domain) (oracle : OracleChoice)
    (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : ArmCert.Translate.Model.HeapV2E17.Pins) (scope : Nat → Prop) (image : MemReloc.Image)
    (loadBase : MemReloc.Word) (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat)
    (disabled1 : ∀ pcount, TimersDisabled (payloadOf1 pcount).data.timers)
    (disabled2 : ∀ pcount, TimersDisabled (payloadOf2 pcount).data.timers)
    (residual : ∀ (p1 p2 : BitVec 88) (spec : ArmCert.Translate.Model.TopologyImageSpec domain),
      SourceSpec rho callers.first spec →
      spec.layout = tables.layout → spec.logicalRows = tables.logicalRows →
      spec.imageRows = tables.imageRows →
      TimersQuiet (makeModelEntry sem1 rho callers.first (payloadOf1 p1)).regs budget →
      TimersQuiet (makeModelEntry sem2 rho callers.second (payloadOf2 p2)).regs budget →
      CTResidual spec rows mapping pins scope image loadBase base offS budget rho callers
        (makeModelEntry sem1 rho callers.first (payloadOf1 p1))
        (makeModelEntry sem2 rho callers.second (payloadOf2 p2))) :
    CTC2 rho callers := by
  obtain ⟨p1, -⟩ : ∃ _ : BitVec 88, True := ⟨0#88, trivial⟩
  obtain ⟨p2, -⟩ : ∃ _ : BitVec 88, True := ⟨0#88, trivial⟩
  have timers1 := model_timersQuiet sem1 rho callers.first (payloadOf1 p1) (disabled1 p1) budget
  have timers2 := model_timersQuiet sem2 rho callers.second (payloadOf2 p2) (disabled2 p2) budget
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho callers.first tables oracle (payloadOf1 p1).data
    (makeModelEntry sem1 rho callers.first (payloadOf1 p1)) rfl
  exact ⟨domain, spec, rows, mapping, pins, scope, image, loadBase, base, offS, budget,
    makeModelEntry sem1 rho callers.first (payloadOf1 p1),
    makeModelEntry sem2 rho callers.second (payloadOf2 p2),
    makeModelEntry_agrees sem1 rho callers.first (payloadOf1 p1),
    makeModelEntry_agrees sem2 rho callers.second (payloadOf2 p2),
    sspec, residual p1 p2 spec sspec hl hlr hir timers1 timers2⟩

#check "CURRENT_DECL GB10.Heap.ct_c2_of_worlds"
/-- Positive CT C2 from two worlds (one per caller): the remaining obligation is the CT residual at the
two world entries, for every source-pinned spec carrying the given tables. Program data is the first
world's. -/
theorem ct_c2_of_worlds (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
    (sem1 sem2 : ModelSemantics) (w1 w2 : HeapWorld) (disabled1 : TimersDisabled w1.data.timers)
    (disabled2 : TimersDisabled w2.data.timers)
    {domain : ArmCert.Translate.Model.QueryDomain} (tables : TopologyTables domain) (oracle : OracleChoice)
    (residual : ∀ (p1 p2 : BitVec 88) (spec : ArmCert.Translate.Model.TopologyImageSpec domain),
      SourceSpec rho callers.first spec →
      spec.layout = tables.layout → spec.logicalRows = tables.logicalRows →
      spec.imageRows = tables.imageRows →
      TimersQuiet (worldEntry sem1 rho callers.first w1 p1).regs w1.budget →
      TimersQuiet (worldEntry sem2 rho callers.second w2 p2).regs w1.budget →
      CTResidual spec w1.rows w1.mapping w1.pins w1.scope w1.image w1.loadBase w1.base w1.offS w1.budget
        rho callers (worldEntry sem1 rho callers.first w1 p1) (worldEntry sem2 rho callers.second w2 p2)) :
    CTC2 rho callers :=
  ct_c2_reduce rho callers sem1 sem2 (worldPayload w1) (worldPayload w2) (fun _ => rfl) (fun _ => rfl)
    tables oracle w1.rows w1.mapping w1.pins w1.scope w1.image w1.loadBase w1.base w1.offS w1.budget
    (fun _ => disabled1) (fun _ => disabled2) residual

end ReleaseProfile.GB10.Heap

#print axioms ReleaseProfile.GB10.Heap.ct_c2_reduce
#print axioms ReleaseProfile.GB10.Heap.ct_c2_of_worlds
