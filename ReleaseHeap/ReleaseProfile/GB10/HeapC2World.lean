import ReleaseProfile.GB10.HeapNormal
import ReleaseProfile.GB10.ModelEntry
import ReleaseProfile.GB10.WorldSemantics
import ReleaseProfile.GB10.SpecWitness

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-!
# Worked Heap normal positive C2: target and reduction interface

`NormalC2 rho caller` is the positive model-feasibility target at an admissible completion and caller:
program data, a source-pinned spec and a source-built model entry satisfying every retained original
input. `normal_c2_reduce` reduces it to the residual for ANY spec that is source-pinned and carries the
base spec's tables, at the source-built model entry. Concrete world data is bound in a later module.
-/

namespace ReleaseProfile.GB10.Heap

open ReleaseProfile.MachineSource ReleaseProfile.GB10

#check "CURRENT_DECL GB10.Heap.NormalC2"
/-- Positive C2 target for the worked Heap normal card (no existential configuration: entry registers
agree with the canonical source, the spec is source-pinned). -/
def NormalC2 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) : Prop :=
  ∃ (domain : ArmCert.Translate.Model.QueryDomain) (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : ArmCert.Translate.Model.HeapV2E17.Pins) (scope : Nat → Prop) (image : MemReloc.Image)
    (loadBase : MemReloc.Word) (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat)
    (e : ArmBridge.Draft.NativeState),
    AgreesAt (Configuration.ofSource rho caller) e.regs ∧ SourceSpec rho caller spec ∧
    NormalResidual spec rows mapping pins scope image loadBase base offS budget rho caller e

#check "CURRENT_DECL GB10.Heap.normal_c2_reduce"
/-- Reduction: it suffices to prove the residual (other than the timers field, discharged here from
the source restriction) at the source-built entry for every source-pinned spec that carries the given
tables, with a payload family whose PhysicalCount is the given pcount and a budget within
`timersBudget`. Tables are TopologyTables (no configuration binder); the spec is source-pinned by construction. -/
theorem normal_c2_reduce (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (sem : ModelSemantics) (payloadOf : BitVec 88 → ModelPayload)
    (sameCount : ∀ pcount, (payloadOf pcount).data.PhysicalCount = pcount)
    {domain : ArmCert.Translate.Model.QueryDomain} (tables : TopologyTables domain) (oracle : OracleChoice)
    (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : ArmCert.Translate.Model.HeapV2E17.Pins) (scope : Nat → Prop) (image : MemReloc.Image)
    (loadBase : MemReloc.Word) (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat)
    (disabled : ∀ pcount, TimersDisabled (payloadOf pcount).data.timers)
    (residual : ∀ (pcount : BitVec 88) (spec : ArmCert.Translate.Model.TopologyImageSpec domain),
      SourceSpec rho caller spec →
      spec.layout = tables.layout → spec.logicalRows = tables.logicalRows →
      spec.imageRows = tables.imageRows →
      TimersQuiet (makeModelEntry sem rho caller (payloadOf pcount)).regs budget →
      NormalResidual spec rows mapping pins scope image loadBase base offS budget rho caller
        (makeModelEntry sem rho caller (payloadOf pcount))) :
    NormalC2 rho caller := by
  obtain ⟨pcount, -⟩ : ∃ _ : BitVec 88, True := ⟨0#88, trivial⟩
  have timers := model_timersQuiet sem rho caller (payloadOf pcount) (disabled pcount) budget
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho caller tables oracle (payloadOf pcount).data
    (makeModelEntry sem rho caller (payloadOf pcount)) rfl
  exact ⟨domain, spec, rows, mapping, pins, scope, image, loadBase, base, offS, budget,
    makeModelEntry sem rho caller (payloadOf pcount), makeModelEntry_agrees sem rho caller (payloadOf pcount),
    sspec, residual pcount spec sspec hl hlr hir timers⟩

#check "CURRENT_DECL GB10.Heap.HeapWorld"
/-- Closed program/payload data of the worked Heap normal model entry. Memory is a finite byte plan
(image, slot/data and table bytes) with distinct addresses; nothing here is configuration. -/
structure HeapWorld where
  /-- Image code bytes at their mapped physical addresses. -/
  imagePlan : List (Nat × BitVec 8)
  /-- Shim slot bytes. -/
  slotPlan : List (Nat × BitVec 8)
  /-- Data bytes. -/
  dataPlan : List (Nat × BitVec 8)
  /-- Translation-table descriptor bytes. -/
  tablePlan : List (Nat × BitVec 8)
  planKeys : (imagePlan ++ slotPlan ++ dataPlan ++ tablePlan).Pairwise (fun a b => (a.1 == b.1) = false)
  mapping : BitVec 64 → Option Nat
  pins : ArmCert.Translate.Model.HeapV2E17.Pins
  scope : Nat → Prop
  image : MemReloc.Image
  loadBase : MemReloc.Word
  base : BitVec 64
  offS : Nat → BitVec 64
  budget : Nat
  rows : List ArmCert.Translate.Model.PermissionRow
  data : DataPart

/-- The whole byte plan: the four named segments in order. -/
abbrev HeapWorld.plan (w : HeapWorld) : List (Nat × BitVec 8) :=
  w.imagePlan ++ w.slotPlan ++ w.dataPlan ++ w.tablePlan

/-- The world payload: its register data with the source-feasible PhysicalCount and its byte plan. -/
def worldPayload (w : HeapWorld) (pcount : BitVec 88) : ModelPayload :=
  ⟨{ w.data with PhysicalCount := pcount }, Std.ExtHashMap.ofList w.plan⟩

/-- The source-built model entry of a world. -/
def worldEntry (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (w : HeapWorld) (pcount : BitVec 88) : ArmBridge.Draft.NativeState :=
  makeModelEntry sem rho caller (worldPayload w pcount)

#check "CURRENT_DECL GB10.Heap.world_realizes"
/-- Every planned byte is present in the world entry's memory. -/
theorem world_realizes (sem : ModelSemantics) (rho : AdmissibleSourceCompletion)
    (caller : AdmissibleCaller rho) (w : HeapWorld) (pcount : BitVec 88) :
    ∀ ab ∈ w.plan, (worldEntry sem rho caller w pcount).mem[ab.1]? = some ab.2 :=
  fun ⟨_, _⟩ mem => Std.ExtHashMap.getElem?_ofList_of_mem (BEq.refl _) w.planKeys mem

theorem world_realizes_image (sem : ModelSemantics) (rho : AdmissibleSourceCompletion)
    (caller : AdmissibleCaller rho) (w : HeapWorld) (pcount : BitVec 88) :
    ∀ ab ∈ w.imagePlan, (worldEntry sem rho caller w pcount).mem[ab.1]? = some ab.2 :=
  fun ab mem => world_realizes sem rho caller w pcount ab (by simp [HeapWorld.plan, mem])

theorem world_realizes_slot (sem : ModelSemantics) (rho : AdmissibleSourceCompletion)
    (caller : AdmissibleCaller rho) (w : HeapWorld) (pcount : BitVec 88) :
    ∀ ab ∈ w.slotPlan, (worldEntry sem rho caller w pcount).mem[ab.1]? = some ab.2 :=
  fun ab mem => world_realizes sem rho caller w pcount ab (by simp [HeapWorld.plan, mem])

theorem world_realizes_data (sem : ModelSemantics) (rho : AdmissibleSourceCompletion)
    (caller : AdmissibleCaller rho) (w : HeapWorld) (pcount : BitVec 88) :
    ∀ ab ∈ w.dataPlan, (worldEntry sem rho caller w pcount).mem[ab.1]? = some ab.2 :=
  fun ab mem => world_realizes sem rho caller w pcount ab (by simp [HeapWorld.plan, mem])

theorem world_realizes_table (sem : ModelSemantics) (rho : AdmissibleSourceCompletion)
    (caller : AdmissibleCaller rho) (w : HeapWorld) (pcount : BitVec 88) :
    ∀ ab ∈ w.tablePlan, (worldEntry sem rho caller w pcount).mem[ab.1]? = some ab.2 :=
  fun ab mem => world_realizes sem rho caller w pcount ab (by simp [HeapWorld.plan, mem])

#check "CURRENT_DECL GB10.Heap.normal_c2_of_world"
/-- Positive normal C2 from a world: the remaining obligation is the residual (minus timers) at the
world entry, for every source-pinned spec carrying the given tables. -/
theorem normal_c2_of_world (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (sem : ModelSemantics) (w : HeapWorld) (disabled : TimersDisabled w.data.timers)
    {domain : ArmCert.Translate.Model.QueryDomain} (tables : TopologyTables domain) (oracle : OracleChoice)
    (residual : ∀ (pcount : BitVec 88) (spec : ArmCert.Translate.Model.TopologyImageSpec domain),
      SourceSpec rho caller spec →
      spec.layout = tables.layout → spec.logicalRows = tables.logicalRows →
      spec.imageRows = tables.imageRows →
      TimersQuiet (worldEntry sem rho caller w pcount).regs w.budget →
      NormalResidual spec w.rows w.mapping w.pins w.scope w.image w.loadBase w.base w.offS w.budget rho caller
        (worldEntry sem rho caller w pcount)) :
    NormalC2 rho caller :=
  normal_c2_reduce rho caller sem (worldPayload w) (fun _ => rfl) tables oracle w.rows w.mapping w.pins
    w.scope w.image w.loadBase w.base w.offS w.budget (fun _ => disabled) residual

#check "CURRENT_DECL GB10.Heap.world_tagStatusRows"
theorem world_tagStatusRows (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (w : HeapWorld)
    (pcount : BitVec 88) (draws : Nat) :
    NativeMteTagCheck.TagStatusRows (worldEntry worldSemantics rho caller w pcount)
      ((worldEntry worldSemantics rho caller w pcount).choiceOcc.getD 1354 0) draws :=
  model_tagStatusRows rho caller (worldPayload w pcount) draws

end ReleaseProfile.GB10.Heap

#print axioms ReleaseProfile.GB10.Heap.normal_c2_reduce
#print axioms ReleaseProfile.GB10.Heap.world_realizes
#print axioms ReleaseProfile.GB10.Heap.normal_c2_of_world
#print axioms ReleaseProfile.GB10.Heap.world_tagStatusRows
