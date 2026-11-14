import PipeLean_D234_SecpAdd_c01.Default
import TranslateSpan.DefaultBudget
import TranslateSpan.DefaultCurrent
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmCert.Translate.Model.StaticPie ArmBridge.Boundary
open ArmBridge.CruxGenGuarded ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 150000
namespace PipeLean_D234_SecpAdd_c01.DefaultState

def drawsBefore (initial : NativeState) (k : Nat) : Nat :=
  DefaultBudget.before EntryBinding.plan initial k

def capacity (initial : NativeState) : Nat :=
  drawsBefore initial EntryBinding.plan.code.length

abbrev Inv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) : Nat → NativeState → Prop :=
  DefaultMTE2.Inv spec config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base base (offset EntryBinding.plan)
    EntryBinding.plan.code.length (profile initial) catalogue
    .f (view EntryBinding.plan mapping initial) regions_c00 σ0_c00
    (Default.inputs mapping initial) (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) initial (capacity initial) (drawsBefore initial)

def check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) : Bool := Default.check raw config rows mapping base initial catalogue (capacity initial)

theorem initial_from_check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (checked : check raw config rows mapping base initial catalogue = true) :
    ∃ topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true,
      Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial ∧
      LayoutFacts EntryBinding.plan raw mapping base initial ∧
      base.toNat % 4096 = 0 ∧ (entryGPR initial 30).toNat < 2 ^ 55 ∧
      (∀ site ∈ sites EntryBinding.plan initial, SelectedLoadFacts.checkTargets mapping site.address = true) ∧
      CheckedEntry.checkQueries (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 1030
        (queries EntryBinding.plan base initial) 4 (beforeFetchState initial) = true := by
  obtain ⟨topology, core, branch, agrees, layout, page, ret, targets, queries, status⟩ :=
    Default.initial_from_check raw config rows mapping base initial catalogue (capacity initial) checked
  exact ⟨topology, ⟨core,branch,agrees,status,0,NativeMteTagCheck.choice_delta_refl initial,Nat.zero_le _⟩,
    layout,page,ret,targets,queries⟩

#print axioms initial_from_check

theorem budget_next_0 (initial : NativeState) :
    drawsBefore initial (0 + 1) = drawsBefore initial 0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0)) := by
  change (0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) =
    0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))
  omega

theorem budget_room_0 (initial : NativeState) :
    drawsBefore initial 0 < capacity initial := by
  change 0 < ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
  have positive := DefaultBudget.cost_positive (BitVec.addInt (entryGPR initial 1) (0))
  omega

theorem status_0 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (x : NativeState) (inv : Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 x) : NativeMteTagCheck.TagStatusOK x :=
  DefaultMTE2.bounded_status initial x (capacity initial) (drawsBefore initial 0)
    inv.statusRows inv.trace (budget_room_0 initial)

#print axioms budget_next_0
#print axioms budget_room_0
#print axioms status_0

theorem budget_next_1 (initial : NativeState) :
    drawsBefore initial (1 + 1) = drawsBefore initial 1 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0)) := by
  change ((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) =
    (0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))
  omega

theorem budget_room_1 (initial : NativeState) :
    drawsBefore initial 1 < capacity initial := by
  change (0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) < ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
  have positive := DefaultBudget.cost_positive (BitVec.addInt (entryGPR initial 2) (0))
  omega

theorem status_1 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (x : NativeState) (inv : Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 1 x) : NativeMteTagCheck.TagStatusOK x :=
  DefaultMTE2.bounded_status initial x (capacity initial) (drawsBefore initial 1)
    inv.statusRows inv.trace (budget_room_1 initial)

#print axioms budget_next_1
#print axioms budget_room_1
#print axioms status_1

theorem budget_next_4 (initial : NativeState) :
    drawsBefore initial (4 + 1) = drawsBefore initial 4 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16)) := by
  change (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) =
    ((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))
  omega

theorem budget_room_4 (initial : NativeState) :
    drawsBefore initial 4 < capacity initial := by
  change ((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) < ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
  have positive := DefaultBudget.cost_positive (BitVec.addInt (entryGPR initial 1) (16))
  omega

theorem status_4 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (x : NativeState) (inv : Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 4 x) : NativeMteTagCheck.TagStatusOK x :=
  DefaultMTE2.bounded_status initial x (capacity initial) (drawsBefore initial 4)
    inv.statusRows inv.trace (budget_room_4 initial)

#print axioms budget_next_4
#print axioms budget_room_4
#print axioms status_4

theorem budget_next_5 (initial : NativeState) :
    drawsBefore initial (5 + 1) = drawsBefore initial 5 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16)) := by
  change ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) =
    (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))
  omega

theorem budget_room_5 (initial : NativeState) :
    drawsBefore initial 5 < capacity initial := by
  change (((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) < ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
  have positive := DefaultBudget.cost_positive (BitVec.addInt (entryGPR initial 2) (16))
  omega

theorem status_5 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (x : NativeState) (inv : Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 5 x) : NativeMteTagCheck.TagStatusOK x :=
  DefaultMTE2.bounded_status initial x (capacity initial) (drawsBefore initial 5)
    inv.statusRows inv.trace (budget_room_5 initial)

#print axioms budget_next_5
#print axioms budget_room_5
#print axioms status_5

theorem budget_next_21 (initial : NativeState) :
    drawsBefore initial (21 + 1) = drawsBefore initial 21 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0)) := by
  change (((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) =
    ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))
  omega

theorem budget_room_21 (initial : NativeState) :
    drawsBefore initial 21 < capacity initial := by
  change ((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) < ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
  have positive := DefaultBudget.cost_positive (BitVec.addInt (entryGPR initial 0) (0))
  omega

theorem status_21 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (x : NativeState) (inv : Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 21 x) : NativeMteTagCheck.TagStatusOK x :=
  DefaultMTE2.bounded_status initial x (capacity initial) (drawsBefore initial 21)
    inv.statusRows inv.trace (budget_room_21 initial)

#print axioms budget_next_21
#print axioms budget_room_21
#print axioms status_21

theorem budget_next_22 (initial : NativeState) :
    drawsBefore initial (22 + 1) = drawsBefore initial 22 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)) := by
  change ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))) =
    (((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))
  omega

theorem budget_room_22 (initial : NativeState) :
    drawsBefore initial 22 < capacity initial := by
  change (((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) < ((((((0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16)))
  have positive := DefaultBudget.cost_positive (BitVec.addInt (entryGPR initial 0) (16))
  omega

theorem status_22 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true)
    (x : NativeState) (inv : Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 22 x) : NativeMteTagCheck.TagStatusOK x :=
  DefaultMTE2.bounded_status initial x (capacity initial) (drawsBefore initial 22)
    inv.statusRows inv.trace (budget_room_22 initial)

#print axioms budget_next_22
#print axioms budget_room_22
#print axioms status_22

theorem budgets (initial : NativeState) :
    (drawsBefore initial (0 + 1) = drawsBefore initial 0 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (0))) ∧
    (drawsBefore initial 0 < capacity initial) ∧
    (drawsBefore initial (1 + 1) = drawsBefore initial 1 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (0))) ∧
    (drawsBefore initial 1 < capacity initial) ∧
    (drawsBefore initial (4 + 1) = drawsBefore initial 4 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 1) (16))) ∧
    (drawsBefore initial 4 < capacity initial) ∧
    (drawsBefore initial (5 + 1) = drawsBefore initial 5 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 2) (16))) ∧
    (drawsBefore initial 5 < capacity initial) ∧
    (drawsBefore initial (21 + 1) = drawsBefore initial 21 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (0))) ∧
    (drawsBefore initial 21 < capacity initial) ∧
    (drawsBefore initial (22 + 1) = drawsBefore initial 22 + DefaultBudget.cost (BitVec.addInt (entryGPR initial 0) (16))) ∧
    (drawsBefore initial 22 < capacity initial) :=
  ⟨budget_next_0 initial, budget_room_0 initial, budget_next_1 initial, budget_room_1 initial, budget_next_4 initial, budget_room_4 initial, budget_next_5 initial, budget_room_5 initial, budget_next_21 initial, budget_room_21 initial, budget_next_22 initial, budget_room_22 initial⟩

theorem statuses (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) :
    (∀ x, Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 x → NativeMteTagCheck.TagStatusOK x) ∧
    (∀ x, Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 1 x → NativeMteTagCheck.TagStatusOK x) ∧
    (∀ x, Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 4 x → NativeMteTagCheck.TagStatusOK x) ∧
    (∀ x, Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 5 x → NativeMteTagCheck.TagStatusOK x) ∧
    (∀ x, Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 21 x → NativeMteTagCheck.TagStatusOK x) ∧
    (∀ x, Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 22 x → NativeMteTagCheck.TagStatusOK x) :=
  ⟨status_0 raw config rows mapping base initial catalogue topology, status_1 raw config rows mapping base initial catalogue topology, status_4 raw config rows mapping base initial catalogue topology, status_5 raw config rows mapping base initial catalogue topology, status_21 raw config rows mapping base initial catalogue topology, status_22 raw config rows mapping base initial catalogue topology⟩

#print axioms budgets
#print axioms statuses

end PipeLean_D234_SecpAdd_c01.DefaultState
