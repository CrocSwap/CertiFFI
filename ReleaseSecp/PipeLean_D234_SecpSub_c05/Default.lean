import PipeLean_D234_SecpSub_c05.EntryBinding
import TranslateSpan.SecpDefaultEntry
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmCert.Translate.Model.StaticPie ArmBridge.Boundary
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
open ArmCertValue ArmCertPipe NativeAccess HeapV2StepCerts.RegBind
open TranslateSpan TranslateSpan.SecpRawDeployment
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 150000
namespace PipeLean_D234_SecpSub_c05.Default

def inputs (mapping : BitVec 64 → Option Nat) (initial : NativeState) : List (BitVec 64) :=
  SecpCurrentEntry.inputs EntryBinding.plan mapping initial

theorem inputs_length (mapping : BitVec 64 → Option Nat) (initial : NativeState) :
    (inputs mapping initial).length = n0_c05 :=
  SecpCurrentEntry.inputs_length EntryBinding.plan mapping initial

abbrev Core {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) : Nat → NativeState → Prop :=
  DefaultMTE2.Core spec config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base base (offset EntryBinding.plan)
    EntryBinding.plan.code.length (profile initial) catalogue

def check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) : Bool :=
  SecpDefaultEntry.check EntryBinding.plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base capacity initial catalogue

theorem initial_from_check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (checked : check raw config rows mapping base initial catalogue capacity = true) :
    ∃ topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true,
      Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial ∧
      BranchMTE2.Pins initial ∧
      ValuePlan.AgreesAt .f (view EntryBinding.plan mapping initial)
        regions_c05 σ0_c05 (inputs mapping initial) (plan_c05 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) 0 initial ∧
      LayoutFacts EntryBinding.plan raw mapping base initial ∧
      base.toNat % 4096 = 0 ∧ (entryGPR initial 30).toNat < 2 ^ 55 ∧
      (∀ site ∈ sites EntryBinding.plan initial, SelectedLoadFacts.checkTargets mapping site.address = true) ∧
      CheckedEntry.checkQueries (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 1030
        (queries EntryBinding.plan base initial) 4 (beforeFetchState initial) = true ∧
      NativeMteTagCheck.TagStatusRows initial (initial.choiceOcc.getD 1354 0) capacity :=
  SecpDefaultEntry.of_check EntryBinding.plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base capacity initial
    .f regions_c05 (plan_c05 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) checked

#print axioms initial_from_check

def fetch_0 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2839549989#32 x := by
  have member : (5784, 2839549989) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[0]? = some (5784, 2839549989) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 5784 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    0 x core (5784, 2839549989) member pc

#print axioms fetch_0

def fetch_1 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 1 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2839546948#32 x := by
  have member : (5788, 2839546948) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[1]? = some (5788, 2839546948) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 5788 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    1 x core (5788, 2839546948) member pc

#print axioms fetch_1

def fetch_4 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 4 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2839617575#32 x := by
  have member : (5800, 2839617575) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[4]? = some (5800, 2839617575) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 5800 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    4 x core (5800, 2839617575) member pc

#print axioms fetch_4

def fetch_5 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 5 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2839612484#32 x := by
  have member : (5804, 2839612484) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[5]? = some (5804, 2839612484) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 5804 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    5 x core (5804, 2839612484) member pc

#print axioms fetch_5

def fetch_15 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 15 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2835355653#32 x := by
  have member : (5844, 2835355653) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[15]? = some (5844, 2835355653) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 5844 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    15 x core (5844, 2835355653) member pc

#print axioms fetch_15

def fetch_16 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 16 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2835423239#32 x := by
  have member : (5848, 2835423239) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[16]? = some (5848, 2835423239) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 5848 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    16 x core (5848, 2835423239) member pc

#print axioms fetch_16

end PipeLean_D234_SecpSub_c05.Default
