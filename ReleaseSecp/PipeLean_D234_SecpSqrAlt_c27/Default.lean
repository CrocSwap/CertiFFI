import PipeLean_D234_SecpSqrAlt_c27.EntryBinding
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
namespace PipeLean_D234_SecpSqrAlt_c27.Default

def inputs (mapping : BitVec 64 → Option Nat) (initial : NativeState) : List (BitVec 64) :=
  SecpCurrentEntry.inputs EntryBinding.plan mapping initial

theorem inputs_length (mapping : BitVec 64 → Option Nat) (initial : NativeState) :
    (inputs mapping initial).length = n0_c00 :=
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
        regions_c00 σ0_c00 (inputs mapping initial) (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) 0 initial ∧
      LayoutFacts EntryBinding.plan raw mapping base initial ∧
      base.toNat % 4096 = 0 ∧ (entryGPR initial 30).toNat < 2 ^ 55 ∧
      (∀ site ∈ sites EntryBinding.plan initial, SelectedLoadFacts.checkTargets mapping site.address = true) ∧
      CheckedEntry.checkQueries (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 1030
        (queries EntryBinding.plan base initial) 4 (beforeFetchState initial) = true ∧
      NativeMteTagCheck.TagStatusRows initial (initial.choiceOcc.getD 1354 0) capacity :=
  SecpDefaultEntry.of_check EntryBinding.plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base capacity initial
    .f regions_c00 (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) checked

#print axioms initial_from_check

def fetch_0 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2839546914#32 x := by
  have member : (7592, 2839546914) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[0]? = some (7592, 2839546914) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 7592 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    0 x core (7592, 2839546914) member pc

#print axioms fetch_0

def fetch_3 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 3 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2839614500#32 x := by
  have member : (7604, 2839614500) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[3]? = some (7604, 2839614500) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 7604 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    3 x core (7604, 2839614500) member pc

#print axioms fetch_3

def fetch_76 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 76 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2835358728#32 x := by
  have member : (7896, 2835358728) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[76]? = some (7896, 2835358728) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 7896 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    76 x core (7896, 2835358728) member pc

#print axioms fetch_76

def fetch_77 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 77 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2835426314#32 x := by
  have member : (7900, 2835426314) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[77]? = some (7900, 2835426314) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 7900 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    77 x core (7900, 2835426314) member pc

#print axioms fetch_77

end PipeLean_D234_SecpSqrAlt_c27.Default
