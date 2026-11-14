import PipeLean_D234_SecpMulAlt_c19.EntryBinding
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
namespace PipeLean_D234_SecpMulAlt_c19.Default

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
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2839547939#32 x := by
  have member : (6644, 2839547939) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[0]? = some (6644, 2839547939) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 6644 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    0 x core (6644, 2839547939) member pc

#print axioms fetch_0

def fetch_1 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 1 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2839552071#32 x := by
  have member : (6648, 2839552071) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[1]? = some (6648, 2839552071) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 6648 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    1 x core (6648, 2839552071) member pc

#print axioms fetch_1

def fetch_7 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 7 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2839619657#32 x := by
  have member : (6672, 2839619657) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[7]? = some (6672, 2839619657) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 6672 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    7 x core (6672, 2839619657) member pc

#print axioms fetch_7

def fetch_15 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 15 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2839615525#32 x := by
  have member : (6704, 2839615525) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[15]? = some (6704, 2839615525) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 6704 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    15 x core (6704, 2839615525) member pc

#print axioms fetch_15

def fetch_98 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 98 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2835362828#32 x := by
  have member : (7036, 2835362828) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[98]? = some (7036, 2835362828) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 7036 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    98 x core (7036, 2835362828) member pc

#print axioms fetch_98

def fetch_99 (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) (x : NativeState)
    (core : Core (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 99 x)
    (layout : LayoutFacts EntryBinding.plan raw mapping base initial) :
    FetchObligations (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows mapping 2835430414#32 x := by
  have member : (7040, 2835430414) ∈ EntryBinding.plan.code :=
    List.mem_of_getElem? (show EntryBinding.plan.code[99]? = some (7040, 2835430414) by rfl)
  have pc : x.regs._PC = MemReloc.imageAddress base 7040 := by
    rw [core.v1.pc]; rfl
  exact SecpDefaultEntry.fetch (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) config rows EntryBinding.plan raw mapping base initial rfl
    layout (referenceImageI SecpArtifact.elf base (fun _ => 0)) (fun c member i hi => ImageBinding.code_image base member i hi)
    99 x core (7040, 2835430414) member pc

#print axioms fetch_99

end PipeLean_D234_SecpMulAlt_c19.Default
