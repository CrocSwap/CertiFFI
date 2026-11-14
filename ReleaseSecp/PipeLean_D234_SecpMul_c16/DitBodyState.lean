import PipeLean_D234_SecpMul_c16.DefaultState
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace PipeLean_D234_SecpMul_c16.DitBodyState
abbrev Inv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) : Nat → NativeState → Prop :=
  DefaultMTE2.Inv spec config rows mapping (consumer EntryBinding.plan raw mapping base initial)
    (· ∈ codeOffsets EntryBinding.plan) (referenceImageI SecpArtifact.elf base (fun _ => 0)) base base (offset EntryBinding.plan)
    (EntryBinding.plan.code.length + 4) (profile initial) catalogue
    .g (view EntryBinding.plan mapping initial) regions_c00 σ0_c00
    (Default.inputs mapping initial) (plan_c00 (initial.regs.bank_BitVec_64 .TPIDR_EL0)) initial
    (DefaultState.capacity initial) (DefaultState.drawsBefore initial)

/-- Internal current-state receipt, produced after the actual prologue.
The spans and targets are state-free deployment facts transported from entry. -/
structure Receipt (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (initial : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (topology : CheckedTopology.check raw (addresses EntryBinding.plan base initial) 4 = true) : Prop where
  initialInv : Inv (CheckedTopology.spec raw (addresses EntryBinding.plan base initial) 4 topology) raw config rows mapping base initial catalogue 0 initial
  layout : LayoutFacts EntryBinding.plan raw mapping base initial
  page : base.toNat % 4096 = 0
  low : (entryGPR initial 30).toNat < 2 ^ 55
  targets : ∀ site ∈ sites EntryBinding.plan initial, SelectedLoadFacts.checkTargets mapping site.address = true
  spans : ∀ (r : Region) (n word : Nat), (r,n) ∈ EntryBinding.plan.buffers → EntryBinding.plan.normalize r = r →
    8 * word + 16 ≤ n → SelectedBinding.At (view EntryBinding.plan mapping initial) r word mapping (regionVA initial r (8 * word))
end PipeLean_D234_SecpMul_c16.DitBodyState
