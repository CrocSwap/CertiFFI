import DefaultHeapClassStep
import DefaultHeapBranchStep
import DefaultHeapCode
import DefaultHeapCbzTail
import DefaultBcondEventTail
import HeapScalarTagCheck.Tails
import HeapV2StepCerts.MemFetchOn
import HeapV2StepCerts.ValBindTrapSteps
import RtBl.TrapPaths
import HeapV2StepCerts.Residue.ZSeg_00

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open HeapV2StepCerts HeapV2StepCerts.C3 CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ReleaseProfile.DefaultHeapTrap

abbrev BaseInv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (S : Nat × Nat × Int × Nat × Bool → Prop) (base : BitVec 64) (budget : Nat)
    (pins : HeapV2E17.Pins) (table : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState) (off : Nat → BitVec 64) (k : Nat) (x : NativeState) : Prop :=
  DefaultHeapEntryMem.HeapInv spec config rows mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table)
    codeScope (HeapV2.image base) base base off budget pins catalogue entry 0 (fun _ => 0) k x

theorem inv_congr {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {S : Nat × Nat × Int × Nat × Bool → Prop} {base : BitVec 64} {budget : Nat}
    {pins : HeapV2E17.Pins} {table : Nat → Prop} {catalogue : NativeMteTagCheck.ControlCatalogue}
    {entry x : NativeState} {off off' : Nat → BitVec 64} {k : Nat}
    (inv : BaseInv spec config rows mapping S base budget pins table catalogue entry off k x)
    (same : off k = off' k) : BaseInv spec config rows mapping S base budget pins table catalogue entry off' k x := by
  refine { inv with core := { inv.core with v1 := { inv.core.v1 with pc := ?_ } } }
  rw [inv.core.v1.pc, same]

def fetchOn (S : Nat × Nat × Int × Nat × Bool → Prop)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget k : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (off wordNat : Nat) (member : (off, wordNat) ∈ HeapV2Plan.codeWords)
    (here : HeapV2Compose.offsetOf k = BitVec.ofNat 64 (0x10278 + off))
    (w : BitVec 32) (wordEq : w = BitVec.ofNat 32 wordNat) (x : NativeState)
    (inv : DefaultCurrent.CurrentInv spec config rows mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table) codeScope
      (HeapV2.image base) base base HeapV2Compose.offsetOf budget k catalogue x) : FetchObligations spec config rows mapping w x :=
  have pcImage : x.regs._PC = MemReloc.imageAddress base (HeapV2.entryOffset + off) := by
    rw [inv.v1.pc, here]; rfl
  have pcCode : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs._PC =
      HeapV2E17.codeVA base.toNat (off, wordNat).1 := by
    show x.regs._PC = _
    rw [pcImage, MemReloc.imageAddress, add_ofNat]
    simp only [HeapV2E17.codeVA, Nat.add_assoc]
  have facts := ArmBridge.CruxGenGuarded.EntryActualFetch.before_fetch_facts x
    (NativeEntryTail.EntryPins.of_scalar x inv.v1.pins) inv.v1.features inv.v1.debug
  have el := facts.2.1
  have mode := facts.2.2.2.2.2.2.1
  have ep := NativeEntryTail.EntryPins.of_scalar x inv.v1.pins
  have rme : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.FeatureImpl[232] = false := by
    show x.regs.FeatureImpl[232] = false; simpa using ep.rme
  have nrw : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.PSTATE.nRW = 0#1 := by
    show x.regs.PSTATE.nRW = 0#1; simpa using ep.nrw
  { queryOf := fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩
    rawOf := fun _ => rfl
    vaOf := fun _ => rfl
    mmio := by rw [pcImage]; exact static.notMMIO _ member
    present := mapped_bytes_present_of_image_on inv.placed pcImage
      (static.inside _ member) (static.contiguous _ member)
    perAcc := HeapV2StepCerts.MemNext.fetch_per_acc_on spec config rows mapping S pins base.toNat table member pcCode inv.closed
      (fun _ actual => ArmCertWalk.actual_ifetch_el_ss actual rme nrw inv.v1.features.b3 inv.v1.features.a3 el mode.ns)
    code := by
      intro acc leafLevel view faultOut address translated w' clean bytes
      rw [wordEq]
      exact HeapV2E17.fetch_code spec config rows mapping (pre := ArmBridge.CruxGenGuarded.beforeFetchState x)
        member (fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩) (fun _ => rfl) inv.placed static.separated
        pcImage (static.inside _ member) (static.contiguous _ member) acc leafLevel view faultOut address
        translated w' clean bytes }



#print axioms inv_congr
#print axioms fetchOn
end ReleaseProfile.DefaultHeapTrap
