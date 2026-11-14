-- Current-profile heap body fetch and placed successor from checked code.
import HeapV2StepCerts.MemStepV3
import DefaultCurrent

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.HeapV2Compose ArmBridge.CruxGenGuarded.ChainInvV2
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapCode
open HeapV2StepCerts
open HeapV2StepCerts.RegBind HeapV2StepCerts.C3

/-- Code side of a memory step (identical to straight2's placedNext / fetch fields). -/
theorem memNextPlaced
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget k : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (off wordNat : Nat) (member : (off, wordNat) ∈ HeapV2Plan.codeWords)
    (here : offsetOf k = BitVec.ofNat 64 (0x10278 + off))
    (succ : offsetOf (k + 1) = BitVec.ofNat 64 (0x10278 + off + 4)) (x : NativeState)
    (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping
      (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base)
      base base offsetOf budget k catalogue x) : x.regs._PC + 4#64 = base + offsetOf (k + 1) := by
  rw [inv.v1.pc, here, succ, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

def memFetch
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget k : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (off wordNat : Nat) (member : (off, wordNat) ∈ HeapV2Plan.codeWords)
    (here : offsetOf k = BitVec.ofNat 64 (0x10278 + off))
    (w : BitVec 32) (wordEq : w = BitVec.ofNat 32 wordNat) (x : NativeState)
    (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping
      (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base)
      base base offsetOf budget k catalogue x) : FetchObligations spec config rows mapping w x :=
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
    perAcc := HeapV2E17.fetch_per_acc_el0 spec config rows mapping pins base.toNat table
      member pcCode inv.closed rme nrw inv.v1.features.b3 inv.v1.features.a3 el mode.ns
    code := by
      intro acc leafLevel view faultOut address translated w' clean bytes
      rw [wordEq]
      exact HeapV2E17.fetch_code spec config rows mapping (pre := ArmBridge.CruxGenGuarded.beforeFetchState x)
        member (fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩) (fun _ => rfl) inv.placed static.separated
        pcImage (static.inside _ member) (static.contiguous _ member) acc leafLevel view faultOut address
        translated w' clean bytes }

#print axioms memNextPlaced
#print axioms memFetch
end ReleaseProfile.DefaultHeapCode
