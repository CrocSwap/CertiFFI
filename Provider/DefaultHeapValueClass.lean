-- Current heap scalar value effects through the actual fetch.
import DefaultHeapValueEntry
import DefaultHeapEntryMem
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ReleaseProfile.DefaultHeapValueClass
theorem class_vholds (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (next : NativeState → BitVec 64)
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (fl : Option (ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd))
    (tail : ∀ x, DefaultHeapEntryMem.HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue entry capacity drawsBefore k x →
      ArmCertValue.ClassTailXAt real w writes K x (next x) vus fl)
    (nextPlaced : ∀ x, DefaultHeapEntryMem.HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue entry capacity drawsBefore k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, DefaultHeapEntryMem.HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue entry capacity drawsBefore k x →
      FetchObligations spec config rows mapping w x) :
    ∀ x, DefaultHeapEntryMem.HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue entry capacity drawsBefore k x →
      ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds vus fl x fin ∧ fin.mem = x.mem := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.core.v1.quiet
  exact DefaultHeapValueEntry.entry_class_next_X real spec config rows mapping w writes K x inv.core.v1.pins (next x)
      (offset (k + 1)) vus fl (tail x inv) inv.core.v1.gic inv.core.v1.features
      inv.core.v1.debug (budget - (k + 1)) hq base (offset k) inv.core.v1.pc page aligned (nextPlaced x inv)
      inv.core.v1.current m inv.core.closed scope image loadBase inv.core.placed separated
      inv.core.raw inv.core.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code


#print axioms class_vholds
end ReleaseProfile.DefaultHeapValueClass
