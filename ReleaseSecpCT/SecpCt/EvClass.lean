-- secp CT0: single-run event shape of a secp class step over TranslateSpan.DefaultMTE2.Core,
-- through Runtime14 DefaultClassEvent.entry_class_event (same tail/fetch inputs the secp step proofs already build).
import DefaultClassEvent
import TranslateSpan.DefaultScalar
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace SecpCt

theorem ev_class (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : BitVec 64)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat)
    (profile : NativeAccess.AccessProfile) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (fl : Option (ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd))
    (next : NativeState → BitVec 64) (x : NativeState)
    (core : TranslateSpan.DefaultMTE2.Core spec config rows mapping m scope image loadBase base offset budget profile catalogue k x)
    (tail : ArmCertValue.ClassTailXAt real w writes K x (next x) vus fl)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (nextPlaced : next x = base + offset (k + 1)) (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧ StepEvents.EvShape spec mapping [] x fin := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact core.v1.quiet
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, events⟩ :=
    ReleaseProfile.DefaultClassEvent.entry_class_event real spec config rows mapping w writes K x
      core.v1.pins (next x) (offset (k + 1)) vus fl tail core.v1.gic core.v1.features core.v1.debug
      (budget - (k + 1)) hq base (offset k) core.v1.pc page aligned nextPlaced core.v1.current m
      core.closed scope image loadBase core.placed separated core.raw core.noUpd
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code nodup
  exact ⟨fin, run, events⟩

end SecpCt
#print axioms SecpCt.ev_class
