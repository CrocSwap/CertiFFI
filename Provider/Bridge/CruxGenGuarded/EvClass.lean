import Bridge.CruxGenGuarded.ClassNextV4E
import Bridge.CruxGenGuarded.ChainInvV3
import RtB4.EvShapeBridge
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.EvSteps
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV3 ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! (H-P3): a fixed-class heap-v2 step from a ChainInv v3 state takes one actual model
step whose appended events have the single-run shape EvShape (fetch traffic + ifetch, no
data events: the class tail is event-silent). From ClassNextV4E's fetch run via
 evShape_of_fetchRun. -/

run_cmd do
  IO.eprintln "CURRENT_DECL EvSteps.ev_class"
  (← IO.getStderr).flush

theorem ev_class (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (next : NativeState → BitVec 64)
    (tail : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      HeapV2StepCerts.TailWE.ClassTailWAt real w writes K x (next x) (HeapV2StepCerts.RegBind.upds k) k)
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping w x) :
    ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      ∃ fin, modelStep real x = .ok () fin ∧ StepEvents.EvShape spec mapping [] x fin := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, fr⟩ :=
    ClassNextV4E.entry_class_next_v4e real spec config rows mapping w writes K x inv.v2.v1.pins (next x)
      (offset (k + 1)) (HeapV2StepCerts.RegBind.upds k) k (tail x inv) inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  exact ⟨fin, run, RtB4.EvShapeBridge.evShape_of_fetchRun spec config rows mapping w x fin inv.v2.v1.pins
    inv.v2.v1.features inv.v2.v1.debug inv.v2.v1.current
    (pc_low_of_placement _ base (offset k) inv.v2.v1.pc page aligned) ob inv.raw inv.noUpd nodup fr⟩

#print axioms ev_class
end ArmBridge.CruxGenGuarded.EvSteps
