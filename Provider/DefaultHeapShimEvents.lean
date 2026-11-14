import RtDit4.ShimEv
import DefaultCurrent
import RtB4.EvShapeBridge
import RtB6.RichZ
import HeapV2StepCerts.MemTailDE
import HeapV2StepCerts.RegValE
import HeapV2StepCerts.FetchTiming
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts HeapV2StepCerts.MemNext NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ReleaseProfile.DefaultHeapShimEvents
open RtDit.ShimEv
open RtDit RtDit.Shim

theorem shim_ev (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (w : BitVec 32) (x : NativeState)
    (inv : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (ob : FetchObligations spec config rows mapping w x) (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (tail : ∀ (final : NativeState) (enc0 : __InstrEnc),
      DitFetched spec config rows mapping m x final (budget - (k + 1)) →
      ∃ fin, nativeTail real x w enc0 final = .ok () fin ∧ ∃ D : Array Event, fin.events = final.events ++ D ∧
        D.toList.map ArmCertCTOrdered.OrderedEventV2.record = data) :
    ∃ fin, modelStep real x = .ok () fin ∧ StepEvents.EvShape spec mapping data x fin := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  obtain ⟨final, fin, run, frun, D, evs, recs⟩ :=
    entry_genE real spec config rows mapping w x inv.v1.pins inv.v1.gic inv.v1.features inv.v1.debug
      (budget - (k + 1)) hq base (offset k) inv.v1.pc page aligned inv.v1.current m inv.closed inv.raw
      inv.noUpd ob _ tail
  exact ⟨fin, run, evShape_of_fetchRunD spec config rows mapping w x fin inv.v1.pins inv.v1.features
    inv.v1.debug inv.v1.current (pc_low_of_placement _ base (offset k) inv.v1.pc page aligned) ob inv.raw
    inv.noUpd nodup data ⟨final, w, frun, D, evs, recs⟩⟩


#print axioms shim_ev
end ReleaseProfile.DefaultHeapShimEvents
