-- Checked heap branch continuations with symbolic register and event effects.
import DefaultHeapEntryMem
import TranslateStepV.BranchX
import DefaultBranchEvent
import DefaultBcondEventTail
import DefaultRetEventTail
import DefaultHeapCbzTail
import DefaultHeapBl

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapValueBranch
open ReleaseProfile.DefaultHeapEntryMem
theorem branch (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int) (upd0 : RegBind.upds k = []) (veff : ValBind.effAt k = .none)
    (x : NativeState) (inv : HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue entry capacity drawsBefore k x)
    (tail : DefaultBranchEvent.BranchTailEvent real w K x (base + offset (k + 1)))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem := by
  have core := inv.core
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact core.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed,
      gpr, sp, mem, sys, br, tco, n, nz, c, v, z, events, gcs, _, _⟩ :=
    DefaultBranchEvent.entry_branch_event real spec config rows mapping w K x core.v1.pins
      (base + offset (k + 1)) (offset (k + 1)) tail core.v1.gic core.v1.features core.v1.debug
      (budget - (k + 1)) hq base (offset k) core.v1.pc page aligned rfl core.v1.current
      m core.closed scope image loadBase core.placed separated core.branch core.raw core.noUpd
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code nodup
  exact ⟨fin, run, TranslateStepV.BranchX.vholds_nil gpr sp n nz c v, mem⟩
#print axioms branch
end ReleaseProfile.DefaultHeapValueBranch
