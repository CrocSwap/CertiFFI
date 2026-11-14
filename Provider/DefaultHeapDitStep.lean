-- Checked heap branch continuations with symbolic register and event effects.
import DefaultHeapEntryMem
import DefaultHeapShimBranch
import DefaultHeapShimBl
import DefaultHeapShimEffects
import DefaultHeapClassStep
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

namespace ReleaseProfile.DefaultHeapDitStep
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
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  have core := inv.core
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact core.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed,
      gpr, sp, mem, sys, br, tco, _, _, _, _, z, events, gcs, _, _, dit⟩ :=
    DefaultHeapShimBranch.entry_branch_event real spec config rows mapping w K x core.v1.pins
      (base + offset (k + 1)) (offset (k + 1)) tail core.v1.gic core.v1.features core.v1.debug
      (budget - (k + 1)) hq base (offset k) core.v1.pc page aligned rfl core.v1.current
      m core.closed scope image loadBase core.placed separated core.branch core.raw core.noUpd
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code nodup
  exact ⟨fin, run, dit⟩
#print axioms branch

theorem bl (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0) (imm26 : BitVec 26)
    (upd : RegBind.upds k = [(.x 30, .drop)]) (veff : ValBind.effAt k = .none)
    (x : NativeState) (inv : HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue entry capacity drawsBefore k x)
    (low : (NativeEntryCallerParts.blTarget imm26 x).toNat < 2 ^ 55)
    (controls : NativeEntryCallerParts.CallerControls x)
    (nextPlaced : NativeEntryCallerParts.blTarget imm26 x = base + offset (k + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (ob : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  have core := inv.core
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact core.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp,
      gpr, sp, mem, sys, tco, z, gcs, events, _, _, dit⟩ :=
    DefaultHeapShimBl.entry_bl real spec config rows mapping imm26 x core.v1.pins (offset (k + 1)) low controls
      core.v1.gic core.v1.features core.v1.debug (budget - (k + 1)) hq base (offset k) core.v1.pc
      page aligned nextPlaced core.v1.current m core.closed scope image loadBase core.placed separated
      core.branch core.raw core.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc nodup ob.code
  exact ⟨fin, run, dit⟩
#print axioms bl

theorem scalar (real : Type) [Sail.SailReal real]
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
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (x : NativeState) (inv : HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue entry capacity drawsBefore k x)
    (tail : TailWE.ClassTailWAt real w writes K x (x.regs._PC + 4#64) (RegBind.upds k) k)
    (target : x.regs._PC + 4#64 = base + offset (k + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (ob : FetchObligations spec config rows mapping w x)
    (noWriteDit : writes.dit = false) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  obtain ⟨fin, run, dit, _, _⟩ :=
    DefaultHeapShimEffects.shim_class real spec config rows mapping m scope image loadBase base offset budget k catalogue
      room page aligned x inv.core tail.tailV.toOld noWriteDit ob
  exact ⟨fin, run, dit⟩
#print axioms scalar

end ReleaseProfile.DefaultHeapDitStep
