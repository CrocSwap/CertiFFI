-- Memory (H-P2): one fixed-class step keeps the SIMD file and has its ValBind effect (Core's EvClass.ev_class
-- over ClassNextZ / ClassNextZF instead of the event shape).
import HeapV2StepCerts.ActionTransport
import HeapV2StepCerts.BodyHolds
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.Carry
import HeapV2StepCerts.CodeScope
import HeapV2StepCerts.MemConfigFrame
import HeapV2StepCerts.MemHolds
import HeapV2StepCerts.RawFetch
import HeapV2StepCerts.RegBind
import HeapV2StepCerts.RegBindCore
import HeapV2StepCerts.RegBindData
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.Straight
import HeapV2StepCerts.ValueTailDef
import HeapV2StepCerts.ClassNextZ
import HeapV2StepCerts.ClassNextZF
import HeapV2StepCerts.ClassNextZN
import Bridge.CruxGenGuarded.ChainInvV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV3 ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace HeapV2StepCerts.ZSteps

theorem z_class (real : Type) [Sail.SailReal real]
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
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._Z = x.regs._Z ∧ HeapV2StepCerts.ValBind.VEff k x fin := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, _, _, _, _, _, veff, _, _, z⟩ :=
    HeapV2StepCerts.ClassNextZ.entry_class_next_z real spec config rows mapping w writes K x inv.v2.v1.pins (next x)
      (offset (k + 1)) (HeapV2StepCerts.RegBind.upds k) k (tail x inv) inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  exact ⟨fin, run, z, veff⟩

theorem z_classF (real : Type) [Sail.SailReal real]
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
      HeapV2StepCerts.TailWE.ClassTailWFAt real w writes K x (next x) (HeapV2StepCerts.RegBind.upds k) k)
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping w x) :
    ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._Z = x.regs._Z ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
        HeapV2StepCerts.Flags.nzcv fin.regs = HeapV2StepCerts.Flags.nzcv x.regs := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, _, _, _, _, _, veff, _, _, z, fl⟩ :=
    HeapV2StepCerts.ClassNextZF.entry_class_next_zf real spec config rows mapping w writes K x inv.v2.v1.pins (next x)
      (offset (k + 1)) (HeapV2StepCerts.RegBind.upds k) k (tail x inv) inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  exact ⟨fin, run, z, veff, fl⟩

theorem z_classN (real : Type) [Sail.SailReal real]
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
      HeapV2StepCerts.TailWE.ClassTailWNAt real w writes K x (next x) (HeapV2StepCerts.RegBind.upds k) k)
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping w x) :
    ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._Z = x.regs._Z ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
        fin.regs.PSTATE.N = 0#1 ∧ fin.regs.PSTATE.C = 0#1 ∧ fin.regs.PSTATE.V = 0#1 := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, _, _, _, _, _, veff, _, _, z, hn, hc, hv⟩ :=
    HeapV2StepCerts.ClassNextZN.entry_class_next_zn real spec config rows mapping w writes K x inv.v2.v1.pins (next x)
      (offset (k + 1)) (HeapV2StepCerts.RegBind.upds k) k (tail x inv) inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  exact ⟨fin, run, z, veff, hn, hc, hv⟩

#print axioms z_class
#print axioms z_classF
#print axioms z_classN
end HeapV2StepCerts.ZSteps
