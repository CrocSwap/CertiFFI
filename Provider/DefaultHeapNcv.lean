import DefaultHeapClassEntryN
import DefaultCurrent
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ReleaseProfile.DefaultHeapNcv
theorem z_classN (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (next : NativeState → BitVec 64)
    (tail : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x →
      HeapV2StepCerts.TailWE.ClassTailWNAt real w writes K x (next x) (HeapV2StepCerts.RegBind.upds k) k)
    (nextPlaced : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x →
      FetchObligations spec config rows mapping w x) :
    ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._Z = x.regs._Z ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
        fin.regs.PSTATE.N = 0#1 ∧ fin.regs.PSTATE.C = 0#1 ∧ fin.regs.PSTATE.V = 0#1 := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, _, _, _, _, _, veff, _, z, _, _, _, hn, hc, hv⟩ :=
    DefaultHeapClassEntryN.entry_class_next_zn real spec config rows mapping w writes K x inv.v1.pins (next x)
      (offset (k + 1)) (HeapV2StepCerts.RegBind.upds k) k (tail x inv) inv.v1.gic inv.v1.features
      inv.v1.debug (budget - (k + 1)) hq base (offset k) inv.v1.pc page aligned (nextPlaced x inv)
      inv.v1.current m inv.closed scope image loadBase inv.placed separated inv.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc nodup ob.code
  exact ⟨fin, run, z, veff, hn, hc, hv⟩

#print axioms z_classN

theorem z_classF (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (next : NativeState → BitVec 64)
    (tail : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x →
      HeapV2StepCerts.TailWE.ClassTailWFAt real w writes K x (next x) (HeapV2StepCerts.RegBind.upds k) k)
    (nextPlaced : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x →
      FetchObligations spec config rows mapping w x) :
    ∀ x, DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._Z = x.regs._Z ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
        HeapV2StepCerts.Flags.nzcv fin.regs = HeapV2StepCerts.Flags.nzcv x.regs := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, _, _, _, _, _, veff, _, z, _, _, _, fl⟩ :=
    DefaultHeapClassEntryN.entry_class_next_zf real spec config rows mapping w writes K x inv.v1.pins (next x)
      (offset (k + 1)) (HeapV2StepCerts.RegBind.upds k) k (tail x inv) inv.v1.gic inv.v1.features
      inv.v1.debug (budget - (k + 1)) hq base (offset k) inv.v1.pc page aligned (nextPlaced x inv)
      inv.v1.current m inv.closed scope image loadBase inv.placed separated inv.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc nodup ob.code
  exact ⟨fin, run, z, veff, fl⟩


#print axioms z_classF

end ReleaseProfile.DefaultHeapNcv
