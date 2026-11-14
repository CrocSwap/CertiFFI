-- runtime14 CT: per-step event shape. EvOb data k: every step from an Inv-k state appends
-- exactly the fetch traffic + ifetch + data events with records `data` (StepEvents.EvShape). Two runs at the same
-- step k with the same PC and data, landing on equal PCs, are timing-equal (StepEvents.pair). The landing PCs
-- come from the run invariant at k+1 (PC = base + offset (k+1)) for every non-final step.
import ArmCertPipe.ZFrame
import TranslateStepV.ClassNextXE
import TranslateStepV.BranchXE
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
namespace ArmCertPipe
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView

/-- Step k's event shape (data records `data`). -/
abbrev EvOb (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (Inv : Nat → NativeState → Prop)
    (data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (k : Nat) : Prop :=
  ∀ x, Inv k x → ∀ fin, modelStep real x = .ok () fin →
    ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping data x fin

theorem evob_of_route {real : Type} [Sail.SailReal real] {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {mapping : BitVec 64 → Option Nat} {Inv : Nat → NativeState → Prop}
    {data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)} {k : Nat}
    (r : ∀ x, Inv k x → ∃ fin, modelStep real x = .ok () fin ∧
      ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping data x fin) :
    EvOb real spec mapping Inv data k := by
  intro x inv fin run
  obtain ⟨fin', run', e⟩ := r x inv
  rw [run] at run'; cases run'; exact e

/-- **One CT step**: two runs (possibly different invariants, e.g. different inputs) at step k, both with the same
 event data and PC, landing on equal PCs, are timing-equal. -/
theorem ct_of_evob {real : Type} [Sail.SailReal real] {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {mapping : BitVec 64 → Option Nat} {Inv1 Inv2 : Nat → NativeState → Prop}
    {data : List (Option ArmCertCTOrdered.OrderedEventV2.Record)} {k : Nat}
    (e1 : EvOb real spec mapping Inv1 data k) (e2 : EvOb real spec mapping Inv2 data k)
    (x y fx fy : NativeState) (ix : Inv1 k x) (iy : Inv2 k y)
    (rx : modelStep real x = .ok () fx) (ry : modelStep real y = .ok () fy)
    (pc : x.regs._PC = y.regs._PC) (pcf : fx.regs._PC = fy.regs._PC) :
    ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record x y fx fy := by
  exact ArmBridge.CruxGenGuarded.StepEvents.pair spec mapping data x y fx fy (e1 x ix fx rx) (e2 y iy fy ry) pc pcf

/-- class_vholdsG plus the event shape (data []). -/
theorem class_vholdsGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (next : NativeState → BitVec 64)
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (fl : Option (ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd × ArmCertValue.VUpd))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (x : NativeState) (inv : ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (tail : ArmCertValue.ClassTailXAt real w writes K x (next x) vus fl)
    (nextPlaced : next x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping [] x fin := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, _, _, _, ev, _⟩ := ArmBridge.CruxGenGuarded.ClassNextX.entry_class_next_XE real spec config rows
    mapping w writes K x inv.v2.v1.pins (next x) (offset (k + 1)) vus fl tail inv.v2.v1.gic inv.v2.v1.features
    inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
    inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
    inv.raw inv.noUpd obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio obligations.present
    obligations.perAcc obligations.code nodup
  exact ⟨fin, run, ev⟩

/-- branch_vholdsG plus the event shape (data []) (tail: BranchTailNZZE). -/
theorem branch_vholdsGE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int) (next : NativeState → BitVec 64)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (x : NativeState) (inv : ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (tail : TranslateStepV.BranchX.BranchTailNZZE real w K x (next x))
    (nextPlaced : next x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping [] x fin := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, _, _, _, _, _, _, _, _, ev⟩ :=
    TranslateStepV.BranchX.entry_branch_next_XE real spec config rows mapping w K x inv.v2.v1.pins (next x)
      (offset (k + 1)) tail inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio
      obligations.present obligations.perAcc obligations.code nodup
  exact ⟨fin, run, ev⟩

#print axioms branch_vholdsGE
#print axioms evob_of_route
#print axioms ct_of_evob
#print axioms class_vholdsGE
end ArmCertPipe
