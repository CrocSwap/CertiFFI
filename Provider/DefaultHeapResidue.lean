-- Lift each actual current-profile successor through the signed heap value and ABI relations.
import HeapBranchStep
import HeapV2StepCerts.Residue.Core
import DefaultHeapCode
import DefaultHeapEntryMem

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryClassNext
open HeapV2StepCerts

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapResidue

structure Inv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (initial : NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (q : ValBind.Inputs) (v19 v30 : BitVec 64) (k : Nat) (x : NativeState) : Prop where
  body : DefaultHeapEntryMem.HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue initial capacity drawsBefore k x
  valBind : ValBind.ValBind q k x
  lr : RtSaved2.LrField p mapping base v19 v30 k x
  residue : RtBl.CallerInv.CallerResidue x

theorem controls {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase base : BitVec 64} {offset : Nat → BitVec 64}
    {budget : Nat} {p : HeapV2E17.Pins}
    {catalogue : NativeMteTagCheck.ControlCatalogue} {initial : NativeState}
    {capacity : Nat} {drawsBefore : Nat → Nat} {q : ValBind.Inputs} {v19 v30 : BitVec 64}
    {k : Nat} {x : NativeState} (inv : Inv spec config rows mapping m scope image loadBase base offset budget p catalogue initial capacity drawsBefore q v19 v30 k x) :
    NativeEntryCallerParts.CallerControls x where
  f4 := inv.body.core.v1.pins.f4
  f2 := inv.body.core.branch.base.hFeature_AA32EL2
  f3 := inv.body.core.branch.base.hFeature_AA32EL3
  f6 := inv.body.core.branch.base.hFeature_AA64EL2
  f7 := inv.body.core.branch.base.hFeature_AA64EL3
  rme := inv.body.core.v1.pins.rme
  vhe := by have h := inv.body.core.branch.vhe; simpa [getElem!_pos] using h
  brbe := inv.body.core.branch.base.hFeature_BRBE
  el := inv.body.core.v1.pins.el
  nrw := inv.body.core.v1.pins.nrw
  e2h := inv.body.core.branch.base.hE2H
  tge := inv.body.core.branch.base.hTGE
  ns := inv.body.core.branch.base.hSCR_NS
  pmb := inv.body.core.branch.base.hPMB_E
  spe := inv.body.core.v1.pins.spe
  pmbs := inv.body.core.v1.pins.pmbs
  nspb := inv.body.core.branch.base.hNSPB
  nspbe := inv.body.core.branch.base.hNSPBE
  gcsEn := inv.residue

abbrev Step (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (records : List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (before after : NativeState → Prop) : Prop :=
  ∀ x, before x → ∃ fin, modelStep real x = .ok () fin ∧ after fin ∧
    fin.regs._Z = x.regs._Z ∧ StepEvents.EvShape spec mapping records x fin

#check "CURRENT_DECL HeapResidue.step_of_at"
theorem step_of_at (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (initial : NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (q : ValBind.Inputs) (v19 v30 : BitVec 64) (k : Nat)
    (R : NativeState → NativeState → Prop)
    (records : List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (at_ : ∀ x, Inv spec config rows mapping m scope image loadBase base offset budget p catalogue initial capacity drawsBefore q v19 v30 k x →
      ∃ fin, modelStep real x = .ok () fin ∧
        DefaultHeapEntryMem.HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue initial capacity drawsBefore (k + 1) fin ∧ R x fin)
    (vcarry : ∀ s f, RegBind.RegBind p k s → ValBind.ValBind q k s → R s f → ValBind.ValBind q (k + 1) f)
    (lcarry : ∀ s f, R s f → RtSaved2.LrField p mapping base v19 v30 k s → RtSaved2.LrField p mapping base v19 v30 (k + 1) f)
    (gcs : ∀ s f, R s f → ChainInvV4.GcsFrame s f)
    (entry : NativeState)
    (rcarry : ∀ s f, R s f → Residue.ResL p mapping base v19 v30 entry k s → Residue.ResL p mapping base v19 v30 entry (k + 1) f)
    (z : ∀ s f, R s f → f.regs._Z = s.regs._Z)
    (ev : ∀ s f, R s f → StepEvents.EvShape spec mapping records s f) :
    Step real spec mapping records
      (fun x => Inv spec config rows mapping m scope image loadBase base offset budget p catalogue initial capacity drawsBefore q v19 v30 k x ∧
        Residue.ResL p mapping base v19 v30 entry k x)
      (fun x => Inv spec config rows mapping m scope image loadBase base offset budget p catalogue initial capacity drawsBefore q v19 v30 (k + 1) x ∧
        Residue.ResL p mapping base v19 v30 entry (k + 1) x) := by
  intro x ⟨inv, res⟩
  obtain ⟨fin, run, body, rel⟩ := at_ x inv
  exact ⟨fin, run, ⟨⟨body, vcarry x fin inv.body.regBind inv.valBind rel, lcarry x fin rel inv.lr,
    RtBl.CallerInv.residue_carry (gcs x fin rel) inv.residue⟩, rcarry x fin rel res⟩,
    z x fin rel, ev x fin rel⟩

#print axioms step_of_at
#print axioms controls
end ReleaseProfile.DefaultHeapResidue
