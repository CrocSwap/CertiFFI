-- Transport the existing feature-only shim profiles from the initial state.
import DitShim243.Choice
import HeapControl
import DefaultHeapShimClass
import DefaultHeapShimEffects
import DitShim243.Utils

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option maxRecDepth 512

open ReleaseProfile
namespace DitShim243.Profiles

theorem features {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {source after : NativeState} (control : RtPremC.CtlRel spec source after) :
    after.regs.FeatureImpl = source.regs.FeatureImpl :=
  congrArg Prod.fst control.1

theorem mrs {source after : NativeState} (profile : NativeEntryAdapters.MrsDit.Profile source)
    (same : after.regs.FeatureImpl = source.regs.FeatureImpl) :
    NativeEntryAdapters.MrsDit.Profile after where
  dit := by rw [same]; exact profile.dit
  bti := by rw [same]; exact profile.bti
  tme := by rw [same]; exact profile.tme

theorem dit_on {source after : NativeState} (profile : NativeEntryAdapters.MrsDit.Profile source)
    (same : after.regs.FeatureImpl = source.regs.FeatureImpl) :
    NativeEntryAdapters.DitOn.Profile after where
  dit := by rw [same]; exact profile.dit
  bti := by rw [same]; exact profile.bti
  tme := by rw [same]; exact profile.tme

theorem isb {source after : NativeState} (profile : NativeEntryAdapters.IsbSy.Profile source)
    (same : after.regs.FeatureImpl = source.regs.FeatureImpl) :
    NativeEntryAdapters.IsbSy.Profile after where
  aa32el2 := by rw [same]; exact profile.aa32el2
  aa32el3 := by rw [same]; exact profile.aa32el3
  aa64el2 := by rw [same]; exact profile.aa64el2
  aa64el3 := by rw [same]; exact profile.aa64el3
  brbe := by rw [same]; exact profile.brbe

theorem msr {source after : NativeState}
    (mrsProfile : NativeEntryAdapters.MrsDit.Profile source)
    (isbProfile : NativeEntryAdapters.IsbSy.Profile source)
    (same : after.regs.FeatureImpl = source.regs.FeatureImpl) :
    NativeEntryAdapters.MsrDit.Profile after where
  dit := by rw [same]; exact mrsProfile.dit
  bti := by rw [same]; exact mrsProfile.bti
  tme := by rw [same]; exact mrsProfile.tme
  aa32el2 := by rw [same]; exact isbProfile.aa32el2
  aa32el3 := by rw [same]; exact isbProfile.aa32el3
  aa64el2 := by rw [same]; exact isbProfile.aa64el2
  aa64el3 := by rw [same]; exact isbProfile.aa64el3

theorem caller_controls {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase base : BitVec 64} {offset : Nat → BitVec 64}
    {budget k : Nat} {catalogue : NativeMteTagCheck.ControlCatalogue} {x : NativeState}
    (core : DefaultCurrent.CurrentInv spec config rows mapping consumer scope image loadBase
      base offset budget k catalogue x) (residue : RtBl.CallerInv.CallerResidue x) :
    NativeEntryCallerParts.CallerControls x where
  f4 := core.v1.pins.f4
  f2 := core.branch.base.hFeature_AA32EL2
  f3 := core.branch.base.hFeature_AA32EL3
  f6 := core.branch.base.hFeature_AA64EL2
  f7 := core.branch.base.hFeature_AA64EL3
  rme := core.v1.pins.rme
  vhe := by have h := core.branch.vhe; simpa [getElem!_pos] using h
  brbe := core.branch.base.hFeature_BRBE
  el := core.v1.pins.el
  nrw := core.v1.pins.nrw
  e2h := core.branch.base.hE2H
  tge := core.branch.base.hTGE
  ns := core.branch.base.hSCR_NS
  pmb := core.branch.base.hPMB_E
  spe := core.v1.pins.spe
  pmbs := core.v1.pins.pmbs
  nspb := core.branch.base.hNSPB
  nspbe := core.branch.base.hNSPBE
  gcsEn := residue

theorem class_gcs (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase base : BitVec 64)
    (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (us : List (HeapV2StepCerts.RegBind.Reg × HeapV2StepCerts.RegBind.Upd))
    (x : NativeState) (core : DefaultCurrent.CurrentInv spec config rows mapping consumer scope image loadBase
      base offset budget k catalogue x)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (tail : HeapV2StepCerts.RegVal.ClassTailVAt real w writes K x (x.regs._PC + 4#64) us)
    (ob : ArmBridge.CruxGenGuarded.ChainInv.FetchObligations spec config rows mapping w x)
    (fin : NativeState) (run : modelStep real x = .ok () fin) :
    fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3 := by
  have hq : ArmCert.HookQuiet.V0.HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]
    exact core.v1.quiet
  have placed : x.regs._PC + 4#64 = base + (x.regs._PC + 4#64 - base) := by
    exact ((BitVec.add_comm base (x.regs._PC + 4#64 - base)).trans
      (BitVec.sub_add_cancel _ _)).symm
  obtain ⟨other, actual, _, _, _, _, _, _, _, _, _, _, _, _, gcs, _, _, _⟩ :=
    DefaultShimClassNext.entry_class_next real spec config rows mapping w writes K x core.v1.pins
      (x.regs._PC + 4#64) (x.regs._PC + 4#64 - base) us tail core.v1.gic core.v1.features core.v1.debug
      (budget - (k + 1)) hq base (offset k) core.v1.pc page aligned placed core.v1.current
      consumer core.closed scope image loadBase core.placed separated core.raw core.noUpd
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  have same := actual.symm.trans run
  cases same
  exact gcs

set_option maxHeartbeats 150000 in
theorem saved_dit (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase base : BitVec 64)
    (offset : Nat → BitVec 64) (budget : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (i0 : DefaultCurrent.CurrentInv spec config rows mapping consumer scope image loadBase base offset budget 0 catalogue entry)
    (i1 : DefaultCurrent.CurrentInv spec config rows mapping consumer scope image loadBase base offset budget 1 catalogue (stateAt real entry 1))
    (i2 : DefaultCurrent.CurrentInv spec config rows mapping consumer scope image loadBase base offset budget 2 catalogue (stateAt real entry 2))
    (room : 3 ≤ budget) (page : base.toNat % 4096 = 0) (aligned : ∀ j, j ≤ 2 → (offset j).toNat % 4 = 0)
    (ob0 : ArmBridge.CruxGenGuarded.ChainInv.FetchObligations spec config rows mapping NativeEntryDispatch.BtiC.word entry)
    {w1 : BitVec 32} {writes1 : NativeEntry.Effects.Writes} {K1 : Int}
    {us1 : List (HeapV2StepCerts.RegBind.Reg × HeapV2StepCerts.RegBind.Upd)}
    (tail1 : HeapV2StepCerts.RegVal.ClassTailVAt real w1 writes1 K1 (stateAt real entry 1)
      ((stateAt real entry 1).regs._PC + 4#64) us1)
    (hw1 : writes1.dit = false)
    (ob1 : ArmBridge.CruxGenGuarded.ChainInv.FetchObligations spec config rows mapping w1 (stateAt real entry 1))
    (prof2 : NativeEntryAdapters.MrsDit.Profile (stateAt real entry 2))
    (ob2 : ArmBridge.CruxGenGuarded.ChainInv.FetchObligations spec config rows mapping
      (NativeEntryDispatch.MrsDit.word 9#5) (stateAt real entry 2)) :
    (stateAt real entry 3).regs.gpr[9].extractLsb 24 24 = entry.regs.PSTATE.DIT := by
  have d1 : (stateAt real entry 1).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
    obtain ⟨fin, run, dit, _, _⟩ := DefaultHeapShimEffects.shim_class real spec config rows mapping consumer scope image
      loadBase base offset budget 0 catalogue (by omega) page (aligned 0 (by omega)) (stateAt real entry 0) i0
      (NativeShimTails.btiC_tailVAt real entry) rfl ob0
    rw [RtDit.stateAt_succ_of run]
    exact dit
  have d2 : (stateAt real entry 2).regs.PSTATE.DIT = (stateAt real entry 1).regs.PSTATE.DIT := by
    obtain ⟨fin, run, dit, _, _⟩ := DefaultHeapShimEffects.shim_class real spec config rows mapping consumer scope image
      loadBase base offset budget 1 catalogue (by omega) page (aligned 1 (by omega)) _ i1 tail1 hw1 ob1
    rw [RtDit.stateAt_succ_of run]
    exact dit
  obtain ⟨fin, run, saved, _, _⟩ := DefaultHeapShimEffects.shim_mrs9 real spec config rows mapping consumer scope image
    loadBase base offset budget 2 catalogue (by omega) page (aligned 2 (by omega)) _ i2 prof2 ob2
  have encoded : (stateAt real entry 3).regs.gpr[9] = (0#39 +++ (stateAt real entry 2).regs.PSTATE.DIT) +++ 0#24 := by
    rw [RtDit.stateAt_succ_of run]
    exact saved
  rw [encoded, d2, d1, DitShim243.Utils.enc_bit]

#print axioms saved_dit

#print axioms caller_controls
#print axioms class_gcs

#print axioms features
#print axioms mrs
#print axioms dit_on
#print axioms isb
#print axioms msr
end DitShim243.Profiles
