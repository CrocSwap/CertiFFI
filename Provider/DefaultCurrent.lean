-- Common heap/runtime continuation state for the MTE2-on profile.
import Bridge.CruxGenGuarded.ChainInv
import ArmCertTranslateModel.C9FetchBinding
import ArmCertWalk.IFetchElSs
import ArmCertWalk.AccessTransfer
import TranslateSpan.BranchMTE2
import ClassNext
import NativeMte2.Control
import HeapV2StepCerts.MemConfigFrame
import DefaultActionControls

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCertWalk ArmCert.Translate.Model
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.HookQuiet.V0 (HookQuiet)

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultCurrent

/-- Current state shared by the shim and the body. Program-specific facts,
    such as the register binding, are added by the body invariant. -/
structure CurrentInv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (x : NativeState) : Prop where
  v1 : ChainInv spec config rows base offset budget k x
  closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState x)
  placed : MemReloc.ImageOn scope image x loadBase mapping
  branch : TranslateSpan.BranchMTE2.Pins x
  raw : RawImageAt spec.imageRows x.mem
  noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
    NoUpdateRows {spec.params with haft := hostHAFT x.regs} acc spec.imageRows = true
  post : MemM1.MemReadD.PostRegs x.regs
  mode : HostEL0ModeAt x.regs
  debug : ExistingE11DebugAt x.regs
  feat : x.regs.FeatureImpl[7] = true ∧ x.regs.FeatureImpl[3] = false ∧
    x.regs.FeatureImpl[227] = false ∧ x.regs.FeatureImpl[111] = true
  dcache : currentDCache x.regs = true
  controls : NativeMteTagCheck.DefaultAt catalogue x

theorem postFrame {r r' : Regs} (sys : SysEq2 r r') (post : MemM1.MemReadD.PostRegs r) :
    MemM1.MemReadD.PostRegs r' :=
  ⟨sys.spe ▸ post.spe, sys.el ▸ post.el0, sys.nrw ▸ post.nrw, sys.feat ▸ post.noRME,
    sys.feat ▸ post.vhe, sys.feat ▸ post.aa64el0, sys.scr ▸ post.ns,
    sys.hcr ▸ post.e2h, sys.hcr ▸ post.tge, sys.sctlr ▸ post.e0e⟩

private theorem haftFrame {r r' : Regs} (sys : SysEq2 r r') : hostHAFT r' = hostHAFT r := by
  simp only [hostHAFT, hostHA, hostTCR2Enabled, sys.feat, sys.tcr, sys.tcr2, sys.scr]
  rfl

#check "CURRENT_DECL classStep"
theorem classStep (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (us : List (HeapV2StepCerts.RegBind.Reg × HeapV2StepCerts.RegBind.Upd))
    (next : NativeState → BitVec 64)
    (x : NativeState) (inv : CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (tail : HeapV2StepCerts.RegVal.ClassTailVAt real w writes K x (next x) us)
    (nextPlaced : next x = base + offset (k + 1)) (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      HeapV2StepCerts.RegBind.Holds us x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed,
      holds, finMem, sys, _, br, tag⟩ :=
    ReleaseProfile.ClassNext.entry_class_next real spec config rows mapping w writes K x
      inv.v1.pins (next x) (offset (k + 1)) us tail inv.v1.gic inv.v1.features inv.v1.debug
      (budget - (k + 1)) hq base (offset k) inv.v1.pc page aligned nextPlaced inv.v1.current m
      inv.closed scope image loadBase inv.placed separated inv.raw inv.noUpd
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed,
    TranslateSpan.BranchMTE2.pins_step x fin inv.branch sys pins br, ?_, ?_, postFrame sys inv.post,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache,
    ReleaseProfile.DefaultActionControls.controls_of_sys inv.controls sys tag⟩, holds, finMem, sys⟩
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [haftFrame sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

/-- Fetch obligations of the step at x, generic in the program. -/
def fetchG {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue) (x : NativeState)
    (inv : CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (off : Nat) (w : BitVec 32)
    (pcImage : x.regs._PC = MemReloc.imageAddress loadBase off)
    (inside : ∀ i < 4, scope (off + i)) (contiguous : ImageWordContiguous mapping loadBase off)
    (mmio : MappedNotMMIO mapping (MemReloc.imageAddress loadBase off))
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (imageWord : ∀ i < 4, image (off + i) = some (w.extractLsb' (8 * i) 8))
    (permit : ∀ acc, FetchShape acc → m.permitted x.regs._PC acc true 4) :
    FetchObligations spec config rows mapping w x :=
  have facts := ArmBridge.CruxGenGuarded.EntryActualFetch.before_fetch_facts x
    (NativeEntryTail.EntryPins.of_scalar x inv.v1.pins) inv.v1.features inv.v1.debug
  have el := facts.2.1
  have mode := facts.2.2.2.2.2.2.1
  have ep := NativeEntryTail.EntryPins.of_scalar x inv.v1.pins
  have rme : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.FeatureImpl[232] = false := by
    show x.regs.FeatureImpl[232] = false; simpa using ep.rme
  have nrw : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.PSTATE.nRW = 0#1 := by
    show x.regs.PSTATE.nRW = 0#1; simpa using ep.nrw
  { queryOf := fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩
    rawOf := fun _ => rfl
    vaOf := fun _ => rfl
    mmio := by rw [pcImage]; exact mmio
    present := mapped_bytes_present_of_image_on inv.placed pcImage inside contiguous
    perAcc := by
      intro acc actual
      obtain ⟨acctype, read, write, tagaccess, transactional, nonfault, contiguous', firstfault, first, ls64⟩ :=
        actual_ifetch_flags actual
      obtain ⟨hel, hss⟩ := actual_ifetch_el_ss actual rme nrw inv.v1.features.b3 inv.v1.features.a3 el mode.ns
      have permitted : m.permitted (ArmBridge.CruxGenGuarded.beforeFetchState x).regs._PC acc true 4 :=
        permit acc ⟨acctype, hel, hss, read, write, tagaccess, transactional, nonfault, contiguous', firstfault,
          first, ls64⟩
      obtain ⟨⟨va, ⟨raw, aligned⟩, size⟩, hva, hraw, haligned, hsize, inDomain, data, current⟩ :=
        inv.closed _ acc true 4 permitted
      simp only at hva hraw haligned hsize
      subst hva hraw haligned hsize
      exact ⟨inDomain, data, current⟩
    code := c9_fetch_code spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState x) _ (fun _ => rfl)
      inv.placed separated pcImage inside contiguous w imageWord }

#print axioms fetchG
#print axioms postFrame
#print axioms classStep
end ReleaseProfile.DefaultCurrent
