-- (H-P13): the shim-state invariant and the generic shim CLASS step. ShimInv is ChainInv v3
-- without the body's RegBind/DataPresent (the shim has its own few registers; its one data access is the
-- slot at the body SP pin): ChainInv2 over the shim offsets + raw table image, no-update rows, PostRegs2,
-- mode, debug, features, dcache. plan_shim_class = Core's plan_step3_class over ShimInv for a fixed-class
-- shim step with a ClassTailVAt tail (shim tails: BtiC/MrsDit/DitOn/IsbSy/MsrDit, and the
-- SubSp64/AddSpRestore class tails), exporting the step's Holds us and memory frame.
import Bridge.CruxGenGuarded.ChainInvV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace RtShim2

structure ShimInv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (k : Nat) (x : NativeState) : Prop where
  v2 : ChainInv2 spec config rows mapping m scope image loadBase base offset budget k x
  raw : RawImageAt spec.imageRows x.mem
  noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
    NoUpdateRows {spec.params with haft := hostHAFT x.regs} acc spec.imageRows = true
  post2 : MemM1.MemReadD2.PostRegs2 x.regs
  mode : HostEL0ModeAt x.regs
  debug : ExistingE11DebugAt x.regs
  feat : x.regs.FeatureImpl[7] = true ∧ x.regs.FeatureImpl[3] = false ∧
    x.regs.FeatureImpl[227] = false ∧ x.regs.FeatureImpl[111] = true
  dcache : currentDCache x.regs = true

/-- One actual fixed-class shim step: ShimInv k → ShimInv (k+1), exporting Holds us and fin.mem = x.mem. -/
theorem plan_shim_class (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (us : List (HeapV2StepCerts.RegBind.Reg × HeapV2StepCerts.RegBind.Upd))
    (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ShimInv spec config rows mapping m scope image loadBase base offset budget k x)
    (tail : HeapV2StepCerts.RegVal.ClassTailVAt real w writes K x (next x) us)
    (nextPlaced : next x = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ShimInv spec config rows mapping m scope image loadBase base offset budget (k + 1) fin ∧
      HeapV2StepCerts.RegBind.Holds us x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, holds, finMem, sys⟩ :=
    ArmBridge.CruxGenGuarded.ClassNextV3.entry_class_next_v3 real spec config rows mapping w writes K x inv.v2.v1.pins (next x)
      (offset (k + 1)) us tail inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩, holds, finMem, sys⟩
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms plan_shim_class
end RtShim2
