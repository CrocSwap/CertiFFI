-- Common heap/runtime continuation state for the MTE2-on profile.
import Bridge.CruxGenGuarded.ChainInv
import ArmCertTranslateModel.C9FetchBinding
import ArmCertWalk.IFetchElSs
import ArmCertWalk.AccessTransfer
import TranslateSpan.BranchMTE2
import DefaultShimClassNext
import DefaultScalarTrace
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

namespace ReleaseProfile.DefaultHeapShimClass
open DefaultCurrent
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
    (nextPlaced : next x = base + offset (k + 1)) (ob : FetchObligations spec config rows mapping w x)
    (tailChoice : DefaultScalarTrace.TailChoiceAt real x w) :
    ∃ fin, modelStep real x = .ok () fin ∧
      CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      HeapV2StepCerts.RegBind.Holds us x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧ RtPremC.CtlRel spec x fin ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed,
      holds, finMem, sys, _, br, tag, control⟩ :=
    DefaultShimClassNext.entry_class_next real spec config rows mapping w writes K x
      inv.v1.pins (next x) (offset (k + 1)) us tail inv.v1.gic inv.v1.features inv.v1.debug
      (budget - (k + 1)) hq base (offset k) inv.v1.pc page aligned nextPlaced inv.v1.current m
      inv.closed scope image loadBase inv.placed separated inv.raw inv.noUpd
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  have choice := DefaultScalarTrace.step_choice real spec config rows mapping m scope image loadBase
    base offset budget catalogue k room page aligned w x fin inv ob tailChoice run
  refine ⟨fin, run, ⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed,
    TranslateSpan.BranchMTE2.pins_step x fin inv.branch sys pins br, ?_, ?_, postFrame sys inv.post,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache,
    ReleaseProfile.DefaultActionControls.controls_of_sys inv.controls sys tag⟩, holds, finMem, sys, control, choice⟩
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [haftFrame sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat


#print axioms classStep
end ReleaseProfile.DefaultHeapShimClass
