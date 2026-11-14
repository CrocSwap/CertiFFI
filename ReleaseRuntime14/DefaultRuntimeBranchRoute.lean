-- Event-bearing branch step over the common current invariant.
import DefaultRuntimeBranchEvent
import DefaultRuntimeMemory
import TranslateStepV.BranchX
import Bridge.CruxGenGuarded.ChainInvV3

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCertWalk ArmCert.Translate.Model
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultRuntime
#check "CURRENT_DECL branchEventStep"
theorem branchEventStep (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int)
    (next : NativeState → BitVec 64)
    (x : NativeState) (inv : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (tail : ReleaseProfile.DefaultRuntimeBranchEvent.BranchTailEvent real w K x (next x))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (nextPlaced : next x = base + offset (k + 1)) (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem ∧
      SysEq2 x.regs fin.regs ∧ fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping [] x fin ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed,
      gpr, sp, finMem, sys, br, tag, n, zf, c, v, z, dit, events, _, choice⟩ :=
    ReleaseProfile.DefaultRuntimeBranchEvent.entry_branch_event real spec config rows mapping w K x
      inv.v1.pins (next x) (offset (k + 1)) tail inv.v1.gic inv.v1.features inv.v1.debug
      (budget - (k + 1)) hq base (offset k) inv.v1.pc page aligned nextPlaced inv.v1.current m
      inv.closed scope image loadBase inv.placed separated inv.branch inv.raw inv.noUpd
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code nodup
  refine ⟨fin, run, ⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed,
    TranslateSpan.BranchMTE2.pins_step x fin inv.branch sys pins br, ?_, ?_, DefaultCurrent.postFrame sys inv.post,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache,
    DefaultActionControls.controls_of_sys inv.controls sys tag⟩, TranslateStepV.BranchX.vholds_nil gpr sp n zf c v, finMem, sys, z, dit, events, choice⟩
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms branchEventStep
#check "CURRENT_DECL branchEventExit"
theorem branchEventExit (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int)
    (next : NativeState → BitVec 64)
    (x : NativeState) (inv : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (tail : ReleaseProfile.DefaultRuntimeBranchEvent.BranchTailEvent real w K x (next x))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      fin.regs._PC = next x ∧
      ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem ∧
      SysEq2 x.regs fin.regs ∧ fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping [] x fin ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  have placed : next x = base + (next x - base) := by
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  obtain ⟨fin, run, _, _, _, pc, _, _, _, _, _, gpr, sp, mem, sys, _, _, n, zf, c, v, z, dit, events, _, choice⟩ :=
    ReleaseProfile.DefaultRuntimeBranchEvent.entry_branch_event real spec config rows mapping w K x
      inv.v1.pins (next x) (next x - base) tail inv.v1.gic inv.v1.features inv.v1.debug
      (budget - (k + 1)) hq base (offset k) inv.v1.pc page aligned placed inv.v1.current m
      inv.closed scope image loadBase inv.placed separated inv.branch inv.raw inv.noUpd
      ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code nodup
  exact ⟨fin, run, pc.trans placed.symm, TranslateStepV.BranchX.vholds_nil gpr sp n zf c v,
    mem, sys, z, dit, events, choice⟩

#print axioms branchEventExit
end ReleaseProfile.DefaultRuntime
