-- The shim BL with current fetched controls and the exact link and DIT effects.
import DefaultHeapShimBl
import DefaultHeapShimBranch
import DefaultRetEventTail
import DefaultHeapEntryMem

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapShimControl

#check "CURRENT_DECL shim_bl"
theorem shim_bl (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) (imm26 : BitVec 26)
    (x : NativeState) (inv : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (low : (blTarget imm26 x).toNat < 2 ^ 55) (controls : CallerControls x)
    (target : blTarget imm26 x = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      fin.regs.gpr = x.regs.gpr.set 30 (x.regs._PC + 4#64) ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧
      fin.mem = x.mem ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping [] x fin ∧
      ChainInvV4.GcsFrame x fin ∧ RtPremC.CtlRel spec x fin ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp,
      gpr, sp, mem, sys, tco, _, gcs, events, control, choice, dit⟩ :=
    DefaultHeapShimBl.entry_bl real spec config rows mapping imm26 x inv.v1.pins (offset (k + 1)) low controls
      inv.v1.gic inv.v1.features inv.v1.debug (budget - (k + 1)) hq base (offset k) inv.v1.pc
      page aligned target inv.v1.current m inv.closed scope image loadBase inv.placed separated
      inv.branch inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc nodup ob.code
  refine ⟨fin, run, ⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp, ?_, ?_,
    postFrame sys inv.post, MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    MemConfigFrame.dcache sys.sctlr inv.dcache,
    DefaultActionControls.controls_of_sys inv.controls sys tco⟩,
    gpr, sp, mem, dit, events, gcs, control, choice⟩
  · rw [mem]; exact inv.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms shim_bl

#check "CURRENT_DECL shim_ret"
theorem shim_ret (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (x : NativeState) (inv : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (low : x.regs.gpr[30].toNat < 2 ^ 55)
    (target : x.regs.gpr[30] = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (EntryBodyRet.W 30#5) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      fin.regs.gpr = x.regs.gpr ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧
      fin.mem = x.mem ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping [] x fin ∧
      ChainInvV4.GcsFrame x fin ∧ RtPremC.CtlRel spec x fin ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  have tail := DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide)
    low (base + offset (k + 1)) target
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed,
      gpr, sp, mem, sys, bp, tco, _, _, _, _, _, events, gcs, control, choice, dit⟩ :=
    DefaultHeapShimBranch.entry_branch_event real spec config rows mapping (EntryBodyRet.W 30#5) 94
      x inv.v1.pins (base + offset (k + 1)) (offset (k + 1)) tail inv.v1.gic
      inv.v1.features inv.v1.debug (budget - (k + 1)) hq base (offset k) inv.v1.pc
      page aligned rfl inv.v1.current m inv.closed scope image loadBase inv.placed separated
      inv.branch inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code nodup
  refine ⟨fin, run, ⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed,
    TranslateSpan.BranchMTE2.pins_step x fin inv.branch sys pins bp, ?_, ?_,
    postFrame sys inv.post, MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    MemConfigFrame.dcache sys.sctlr inv.dcache,
    DefaultActionControls.controls_of_sys inv.controls sys tco⟩,
    gpr, sp, mem, dit, events, gcs, control, choice⟩
  · rw [mem]; exact inv.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms shim_ret
theorem shim_ret_between (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nextOffset : Nat → BitVec 64) (nextBudget nextIndex : Nat)
    (budgetEq : budget - (k + 1) = nextBudget - nextIndex)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (x : NativeState) (inv : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (low : x.regs.gpr[30].toNat < 2 ^ 55)
    (target : x.regs.gpr[30] = base + nextOffset nextIndex)
    (ob : FetchObligations spec config rows mapping (EntryBodyRet.W 30#5) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base nextOffset nextBudget nextIndex catalogue fin ∧
      fin.regs.gpr = x.regs.gpr ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧
      fin.mem = x.mem ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping [] x fin ∧
      ChainInvV4.GcsFrame x fin ∧ RtPremC.CtlRel spec x fin ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  have tail := DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide)
    low (base + nextOffset nextIndex) target
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed,
      gpr, sp, mem, sys, bp, tco, _, _, _, _, _, events, gcs, control, choice, dit⟩ :=
    DefaultHeapShimBranch.entry_branch_event real spec config rows mapping (EntryBodyRet.W 30#5) 94
      x inv.v1.pins (base + nextOffset nextIndex) (nextOffset nextIndex) tail inv.v1.gic
      inv.v1.features inv.v1.debug (budget - (k + 1)) hq base (offset k) inv.v1.pc
      page aligned rfl inv.v1.current m inv.closed scope image loadBase inv.placed separated
      inv.branch inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code nodup
  refine ⟨fin, run, ⟨⟨pins, features, debug, current, (by rw [← budgetEq]; exact quiet), gic, pc⟩, closed, placed,
    TranslateSpan.BranchMTE2.pins_step x fin inv.branch sys pins bp, ?_, ?_,
    postFrame sys inv.post, MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    MemConfigFrame.dcache sys.sctlr inv.dcache,
    DefaultActionControls.controls_of_sys inv.controls sys tco⟩,
    gpr, sp, mem, dit, events, gcs, control, choice⟩
  · rw [mem]; exact inv.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat


#print axioms shim_ret_between
end ReleaseProfile.DefaultHeapShimControl
