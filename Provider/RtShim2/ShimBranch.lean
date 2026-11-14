-- (H-P13,): the shim's control-flow steps over ShimInv. Each re-anchors the
-- invariant at an arbitrary (offset', budget', k') whose PC is the branch target (budget' - k' = budget - (k+1)):
--   plan_shim_bl  : s6 BL into the body (X30 := PC+4; other GPRs/SP/mem kept),
--   plan_shim_ret : RET Rn (s10 exit to the caller, or the body's final RET 357 back into the shim at s7),
-- plus the ChainInv3 ↔ ShimInv bridges (body = ShimInv + RegBind + DataPresent). Fetch obligations are
-- hypotheses (: (A), synthetic instance after the relink).
import RtShim2.ShimInv
import RtBranch.BranchStepV3Classes
import RtB6.RichZ
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace RtShim2.ShimBranch

/-- The body invariant projects to the shim invariant. -/
theorem shimInv_of_chainInv3 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
    {base : BitVec 64} {offset : Nat → BitVec 64} {budget : Nat} {p : HeapV2E17.Pins} {k : Nat} {x : NativeState}
    (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x) :
    RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset budget k x :=
  { v2 := inv.v2, raw := inv.raw, noUpd := inv.noUpd, post2 := inv.post2, mode := inv.mode,
    debug := inv.debug, feat := inv.feat, dcache := inv.dcache }

/-- The shim invariant plus the body's register binding and data presence is the body invariant. -/
theorem chainInv3_of_shimInv {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
    {base : BitVec 64} {offset : Nat → BitVec 64} {budget : Nat} {p : HeapV2E17.Pins} {k : Nat} {x : NativeState}
    (inv : RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset budget k x)
    (regBind : HeapV2StepCerts.RegBind.RegBind p k x) (present : HeapV2StepCerts.C3.DataPresent p mapping x) :
    ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x :=
  { v2 := inv.v2, regBind := regBind, present := present, raw := inv.raw, noUpd := inv.noUpd,
    post2 := inv.post2, mode := inv.mode, debug := inv.debug, feat := inv.feat, dcache := inv.dcache }

run_cmd do
  IO.eprintln "CURRENT_DECL RtShim2.ShimBranch.plan_shim_bl"
  (← IO.getStderr).flush

/-- s6: BL into the body. -/
theorem plan_shim_bl (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (imm26 : BitVec 26)
    (x : NativeState) (inv : RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset budget k x)
    (low : (blTarget imm26 x).toNat < 2 ^ 55) (controls : CallerControls x)
    (offset' : Nat → BitVec 64) (budget' k' : Nat) (hb : budget' - k' = budget - (k + 1))
    (nextPlaced : blTarget imm26 x = base + offset' k')
    (ob : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset' budget' k' fin ∧
      fin.regs.gpr = x.regs.gpr.set 30 (x.regs._PC + 4#64) ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧
      fin.mem = x.mem ∧ SysEq2 x.regs fin.regs := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, ⟨v, gprEq⟩, x30, spEq,
      finMem, sys, _, _, _⟩ :=
    RtB6.RichZ.entry_class_next_v3_blE real spec config rows mapping imm26 x inv.v2.v1.pins (blTarget imm26 x)
      (offset' k') (RtB6.RichZ.bl_tailE real imm26 x low) controls inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd nodup ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  have hv : v = x.regs._PC + 4#64 := by
    rw [gprEq] at x30; simpa using x30
  subst hv
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, by rw [hb]; exact quiet, gic, pc⟩, closed, placed, bp⟩, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩, gprEq, spEq, finMem, sys⟩
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

run_cmd do
  IO.eprintln "CURRENT_DECL RtShim2.ShimBranch.plan_shim_ret"
  (← IO.getStderr).flush

/-- RET Rn to X[Rn] = base + offset' k': the shim's s10 exit, or the body's final RET back into the shim. -/
theorem plan_shim_ret (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset budget k x)
    (hlow : (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (offset' : Nat → BitVec 64) (budget' k' : Nat) (hb : budget' - k' = budget - (k + 1))
    (target : x.regs.gpr[(GPRSummary.key Rn.toNat).val] = base + offset' k')
    (ob : FetchObligations spec config rows mapping (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      RtShim2.ShimInv spec config rows mapping m scope image loadBase base offset' budget' k' fin ∧
      fin.regs.gpr = x.regs.gpr ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧
      fin.mem = x.mem ∧ SysEq2 x.regs fin.regs := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  have tail : HeapV2StepCerts.BranchStepV3.BranchTailAt real (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) 94 x (base + offset' k') := by
    intro fetched enc0 b pins bp input guard quiet it ss
    obtain ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, _, _, _, _, _, nonProj, _, pcS,
        gpr, spr, gic⟩ :=
      ArmBridge.CruxGenGuarded.EntryBodyRet.native_tail_x real x fetched enc0 Rn hRn noEret pins bp input guard b quiet it ss hlow
    exact ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, gic, pcS.trans target, nonProj, gpr, spr⟩
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, gprEq, spEq, finMem, sys⟩ :=
    HeapV2StepCerts.BranchStepV3.entry_class_next_v3_br real spec config rows mapping (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) 94 x
      inv.v2.v1.pins (base + offset' k') (offset' k') tail inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned rfl
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, by rw [hb]; exact quiet, gic, pc⟩, closed, placed, bp⟩, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩, gprEq, spEq, finMem, sys⟩
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms shimInv_of_chainInv3
#print axioms chainInv3_of_shimInv
#print axioms plan_shim_bl
#print axioms plan_shim_ret
end RtShim2.ShimBranch
