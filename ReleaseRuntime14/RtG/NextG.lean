-- RtG.NextG (, d200 /): the rich branch step over ArmCertPipe.ChainInvG (program-generic).
-- Same proof as RtB2.RichG.rich_branch_at, with the heap-v2 RegBind/ValBind/DataPresent part replaced by the
-- caller's  obligation, stated over the step's frame facts (fin is existential, so the caller gets them).
import ArmCertPipe.ChainInvG
import RtB2.RichG
import RtB3.RichH
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace RtG
open HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCertPipe RtB2.RichG RtB3.RichH
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false

/-- A branch step over ChainInvG: any branch tail (BranchTailAt) at x, the next PC placed at offset (k+1). -/
theorem nextG_branch (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int) (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (tail : HeapV2StepCerts.BranchStepV3.BranchTailAt real w K x (next x))
    (nextPlaced : next x = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping w x)
    (hextra : ∀ fin, modelStep real x = .ok () fin → fin.mem = x.mem → fin.regs.gpr = x.regs.gpr →
      fin.regs.SP_EL0 = x.regs.SP_EL0 → extra (k + 1) fin) :
    ∃ fin, modelStep real x = .ok () fin ∧
        ChainInvG spec config rows mapping m scope image loadBase base offset budget extra (k + 1) fin ∧
        fin.mem = x.mem ∧ fin.regs.gpr = x.regs.gpr ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧
        fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3 := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, gprEq, spEq, finMem, sys, gcs⟩ :=
    entry_class_next_v3_brG real spec config rows mapping w K x inv.v2.v1.pins (next x)
      (offset (k + 1)) tail inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache, hextra fin run finMem gprEq spEq⟩,
    finMem, gprEq, spEq, gcs⟩
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [ChainInvV3.hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms nextG_branch

/-- A BL step over ChainInvG (BlTailAtL tail, caller controls), x30 := PC + 4. -/
theorem nextG_bl (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm26 : BitVec 26) (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (tail : BlTailAtL real imm26 x (next x)) (controls : CallerControls x)
    (nextPlaced : next x = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x)
    (hextra : ∀ fin, modelStep real x = .ok () fin → fin.mem = x.mem → (∃ v, fin.regs.gpr = x.regs.gpr.set 30 v) →
      fin.regs.gpr[30] = x.regs._PC + 4#64 → fin.regs.SP_EL0 = x.regs.SP_EL0 → extra (k + 1) fin) :
    ∃ fin, modelStep real x = .ok () fin ∧
        ChainInvG spec config rows mapping m scope image loadBase base offset budget extra (k + 1) fin ∧
        fin.mem = x.mem ∧ (∃ v, fin.regs.gpr = x.regs.gpr.set 30 v) ∧ fin.regs.gpr[30] = x.regs._PC + 4#64 ∧
        fin.regs.SP_EL0 = x.regs.SP_EL0 ∧
        fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3 := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, gprEq, lrEq, spEq, finMem, sys, gcs⟩ :=
    entry_class_next_v3_blL real spec config rows mapping imm26 x inv.v2.v1.pins (next x)
      (offset (k + 1)) tail controls inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned nextPlaced
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache, hextra fin run finMem gprEq lrEq spEq⟩,
    finMem, gprEq, lrEq, spEq, gcs⟩
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [ChainInvV3.hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

/-- A RET Xn step over ChainInvG (the actual EntryBodyRet native tail), target X[Rn] placed at offset (k+1). -/
theorem nextG_ret (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyRet.W Rn) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (hlow : (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (target : x.regs.gpr[(GPRSummary.key Rn.toNat).val] = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (EntryBodyRet.W Rn) x)
    (hextra : ∀ fin, modelStep real x = .ok () fin → fin.mem = x.mem → fin.regs.gpr = x.regs.gpr →
      fin.regs.SP_EL0 = x.regs.SP_EL0 → extra (k + 1) fin) :
    ∃ fin, modelStep real x = .ok () fin ∧
        ChainInvG spec config rows mapping m scope image loadBase base offset budget extra (k + 1) fin ∧
        fin.mem = x.mem ∧ fin.regs.gpr = x.regs.gpr ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧
        fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3 := by
  refine nextG_branch real spec config rows mapping m scope image loadBase separated base offset budget extra k
    room page aligned (EntryBodyRet.W Rn) 94 (fun _ => base + offset (k + 1)) x inv ?_ rfl ob hextra
  intro fetched enc0 b pins bp input guard quiet it ss
  obtain ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, _, _, _, _, _, nonProj, _, pcS,
      gpr, spr, gic⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyRet.native_tail_x real x fetched enc0 Rn hRn noEret pins bp input guard b quiet it ss
      hlow
  exact ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, gic, pcS.trans target, nonProj,
    gpr, spr⟩

#print axioms nextG_bl
#print axioms nextG_ret
end RtG
