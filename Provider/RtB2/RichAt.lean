-- POINTWISE rich branch/BL steps for ChainInv v4. Same proofs as rich-v2
-- (RtB2.RichG), with the step-state premises that need v4 fields (dec, CallerControls) and the tail given
-- at the step's own state x (inv : ChainInv3 k x) instead of quantified over ChainInv3.
import RtB2.RichG
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace RtB2.RichG
open HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false

theorem rich_branch_at (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int) (upd0 : HeapV2StepCerts.RegBind.upds k = []) (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (tail : HeapV2StepCerts.BranchStepV3.BranchTailAt real w K x (next x))
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
        ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) x fin ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
          fin.mem = x.mem ∧ fin.regs.gpr = x.regs.gpr ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) := by
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, gprEq, spEq, finMem, sys, gcs⟩ :=
    entry_class_next_v3_brG real spec config rows mapping w K x inv.v2.v1.pins (next x)
      (offset (k + 1)) tail inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩,
    HeapV2StepCerts.RegBind.carry_step hk (HeapV2StepCerts.BranchStepV3.keep_holds upd0 gprEq spEq) inv.regBind, ?_, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩,
    HeapV2StepCerts.BranchStepV3.keep_holds upd0 gprEq spEq, HeapV2StepCerts.ValBind.veff_none veff x fin, finMem, gprEq, gcs⟩
  · intro e he n hn i hi; rw [finMem]; exact inv.present e he n hn i hi
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [ChainInvV3.hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

theorem rich_branch_cbz_at (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = []) (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (Rt : BitVec 5) (imm19 : BitVec 19) (taken : Bool)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyCbz.W Rt imm19) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (dec : Crypto.CruxCbz.cbzC 1#1 Rt x ↔ taken = true)
    (hlow : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      (x.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (target : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      base + offset (k + 1) =
        (if taken then x.regs._PC + sign_extend (imm19 ++ 0#2) 64 else x.regs._PC + 4#64))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping (EntryBodyCbz.W Rt imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
        ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) x fin ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
          fin.mem = x.mem ∧ fin.regs.gpr = x.regs.gpr ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) := by
  refine rich_branch_at real spec config rows mapping m scope image loadBase separated base offset
    budget p k room hk page aligned (EntryBodyCbz.W Rt imm19) 118 upd0 veff (fun _ => base + offset (k + 1))
    x inv ?_ (fun _ _ => rfl) obligations
  intro fetched enc0 b pins bp input guard quiet it ss
  obtain ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, _, _, _, _, _, nonProj, _, pcS,
      gpr, spr, gic⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyCbz.native_tail_x real x fetched enc0 Rt imm19 noEret pins bp input guard b quiet it ss
      (hlow x inv)
  refine ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, gic, ?_, nonProj, gpr, spr⟩
  rw [pcS, target x inv]
  have d := dec
  cases taken
  · rw [if_neg (fun h => absurd (d.mp h) (by decide))]; rfl
  · rw [if_pos (d.mpr rfl)]; rfl

theorem rich_branch_bcond_at (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = []) (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (cond : BitVec 4) (imm19 : BitVec 19) (taken : Bool)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyBcond.W cond imm19) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (dec : Crypto.BcondCore.bcondC cond x.regs ↔ taken = true)
    (hlow : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      (x.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (target : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      base + offset (k + 1) =
        (if taken then x.regs._PC + sign_extend (imm19 ++ 0#2) 64 else x.regs._PC + 4#64))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping (EntryBodyBcond.W cond imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
        ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) x fin ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
          fin.mem = x.mem ∧ fin.regs.gpr = x.regs.gpr ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) := by
  refine rich_branch_at real spec config rows mapping m scope image loadBase separated base offset
    budget p k room hk page aligned (EntryBodyBcond.W cond imm19) 69 upd0 veff (fun _ => base + offset (k + 1))
    x inv ?_ (fun _ _ => rfl) obligations
  intro fetched enc0 b pins bp input guard quiet it ss
  obtain ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, _, _, _, _, _, nonProj, _, pcS,
      gpr, spr, gic⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyBcond.native_tail_x real x fetched enc0 cond imm19 noEret pins bp input guard b quiet it ss
      (hlow x inv)
  refine ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, gic, ?_, nonProj, gpr, spr⟩
  rw [pcS, target x inv]
  have d := dec
  cases taken
  · rw [if_neg (fun h => absurd (d.mp h) (by decide))]; rfl
  · rw [if_pos (d.mpr rfl)]; rfl

theorem rich_branch_ret_at (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = []) (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyRet.W Rn) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (hlow : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (target : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      x.regs.gpr[(GPRSummary.key Rn.toNat).val] = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping (EntryBodyRet.W Rn) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
        ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) x fin ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
          fin.mem = x.mem ∧ fin.regs.gpr = x.regs.gpr ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) := by
  refine rich_branch_at real spec config rows mapping m scope image loadBase separated base offset
    budget p k room hk page aligned (EntryBodyRet.W Rn) 94 upd0 veff (fun _ => base + offset (k + 1))
    x inv ?_ (fun _ _ => rfl) obligations
  intro fetched enc0 b pins bp input guard quiet it ss
  obtain ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, _, _, _, _, _, nonProj, _, pcS,
      gpr, spr, gic⟩ :=
    ArmBridge.CruxGenGuarded.EntryBodyRet.native_tail_x real x fetched enc0 Rn hRn noEret pins bp input guard b quiet it ss
      (hlow x inv)
  exact ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, gic, pcS.trans (target x inv), nonProj,
    gpr, spr⟩

theorem rich_bl_at (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm26 : BitVec 26) (upd : HeapV2StepCerts.RegBind.upds k = [(.x 30, .drop)]) (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (tail : BlTailAt real imm26 x (next x)) (controls : CallerControls x)
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
        ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) x fin ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
          fin.mem = x.mem ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) := by
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, gprEq, spEq, finMem, sys, gcs⟩ :=
    entry_class_next_v3_bl real spec config rows mapping imm26 x inv.v2.v1.pins (next x)
      (offset (k + 1)) tail controls inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩,
    HeapV2StepCerts.RegBind.carry_step hk (bl_holds upd gprEq spEq) inv.regBind, ?_, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩,
    bl_holds upd gprEq spEq, HeapV2StepCerts.ValBind.veff_none veff x fin, finMem, gcs⟩
  · intro e he n hn i hi; rw [finMem]; exact inv.present e he n hn i hi
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [ChainInvV3.hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms rich_branch_at
#print axioms rich_branch_cbz_at
#print axioms rich_branch_bcond_at
#print axioms rich_branch_ret_at
#print axioms rich_bl_at
end RtB2.RichG

namespace HeapV2StepCerts.RichG
open NativeEntryCallerParts
/-- One BL step from its plan word (generic in k). -/
theorem richBl_at_pt (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (k : Nat) (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (aligned : (ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf k).toNat % 4 = 0)
    (imm26 : BitVec 26) (upd : RegBind.upds k = [(.x 30, .drop)])
    (veff : HeapV2StepCerts.ValBind.effAt k = .none)
    (off wordNat : Nat) (member : (off, wordNat) ∈ HeapV2Plan.codeWords)
    (here : ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf k = BitVec.ofNat 64 (0x10278 + off))
    (wordEq : NativeEntryCallerDispatch.Bl.word imm26 = BitVec.ofNat 32 wordNat)
    (land : ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf k + sign_extend (imm26 ++ 0#2) 64 =
      ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (k + 1))
    (low : (base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (k + 1)).toNat < 2 ^ 55)
    (x : NativeState) (inv : ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins k x) (controls : CallerControls x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins (k + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds k) x fin ∧ HeapV2StepCerts.ValBind.VEff k x fin ∧
          fin.mem = x.mem ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) := by
  have placedNext : ∀ x, ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins k x →
      blTarget imm26 x = base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (k + 1) := by
    intro x inv
    rw [NativeEntryCallerRegisters.bl_target, inv.v2.v1.pc, BitVec.add_assoc, land]
  exact RtB2.RichG.rich_bl_at real spec config rows mapping _ codeScope (HeapV2.image base) base static.separated
    base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins k room hk page aligned imm26 upd veff
    (fun x => blTarget imm26 x) x inv
    (RtB2.RichG.bl_tail real imm26 x (by rw [placedNext x inv]; exact low))
    controls placedNext
    (fun x inv => MemNext.memFetch spec config rows mapping base budget k pins table static off wordNat
      member here _ wordEq x inv.v2)

/-- step 15 @+0x3c BL 0x9400003b (imm26 = 59: callee at entry offset 296) -/
theorem richBl_15_at (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 15 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (15 + 1)).toNat < 2 ^ 55)
    (x : NativeState) (inv : ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 15 x) (controls : CallerControls x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins (15 + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds 15) x fin ∧ HeapV2StepCerts.ValBind.VEff 15 x fin ∧
          fin.mem = x.mem ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) :=
  richBl_at_pt real spec config rows mapping base budget pins table static 15 room (by decide) page
    (by decide +kernel) (59#26) (by decide) (by decide) 60 2483028027 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) low x inv controls

/-- step 150 @+0x4c BL 0x9400004b (imm26 = 75: callee at entry offset 376) -/
theorem richBl_150_at (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 150 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (150 + 1)).toNat < 2 ^ 55)
    (x : NativeState) (inv : ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 150 x) (controls : CallerControls x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins (150 + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds 150) x fin ∧ HeapV2StepCerts.ValBind.VEff 150 x fin ∧
          fin.mem = x.mem ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) :=
  richBl_at_pt real spec config rows mapping base budget pins table static 150 room (by decide) page
    (by decide +kernel) (75#26) (by decide) (by decide) 76 2483028043 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) low x inv controls

/-- step 252 @+0x58 BL 0x9400004e (imm26 = 78: callee at entry offset 400) -/
theorem richBl_252_at (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (room : 252 < budget) (page : base.toNat % 4096 = 0)
    (low : (base + ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf (252 + 1)).toNat < 2 ^ 55)
    (x : NativeState) (inv : ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins 252 x) (controls : CallerControls x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmBridge.CruxGenGuarded.ChainInvV3.ChainInv3 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope (HeapV2.image base) base base ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf budget pins (252 + 1) fin ∧
        (HeapV2StepCerts.RegBind.Holds (HeapV2StepCerts.RegBind.upds 252) x fin ∧ HeapV2StepCerts.ValBind.VEff 252 x fin ∧
          fin.mem = x.mem ∧ fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3) :=
  richBl_at_pt real spec config rows mapping base budget pins table static 252 room (by decide) page
    (by decide +kernel) (78#26) (by decide) (by decide) 88 2483028046 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) low x inv controls

#print axioms richBl_at_pt
#print axioms richBl_15_at
#print axioms richBl_150_at
#print axioms richBl_252_at
end HeapV2StepCerts.RichG
