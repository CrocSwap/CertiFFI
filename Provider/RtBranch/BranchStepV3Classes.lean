-- per-class ACTUAL branch steps over ChainInv v3.
-- Each step fixes `taken : Bool`; the path condition is the explicit hypothesis `dec`, the landing
-- offset is `target`, and upds k = [] (all registers kept). RET covers internal returns only
-- (X[Rn] = base + offset (k+1)); the final RET is Core's Exit.exit_lands.
import RtBranch.BranchStepV3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace HeapV2StepCerts.BranchStepV3
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

run_cmd do
  IO.eprintln "CURRENT_DECL HeapV2StepCerts.BranchStepV3.plan_step3_branch_cbz"
  (← IO.getStderr).flush

/-- CBZ step (sf = 1): taken iff `cbzC 1#1 Rt x ↔ taken`, landing at `offset (k+1)`. -/
theorem plan_step3_branch_cbz (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = [])
    (Rt : BitVec 5) (imm19 : BitVec 19) (taken : Bool)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyCbz.W Rt imm19) 31 12 == 879088#20) = false)
    (dec : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      (Crypto.CruxCbz.cbzC 1#1 Rt x ↔ taken = true))
    (hlow : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      (x.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (target : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      base + offset (k + 1) =
        (if taken then x.regs._PC + sign_extend (imm19 ++ 0#2) 64 else x.regs._PC + 4#64))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping (EntryBodyCbz.W Rt imm19) x) :
    Uget.Chain.Step real (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)) := by
  refine plan_step3_branch real spec config rows mapping m scope image loadBase separated base offset
    budget p k room hk page aligned (EntryBodyCbz.W Rt imm19) 118 upd0 (fun _ => base + offset (k + 1))
    ?_ (fun _ _ => rfl) obligations
  intro x inv fetched enc0 b pins bp input guard quiet it ss
  obtain ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, _, _, _, _, _, nonProj, _, pcS,
      gpr, spr, gic⟩ :=
    EntryBodyCbz.native_tail_x real x fetched enc0 Rt imm19 noEret pins bp input guard b quiet it ss
      (hlow x inv)
  refine ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, gic, ?_, nonProj, gpr, spr⟩
  rw [pcS, target x inv]
  have d := dec x inv
  cases taken
  · rw [if_neg (fun h => absurd (d.mp h) (by decide))]; rfl
  · rw [if_pos (d.mpr rfl)]; rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HeapV2StepCerts.BranchStepV3.plan_step3_branch_bcond"
  (← IO.getStderr).flush

/-- B.cond step: taken iff `bcondC cond x.regs ↔ taken`, landing at `offset (k+1)`. -/
theorem plan_step3_branch_bcond (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = [])
    (cond : BitVec 4) (imm19 : BitVec 19) (taken : Bool)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyBcond.W cond imm19) 31 12 == 879088#20) = false)
    (dec : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      (Crypto.BcondCore.bcondC cond x.regs ↔ taken = true))
    (hlow : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      (x.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (target : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      base + offset (k + 1) =
        (if taken then x.regs._PC + sign_extend (imm19 ++ 0#2) 64 else x.regs._PC + 4#64))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping (EntryBodyBcond.W cond imm19) x) :
    Uget.Chain.Step real (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)) := by
  refine plan_step3_branch real spec config rows mapping m scope image loadBase separated base offset
    budget p k room hk page aligned (EntryBodyBcond.W cond imm19) 69 upd0 (fun _ => base + offset (k + 1))
    ?_ (fun _ _ => rfl) obligations
  intro x inv fetched enc0 b pins bp input guard quiet it ss
  obtain ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, _, _, _, _, _, nonProj, _, pcS,
      gpr, spr, gic⟩ :=
    EntryBodyBcond.native_tail_x real x fetched enc0 cond imm19 noEret pins bp input guard b quiet it ss
      (hlow x inv)
  refine ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, gic, ?_, nonProj, gpr, spr⟩
  rw [pcS, target x inv]
  have d := dec x inv
  cases taken
  · rw [if_neg (fun h => absurd (d.mp h) (by decide))]; rfl
  · rw [if_pos (d.mpr rfl)]; rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HeapV2StepCerts.BranchStepV3.plan_step3_branch_ret"
  (← IO.getStderr).flush

/-- Internal RET step (always taken): lands at `X[Rn] = base + offset (k+1)`. The program's final
RET is not this step; it is Core's `Exit.exit_lands`. -/
theorem plan_step3_branch_ret (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (upd0 : HeapV2StepCerts.RegBind.upds k = [])
    (Rn : BitVec 5) (hRn : Rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyRet.W Rn) 31 12 == 879088#20) = false)
    (hlow : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (target : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      x.regs.gpr[(GPRSummary.key Rn.toNat).val] = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping (EntryBodyRet.W Rn) x) :
    Uget.Chain.Step real (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)) := by
  refine plan_step3_branch real spec config rows mapping m scope image loadBase separated base offset
    budget p k room hk page aligned (EntryBodyRet.W Rn) 94 upd0 (fun _ => base + offset (k + 1))
    ?_ (fun _ _ => rfl) obligations
  intro x inv fetched enc0 b pins bp input guard quiet it ss
  obtain ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, _, _, _, _, _, nonProj, _, pcS,
      gpr, spr, gic⟩ :=
    EntryBodyRet.native_tail_x real x fetched enc0 Rn hRn noEret pins bp input guard b quiet it ss
      (hlow x inv)
  exact ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, gic, pcS.trans (target x inv), nonProj,
    gpr, spr⟩

#print axioms plan_step3_branch_cbz
#print axioms plan_step3_branch_bcond
#print axioms plan_step3_branch_ret
end HeapV2StepCerts.BranchStepV3
