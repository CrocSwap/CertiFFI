-- PipeR14Next.Common: shared pieces for the runtime14 branch next obligations.
-- flags_of_agreesAt: the NZCV analogue of regVal_of_agreesAt. cond_bridge: the value layer's condHolds on
-- the flag words decides Crypto.BcondCore.bcondC. nextG_bcond: B.cond over ChainInvG with the rich RtBranch tail.
import ArmCertPipe.Prefix
import ArmCertPipe.Guard
import RtG.NextG
import RtBranch.BranchTailsX
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.Boundary ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
namespace PipeR14Next
open ArmCertValue ArmCertPipe

theorem flags_of_agreesAt {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {k : Nat} {x : HeapV2StepCerts.RegBind.St} {D : List Def} {σf : Sym}
    (h : AgreesAt mapping pinv regions σ0 inputs plan k x)
    (hall : compileRun regions σ0 inputs.length plan = some (D, σf))
    {n z c v : Nat}
    (hr : (compileRun regions σ0 inputs.length (plan.take k)).map (fun p => p.2.nzcv) = some (some (n, z, c, v))) :
    x.regs.PSTATE.N.setWidth 64 = (extend inputs D).getD n 0 ∧ x.regs.PSTATE.Z.setWidth 64 = (extend inputs D).getD z 0 ∧
    x.regs.PSTATE.C.setWidth 64 = (extend inputs D).getD c 0 ∧ x.regs.PSTATE.V.setWidth 64 = (extend inputs D).getD v 0 := by
  obtain ⟨ds, σ, hc, hA, hB⟩ := h
  rw [hc] at hr
  simp only [Option.map_some, Option.some.injEq] at hr
  obtain ⟨vn, vz, vc, vv⟩ := hA.2.1 n z c v hr
  obtain ⟨ln, lz, lc, lv⟩ := hB.2.1 n z c v hr
  have split := compileRun_append regions (plan.take k) (plan.drop k) σ0 inputs.length
  rw [List.take_append_drop, hall, hc] at split
  simp only [Option.bind_some] at split
  cases hrest : compileRun regions σ (inputs.length + ds.length) (plan.drop k) with
  | none => rw [hrest] at split; simp at split
  | some q =>
    rw [hrest] at split
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at split
    rw [split.1, extend_append]
    exact ⟨by rw [vn, getD_extend_input _ _ ln], by rw [vz, getD_extend_input _ _ lz],
      by rw [vc, getD_extend_input _ _ lc], by rw [vv, getD_extend_input _ _ lv]⟩

theorem bv1_cases (a : BitVec 1) : a = 0#1 ∨ a = 1#1 := by
  have h := a.isLt
  rcases (show a.toNat = 0 ∨ a.toNat = 1 by omega) with h0 | h1
  · left; exact BitVec.eq_of_toNat_eq h0
  · right; exact BitVec.eq_of_toNat_eq h1

theorem bv4_cases (c : BitVec 4) : c = 0#4 ∨ c = 1#4 ∨ c = 2#4 ∨ c = 3#4 ∨ c = 4#4 ∨ c = 5#4 ∨ c = 6#4 ∨ c = 7#4 ∨ c = 8#4 ∨ c = 9#4 ∨ c = 10#4 ∨ c = 11#4 ∨ c = 12#4 ∨ c = 13#4 ∨ c = 14#4 ∨ c = 15#4 := by
  have h := c.isLt
  have : c.toNat < 16 := h
  rcases (show c.toNat = 0 ∨ c.toNat = 1 ∨ c.toNat = 2 ∨ c.toNat = 3 ∨ c.toNat = 4 ∨ c.toNat = 5 ∨ c.toNat = 6 ∨ c.toNat = 7 ∨ c.toNat = 8 ∨ c.toNat = 9 ∨ c.toNat = 10 ∨ c.toNat = 11 ∨ c.toNat = 12 ∨ c.toNat = 13 ∨ c.toNat = 14 ∨ c.toNat = 15 by omega) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    first | (simp only [← BitVec.toNat_inj]; simp [h]) | omega

/-- The value layer's condition on the flag words decides the Sail B.cond condition. -/
theorem cond_bridge (c : BitVec 4) (r : Regs) (b : Bool)
    (h : condHolds c (r.PSTATE.N.setWidth 64) (r.PSTATE.Z.setWidth 64) (r.PSTATE.C.setWidth 64)
      (r.PSTATE.V.setWidth 64) = b) :
    Crypto.BcondCore.bcondC c r ↔ b = true := by
  unfold Crypto.BcondCore.bcondC
  revert h
  generalize r.PSTATE.N = n
  generalize r.PSTATE.Z = z
  generalize r.PSTATE.C = cv
  generalize r.PSTATE.V = v
  rcases bv4_cases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases bv1_cases n with rfl | rfl <;> rcases bv1_cases z with rfl | rfl <;>
    rcases bv1_cases cv with rfl | rfl <;> rcases bv1_cases v with rfl | rfl <;> cases b <;> decide

#print axioms cond_bridge
#print axioms flags_of_agreesAt


open ArmCert.Translate.Model ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext in
/-- B.cond over ChainInvG, direction  decided by : RtG.nextG_branch with LRBranch's rich B.cond tail. -/
theorem nextG_bcond (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (cond : BitVec 4) (imm19 : BitVec 19) (taken : Bool)
    (noEret : (Sail.BitVec.extractLsb (ArmBridge.CruxGenGuarded.EntryBodyBcond.W cond imm19) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (dec : Crypto.BcondCore.bcondC cond x.regs ↔ taken = true)
    (hlow : (x.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55)
    (target : base + offset (k + 1) =
      (if taken then x.regs._PC + sign_extend (imm19 ++ 0#2) 64 else x.regs._PC + 4#64))
    (ob : FetchObligations spec config rows mapping (ArmBridge.CruxGenGuarded.EntryBodyBcond.W cond imm19) x)
    (hextra : ∀ fin, modelStep real x = .ok () fin → fin.mem = x.mem → fin.regs.gpr = x.regs.gpr →
      fin.regs.SP_EL0 = x.regs.SP_EL0 → extra (k + 1) fin) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra (k + 1) fin := by
  have tail : HeapV2StepCerts.BranchStepV3.BranchTailAt real (ArmBridge.CruxGenGuarded.EntryBodyBcond.W cond imm19) 69 x
      (base + offset (k + 1)) := by
    intro fetched enc0 b pins bp input guard quiet it ss
    obtain ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, _, _, _, _, _, nonProj, _, pcS,
        gpr, spr, gic⟩ :=
      ArmBridge.CruxGenGuarded.EntryBodyBcond.native_tail_x real x fetched enc0 cond imm19 noEret pins bp input guard b quiet it ss
        hlow
    refine ⟨sp, a, fin, pmu, run, frame, quiet', pins', sys, brs, mem, gic, ?_, nonProj, gpr, spr⟩
    rw [pcS, target]
    cases taken
    · rw [if_neg (fun h => absurd (dec.mp h) (by decide))] <;> rfl
    · rw [if_pos (dec.mpr rfl)] <;> rfl
  obtain ⟨fin, run, inv', _⟩ := RtG.nextG_branch real spec config rows mapping m scope image loadBase separated base offset
    budget extra k room page aligned (ArmBridge.CruxGenGuarded.EntryBodyBcond.W cond imm19) 69
    (fun _ => base + offset (k + 1)) x inv tail rfl ob hextra
  exact ⟨fin, run, inv'⟩

#print axioms nextG_bcond
end PipeR14Next
