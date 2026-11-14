import RtBr.BrToRwPA
import Crypto.BranchDefs
import Crypto.BrToRw
import BR8.BCond
import Crypto.BcondDecode
import Crypto.BranchPins
import Crypto.BranchPinsF
import Crypto.BrSimp
import Pilot.ObservationSimp
import Bridge.CruxNonProj
import Crypto.Tac
import Crypto.Tac2
import Bridge.StepM
import Bridge.CruxNonProj
import SDKPA.BranchPinsF
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace NativeEntryBodyBranch.BcondExtra
open Crypto.BcondDec Crypto.BcondCore

/- Core f10a: PhysicalCount, full bkHeap mask and GIC for the actual B.cond successor,
by Crypto.BcondCore.bcond_obs_pa's own evaluation script on BR_BCondH.native. -/
set_option maxHeartbeats 40000000 in
theorem extra (real : Type) [Sail.SailReal real] (cond : BitVec 4) (imm19 : BitVec 19) (S0 : SequentialState Regs oracleChoiceSource)
    (hBP : Crypto.BranchPinsPA S0) (hVHE : S0.regs.FeatureImpl[54] = true)
    (hlow : (S0.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∃ t, BR_BCondH.native real cond imm19 (bcondWord imm19 cond) (-1) S0 = .ok () t ∧
      t.regs.PhysicalCount = S0.regs.PhysicalCount ∧
      ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap t.regs = ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap S0.regs ∧
      t.regs.bank_Option_InterruptID .__GIC_Pending = S0.regs.bank_Option_InterruptID .__GIC_Pending := by
  have hNS : Sail.BitVec.extractLsb (Mk_SCRType (S0.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3)) 0 0 = 1#1 := hBP.hSCR_NS
  have hb55 := Crypto.BrSimp.b55_false _ hlow
  have gi := Crypto.BrSimp.gi259
  have := hBP.f0
  have := hBP.f1
  have := hBP.f2
  have := hBP.f3
  have := hBP.f4
  have := hBP.f5
  have := hBP.f6
  have := hBP.f7
  have := hBP.f12
  have := hBP.f153
  have := hBP.f13
  have := hBP.f143
  have := hBP.f230
  have := hBP.f123
  have := hBP.f45
  have := hBP.f144
  have := hBP.f103
  have := hBP.f60
  have := hBP.f126
  have := hBP.f185
  have := hBP.f105
  have := hBP.f145
  have := hBP.f89
  have := hBP.f107
  have := hBP.f27
  have := hBP.f65
  have := hBP.f130
  have := hBP.f108
  have := hBP.f131
  have := hBP.f67
  have := hBP.f92
  have := hBP.f93
  have := hBP.f110
  have := hBP.f50
  have := hBP.f111
  have := hBP.f171
  have := hBP.f133
  have := hBP.f134
  have := hBP.f95
  have := hBP.f200
  have := hBP.f36
  have := hBP.f53
  have := hBP.f232
  have := hBP.f138
  have := hBP.f40
  have := hBP.f41
  have := hBP.f76
  have := hBP.f77
  have := hBP.f78
  have := hBP.f79
  have := hBP.f233
  have := hBP.f234
  have := hBP.f235
  have := hBP.f236
  have := hBP.f81
  have := hBP.f221
  have := hBP.f222
  have := hBP.f223
  have := hBP.f224
  have := hBP.f225
  have := hBP.f226
  have := hBP.f227
  have := hBP.f165
  observe_simp [BR_BCondH.native]
  rw [RtBr.BrToRwPA.brto_rw_pa ?hb (hV := ?hv) (hlow := ?hl)]
  case hb => exact { hBP with }
  case hv => exact hVHE
  case hl => exact hlow
  observe_simp [BR8_BranchTo.native]
  simp only [Crypto.BrSimp.tt_ff, Crypto.BrSimp.tt_ff2, Crypto.BrSimp.idx_55_63, ite_true, ite_false,
    dite_true, dite_false]
  simp (config := {maxSteps := 2000000}) only [Crypto.BrSimp.ok_ite, Crypto.BrSimp.ok_dite, Crypto.BrSimp.ok_exists]
  by_cases hC : bcondC cond S0.regs
  · have hC2 := hC
    unfold bcondC at hC2
    rw [if_pos hC2]
    refine ⟨?_, ?_, ?_⟩
    all_goals try (intro k hk)
    all_goals observe_simp [Sail.ConcurrencyInterfaceV1.RegisterRef.set]
    all_goals try simp only [dite_eq_ite, ite_self]
    all_goals try simp only [ArmCertCT.CT2.mask, ArmCertCT.CT2.maskPSTATE, ArmCertCT.CT2.maskBank, ArmBridge.CruxNonProj.bkHeap]
    all_goals
      congr 1
      all_goals first
        | rfl
        | (split <;> rfl)
        | (split <;> split <;> rfl)
        | (funext k; split <;> rfl)
        | (funext k; cases k <;> rfl)
        | (funext k; simp only [ArmCertCT.CT2.maskBank]; split <;> (try split) <;> (try split) <;> (try split) <;> (try simp (config := {maxSteps := 200000}) [Sail.ConcurrencyInterfaceV1.RegMap.set, Sail.ConcurrencyInterfaceV1.RegisterRef.set, *]) <;> (try contradiction) <;> (try (subst_vars; contradiction)) <;> (try (subst_vars; simp_all)) <;> (try (intro _ hk; subst hk; contradiction)) <;> (try (intro _ hk; subst hk; simp_all)) <;> done)
  · have hC2 := hC
    unfold bcondC at hC2
    rw [if_neg hC2]
    refine ⟨?_, ?_, ?_⟩
    all_goals try (intro k hk)
    all_goals observe_simp [Sail.ConcurrencyInterfaceV1.RegisterRef.set]
    all_goals try simp only [dite_eq_ite, ite_self]
    all_goals try simp only [ArmCertCT.CT2.mask, ArmCertCT.CT2.maskPSTATE, ArmCertCT.CT2.maskBank, ArmBridge.CruxNonProj.bkHeap]
    all_goals
      congr 1
      all_goals first
        | rfl
        | (split <;> rfl)
        | (split <;> split <;> rfl)
        | (funext k; split <;> rfl)
        | (funext k; cases k <;> rfl)
        | (funext k; simp only [ArmCertCT.CT2.maskBank]; split <;> (try split) <;> (try split) <;> (try split) <;> (try simp (config := {maxSteps := 200000}) [Sail.ConcurrencyInterfaceV1.RegMap.set, Sail.ConcurrencyInterfaceV1.RegisterRef.set, *]) <;> (try contradiction) <;> (try (subst_vars; contradiction)) <;> (try (subst_vars; simp_all)) <;> (try (intro _ hk; subst hk; contradiction)) <;> (try (intro _ hk; subst hk; simp_all)) <;> done)

#print axioms extra
end NativeEntryBodyBranch.BcondExtra
