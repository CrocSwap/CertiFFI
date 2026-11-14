import BR8.BranchTo
import SDKPA.BranchPins
import SDKPA.BranchPinsF
import Crypto.Tac
import Crypto.Tac2
import Crypto.BrSimp
import Crypto.BranchDefs
import Crypto.BrToRw
import Bridge.CruxNonProj
import Crypto.BranchPins
import Crypto.BranchPinsF
import Pilot.ObservationSimp
import Bridge.StepM
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace Crypto.BrToCore
open Crypto.BcondCore

set_option maxHeartbeats 40000000 in
/-- Observation of driver's flat BranchTo root: ok, frame, BranchTaken, PC = target (low target). -/
theorem brto_obs_pa (target : BitVec 64) (bt : BranchType) (c : Bool) (S0 : SequentialState Regs oracleChoiceSource)
    (hBP : Crypto.BranchPinsPA S0) (hVHE : S0.regs.FeatureImpl[54] = true) (hlow : target.toNat < 2 ^ 55) :
    ∃ t, BR8_BranchTo.native target bt c S0 = .ok () t ∧ BrFrame S0 t ∧
      t.regs.__BranchTaken = true ∧ t.regs._PC = target ∧ t.regs.Branchtypetaken = bt := by
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
  observe_simp [BR8_BranchTo.native]
  simp only [Crypto.BrSimp.tt_ff, Crypto.BrSimp.tt_ff2, Crypto.BrSimp.idx_55_63, ite_true, ite_false,
    dite_true, dite_false]
  simp (config := {maxSteps := 2000000}) only [Crypto.BrSimp.ok_ite, Crypto.BrSimp.ok_dite, Crypto.BrSimp.ok_exists]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals try (intro k hk)
  all_goals observe_simp [Sail.ConcurrencyInterfaceV1.RegisterRef.set]
  all_goals try simp only [dite_eq_ite, ite_self]
  all_goals try (simp (disch := first | exact hk | exact Ne.symm hk) only [Sail.ConcurrencyInterfaceV1.RegMap.set_ne, dite_eq_ite, ite_self]; done)
  all_goals try exact Crypto.BrSimp.tbi_low _ hlow _
  all_goals try decide
  all_goals try (first
    | exact ArmCertCT.CT2.NonProjRegsEq.refl _ _
    | (unfold ArmCertCT.CT2.NonProjRegsEq ArmCertCT.CT2.mask
       congr 1 <;> (try repeat' split) <;> (try simp (disch := decide) only [ArmBridge.CruxNonProj.maskBank_set]) <;> rfl))
#print axioms brto_obs_pa
end Crypto.BrToCore
