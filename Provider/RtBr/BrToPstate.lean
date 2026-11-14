-- RtBr.BrToPstate: BranchTo (BR8 root) leaves PSTATE unchanged. Prelude from SDKPA.BrToCore.brto_obs_pa
-- (copied: that module's closure reaches LNSym). Imports: BR8.BranchTo, BranchPins(F), BrSimp, ObservationSimp only.
import BR8.BranchTo
import SDKPA.BranchPins
import SDKPA.BranchPinsF
import Crypto.BrSimp
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
set_option autoImplicit false
namespace RtBr.BrToPstate

set_option maxHeartbeats 40000000 in
theorem pstate (target : BitVec 64) (bt : BranchType) (c : Bool) (S0 : SequentialState Regs oracleChoiceSource)
    (hBP : Crypto.BranchPinsPA S0) (hVHE : S0.regs.FeatureImpl[54] = true) (hlow : target.toNat < 2 ^ 55) :
    ∃ t, BR8_BranchTo.native target bt c S0 = .ok () t ∧ t.regs.PSTATE = S0.regs.PSTATE := by
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
  observe_simp [Sail.ConcurrencyInterfaceV1.RegisterRef.set]
  all_goals try simp only [dite_eq_ite, ite_self]
  all_goals try rfl

#print axioms pstate
end RtBr.BrToPstate
