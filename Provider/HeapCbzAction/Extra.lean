-- BR8 L2: HeapCbzAction.extra (parallel with Obs).
import HeapCbzAction.Base
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace ReleaseProfile.HeapCbzAction
open Crypto.CbzDec Crypto.BcondCore
open ArmBridge.Draft ArmBridge.DraftM

/- Core f10a: PhysicalCount, the full bkHeap mask and GIC for the actual CBZ successor
(the SDK branch line proves none of them). Same canonical BR_CBZ.native root and the
same evaluation script as Crypto.CbzCore.cbz_obs_pa, with a different conclusion. -/
#check "CURRENT_DECL CBZ X extra"
set_option maxHeartbeats 4000000 in
theorem extra (real : Type) [Sail.SailReal real]
    (Rt : BitVec 5) (imm19 : BitVec 19) (op sf : BitVec 1) (S0 : NativeState)
    (hBP : TranslateSpan.BranchMTE2.Base S0) (hVHE : S0.regs.FeatureImpl[54] = true)
    (hlow : (S0.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) :
    ∃ t, BR_CBZ.native real Rt imm19 op sf (cbzWord sf op imm19 Rt) (-1) S0 = .ok () t ∧
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
  observe_simp [BR_CBZ.native]
  rw [TranslateSpan.BrToRwMTE.brto_rw_mte ?hb (hV := ?hv) (hlow := ?hl)]
  case hb => exact { hBP with }
  case hv => exact hVHE
  case hl => exact hlow
  observe_simp [BR8_BranchTo.native]
  simp only [Crypto.BrSimp.tt_ff, Crypto.BrSimp.tt_ff2, Crypto.BrSimp.idx_55_63, Crypto.BrSimp.w_ok, ite_true, ite_false,
    dite_true, dite_false]
  simp (config := {maxSteps := 2000000}) only [Crypto.BrSimp.ok_ite, Crypto.BrSimp.ok_dite, Crypto.BrSimp.ok_exists]
  by_cases hL : cbzCond S0 sf op Rt
  · rw [if_pos ?nc]
    case nc => exact hL
    refine ⟨?_, ?_, ?_⟩
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
        | (funext k; simp only [ArmCertCT.CT2.maskBank]; split <;> (try split) <;> (try split) <;> (try split) <;> simp_all [Sail.ConcurrencyInterfaceV1.RegMap.set, Sail.ConcurrencyInterfaceV1.RegisterRef.set])
  · rw [if_neg ?nc]
    case nc => exact hL
    refine ⟨?_, ?_, ?_⟩
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
        | (funext k; simp only [ArmCertCT.CT2.maskBank]; split <;> (try split) <;> (try split) <;> (try split) <;> simp_all [Sail.ConcurrencyInterfaceV1.RegMap.set, Sail.ConcurrencyInterfaceV1.RegisterRef.set])

#print axioms extra
end ReleaseProfile.HeapCbzAction
