import BR8.BranchToPins
import NativeR14B.TbnzPinsPrefix
import BridgeDraft.StateProjection
import Crypto.BcondCore
import SDKPA.BrToCore
import SDKPA.BranchV2
import SDKPA.Roots
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace NativeR14B
open ArmBridge.Draft
set_option autoImplicit false
set_option maxRecDepth 1024
/-! runtime14 TBNZ (32-bit form, b5 = 0): exact taken / not-taken actions. The actual decoder is
TbnzPinsPrefix_native (drive_spec under the BR8 pins, BranchTo opaque): bit 0 of X[Rt] = 1 gives
BranchTo (PC + sext(imm14 ++ 00)) DIR true; otherwise the registers are untouched. The taken branch then
composes BR8_BranchTo.complete_pa / Crypto.BrToCore.brto_obs_pa (as B.cond, conditional = true). -/

/-- The decoder's branch condition, verbatim from the native. -/
abbrev tbnzBit (Rt : BitVec 5) (s : NativeState) : BitVec 1 :=
  BitVec.join1 [BitVec.access (BitVec.castWidth
    (Sail.BitVec.extractLsb s.regs.gpr[(GPRSummary.key Rt.toNat).val] (Int.toNatChecked 31) 0) : BitVec 32) 0]

/-- The TBNZ target. -/
abbrev tbnzTarget (imm14 : BitVec 14) (s : NativeState) : BitVec 64 := s.regs._PC + sign_extend (imm14 +++ 0#2) 64

set_option maxHeartbeats 8000000 in
theorem tbnz_taken (Rt : BitVec 5) (imm14 : BitVec 14) (s : NativeState)
    (hBP : Crypto.BranchV2.BranchPinsV2PA s)
    (hrt : Rt.toNat < 31) (hc : tbnzBit Rt s = 1#1) (hlow : (tbnzTarget imm14 s).toNat < 2 ^ 55) :
    ∃ u, (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 0#5 1#1 0#1 : SailM Unit) s = .ok () u ∧
      u.regs.gpr = s.regs.gpr ∧ u.regs.SP_EL0 = s.regs.SP_EL0 ∧ u.regs.PSTATE = s.regs.PSTATE ∧
      u.mem = s.mem ∧ u.events = s.events ∧ u.regs.BTypeNext = s.regs.BTypeNext ∧
      u.regs._PC = tbnzTarget imm14 s ∧ u.regs.__BranchTaken = true := by
  rw [TbnzPinsPrefix_complete Rt imm14 s hBP.base.hFeature_AA32EL0 hBP.base.hFeature_AA32EL1 hBP.base.hFeature_AA32EL2 hBP.base.hFeature_AA32EL3 hBP.base.hFeature_AA64EL0 hBP.base.hFeature_AA64EL1 hBP.base.hFeature_AA64EL2 hBP.base.hFeature_AA64EL3 hBP.base.hFeature_AES hBP.base.hFeature_AFP hBP.base.hFeature_AdvSIMD hBP.base.hFeature_BF16 hBP.base.hFeature_BRBE hBP.base.hFeature_BTI hBP.base.hFeature_CRC32 hBP.base.hFeature_DGH hBP.base.hFeature_DIT hBP.base.hFeature_DPB hBP.base.hFeature_DPB2 hBP.base.hFeature_Debugv8p9 hBP.base.hFeature_DotProd hBP.base.hFeature_ECV hBP.base.hFeature_FCMA hBP.base.hFeature_FHM hBP.base.hFeature_FP hBP.base.hFeature_FP16 hBP.base.hFeature_FRINTTS hBP.base.hFeature_FlagM hBP.base.hFeature_FlagM2 hBP.base.hFeature_I8MM hBP.base.hFeature_JSCVT hBP.base.hFeature_LRCPC hBP.base.hFeature_LRCPC2 hBP.base.hFeature_LSE hBP.base.hFeature_LSE2 hBP.base.hFeature_MOPS hBP.base.hFeature_MTE hBP.base.hFeature_MTE2 hBP.base.hFeature_PACIMP hBP.base.hFeature_PFAR hBP.base.hFeature_PMULL hBP.base.hFeature_RDM hBP.base.hFeature_RME hBP.base.hFeature_SB hBP.base.hFeature_SHA1 hBP.base.hFeature_SHA256 hBP.base.hFeature_SHA3 hBP.base.hFeature_SHA512 hBP.base.hFeature_SM3 hBP.base.hFeature_SM4 hBP.base.hFeature_SME hBP.base.hFeature_SME_F64F64 hBP.base.hFeature_SME_FA64 hBP.base.hFeature_SME_I16I64 hBP.base.hFeature_SVE hBP.base.hFeature_SVE2 hBP.base.hFeature_SVE_AES hBP.base.hFeature_SVE_BitPerm hBP.base.hFeature_SVE_PMULL128 hBP.base.hFeature_SVE_SHA3 hBP.base.hFeature_SVE_SM4 hBP.base.hFeature_TME hBP.base.hFeature_WFxT hBP.base.hDebugBP hBP.base.hDebugWP hBP.base.hDebugCTX hBP.base.hEDSCR_STATUS hBP.base.hSPE hBP.base.hEL hBP.base.hnRW hBP.base.hIL hBP.base.hE2H hBP.base.hTGE hBP.base.hSCR_NS hBP.base.hSCR_NSE hBP.base.hMDSCR_SS hBP.base.hPSTATE_SS hBP.base.hOSUC hBP.base.hPMB_E hBP.base.hSCR_RW hBP.base.hSCR_EEL2 hBP.base.hTBI0 hBP.base.hTBID0 hBP.base.hNSPB hBP.base.hNSPBE  hrt]
  unfold TbnzPinsPrefix_native
  rw [dite_cond_eq_true (eq_true hc)]
  rw [BR8_BranchTo.complete_pa _ BranchType.BranchType_DIR true s hBP.base.hFeature_AA32EL0 hBP.base.hFeature_AA32EL1 hBP.base.hFeature_AA32EL2 hBP.base.hFeature_AA32EL3 hBP.base.hFeature_AA64EL0 hBP.base.hFeature_AA64EL1 hBP.base.hFeature_AA64EL2 hBP.base.hFeature_AA64EL3 hBP.base.hFeature_AES hBP.base.hFeature_AFP hBP.base.hFeature_AdvSIMD hBP.base.hFeature_BF16 hBP.base.hFeature_BRBE hBP.base.hFeature_BTI hBP.base.hFeature_CRC32 hBP.base.hFeature_DGH hBP.base.hFeature_DIT hBP.base.hFeature_DPB hBP.base.hFeature_DPB2 hBP.base.hFeature_Debugv8p9 hBP.base.hFeature_DotProd hBP.base.hFeature_ECV hBP.base.hFeature_FCMA hBP.base.hFeature_FHM hBP.base.hFeature_FP hBP.base.hFeature_FP16 hBP.base.hFeature_FRINTTS hBP.base.hFeature_FlagM hBP.base.hFeature_FlagM2 hBP.base.hFeature_I8MM hBP.base.hFeature_JSCVT hBP.base.hFeature_LRCPC hBP.base.hFeature_LRCPC2 hBP.base.hFeature_LSE hBP.base.hFeature_LSE2 hBP.base.hFeature_MOPS hBP.base.hFeature_MTE hBP.base.hFeature_MTE2 hBP.base.hFeature_PACIMP hBP.base.hFeature_PFAR hBP.base.hFeature_PMULL hBP.base.hFeature_RDM hBP.base.hFeature_RME hBP.base.hFeature_SB hBP.base.hFeature_SHA1 hBP.base.hFeature_SHA256 hBP.base.hFeature_SHA3 hBP.base.hFeature_SHA512 hBP.base.hFeature_SM3 hBP.base.hFeature_SM4 hBP.base.hFeature_SME hBP.base.hFeature_SME_F64F64 hBP.base.hFeature_SME_FA64 hBP.base.hFeature_SME_I16I64 hBP.base.hFeature_SVE hBP.base.hFeature_SVE2 hBP.base.hFeature_SVE_AES hBP.base.hFeature_SVE_BitPerm hBP.base.hFeature_SVE_PMULL128 hBP.base.hFeature_SVE_SHA3 hBP.base.hFeature_SVE_SM4 hBP.base.hFeature_TME hBP.base.hFeature_WFxT hBP.base.hDebugBP hBP.base.hDebugWP hBP.base.hDebugCTX hBP.base.hEDSCR_STATUS hBP.base.hSPE hBP.base.hEL hBP.base.hnRW hBP.base.hIL hBP.base.hE2H hBP.base.hTGE hBP.base.hSCR_NS hBP.base.hSCR_NSE hBP.base.hMDSCR_SS hBP.base.hPSTATE_SS hBP.base.hOSUC hBP.base.hPMB_E hBP.base.hSCR_RW hBP.base.hSCR_EEL2 hBP.base.hTBI0 hBP.base.hTBID0 hBP.base.hNSPB hBP.base.hNSPBE]
  obtain ⟨u, hN, hF, hbt, hpc, _⟩ := Crypto.BrToCore.brto_obs_pa _ BranchType.BranchType_DIR true s hBP.base hBP.vhe hlow
  exact ⟨u, hN, hF.gpr, hF.sp, hF.pstate, hF.mem, hF.events, hF.btn, hpc, hbt⟩
  -- train-v3 BR8 split B2: BranchTo native pins (VHE, target bit55)
  case hVHE => exact BR8Pins.vhe_bang _ hBP.vhe
  case hBit55 => exact BR8Pins.bit55_of_lt _ hlow

set_option maxHeartbeats 8000000 in
theorem tbnz_not_taken (Rt : BitVec 5) (imm14 : BitVec 14) (s : NativeState)
    (hBP : Crypto.BranchV2.BranchPinsV2PA s)
    (hrt : Rt.toNat < 31) (hc : ¬ tbnzBit Rt s = 1#1) :
    ∃ u, (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 0#5 1#1 0#1 : SailM Unit) s = .ok () u ∧
      u.regs = s.regs ∧ u.mem = s.mem ∧ u.events = s.events := by
  rw [TbnzPinsPrefix_complete Rt imm14 s hBP.base.hFeature_AA32EL0 hBP.base.hFeature_AA32EL1 hBP.base.hFeature_AA32EL2 hBP.base.hFeature_AA32EL3 hBP.base.hFeature_AA64EL0 hBP.base.hFeature_AA64EL1 hBP.base.hFeature_AA64EL2 hBP.base.hFeature_AA64EL3 hBP.base.hFeature_AES hBP.base.hFeature_AFP hBP.base.hFeature_AdvSIMD hBP.base.hFeature_BF16 hBP.base.hFeature_BRBE hBP.base.hFeature_BTI hBP.base.hFeature_CRC32 hBP.base.hFeature_DGH hBP.base.hFeature_DIT hBP.base.hFeature_DPB hBP.base.hFeature_DPB2 hBP.base.hFeature_Debugv8p9 hBP.base.hFeature_DotProd hBP.base.hFeature_ECV hBP.base.hFeature_FCMA hBP.base.hFeature_FHM hBP.base.hFeature_FP hBP.base.hFeature_FP16 hBP.base.hFeature_FRINTTS hBP.base.hFeature_FlagM hBP.base.hFeature_FlagM2 hBP.base.hFeature_I8MM hBP.base.hFeature_JSCVT hBP.base.hFeature_LRCPC hBP.base.hFeature_LRCPC2 hBP.base.hFeature_LSE hBP.base.hFeature_LSE2 hBP.base.hFeature_MOPS hBP.base.hFeature_MTE hBP.base.hFeature_MTE2 hBP.base.hFeature_PACIMP hBP.base.hFeature_PFAR hBP.base.hFeature_PMULL hBP.base.hFeature_RDM hBP.base.hFeature_RME hBP.base.hFeature_SB hBP.base.hFeature_SHA1 hBP.base.hFeature_SHA256 hBP.base.hFeature_SHA3 hBP.base.hFeature_SHA512 hBP.base.hFeature_SM3 hBP.base.hFeature_SM4 hBP.base.hFeature_SME hBP.base.hFeature_SME_F64F64 hBP.base.hFeature_SME_FA64 hBP.base.hFeature_SME_I16I64 hBP.base.hFeature_SVE hBP.base.hFeature_SVE2 hBP.base.hFeature_SVE_AES hBP.base.hFeature_SVE_BitPerm hBP.base.hFeature_SVE_PMULL128 hBP.base.hFeature_SVE_SHA3 hBP.base.hFeature_SVE_SM4 hBP.base.hFeature_TME hBP.base.hFeature_WFxT hBP.base.hDebugBP hBP.base.hDebugWP hBP.base.hDebugCTX hBP.base.hEDSCR_STATUS hBP.base.hSPE hBP.base.hEL hBP.base.hnRW hBP.base.hIL hBP.base.hE2H hBP.base.hTGE hBP.base.hSCR_NS hBP.base.hSCR_NSE hBP.base.hMDSCR_SS hBP.base.hPSTATE_SS hBP.base.hOSUC hBP.base.hPMB_E hBP.base.hSCR_RW hBP.base.hSCR_EEL2 hBP.base.hTBI0 hBP.base.hTBID0 hBP.base.hNSPB hBP.base.hNSPBE  hrt]
  unfold TbnzPinsPrefix_native
  rw [dite_cond_eq_false (eq_false hc)]
  refine ⟨_, rfl, ?_, ?_, ?_⟩ <;> (repeat' split) <;> rfl

#print axioms tbnz_taken
#print axioms tbnz_not_taken
end NativeR14B
