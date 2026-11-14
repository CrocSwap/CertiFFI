import Crypto.BranchPins
import Crypto.BranchV2
import Bridge.CruxGen
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions EvalProfile
namespace Crypto4
open ArmBridge.CruxCore ArmBridge.CruxGen

/-- BranchPins persists along a run: crux4 steps give SysEq2 s fin, StepPins fin and BrSysEq s fin. Proof script emitted
    field-by-field from the BranchPins source (one generic lemma). -/
theorem branchPins_step (s fin : SequentialState Regs oracleChoiceSource) (h : Crypto.BranchPins s)
    (hsys : SysEq2 s.regs fin.regs) (hp : StepPins fin) (hbr : BrSysEq s.regs fin.regs) : Crypto.BranchPins fin where
  hFeature_AA32EL0 := by rw [hsys.feat]; exact h.hFeature_AA32EL0
  hFeature_AA32EL1 := by rw [hsys.feat]; exact h.hFeature_AA32EL1
  hFeature_AA32EL2 := by rw [hsys.feat]; exact h.hFeature_AA32EL2
  hFeature_AA32EL3 := by rw [hsys.feat]; exact h.hFeature_AA32EL3
  hFeature_AA64EL0 := by rw [hsys.feat]; exact h.hFeature_AA64EL0
  hFeature_AA64EL1 := by rw [hsys.feat]; exact h.hFeature_AA64EL1
  hFeature_AA64EL2 := by rw [hsys.feat]; exact h.hFeature_AA64EL2
  hFeature_AA64EL3 := by rw [hsys.feat]; exact h.hFeature_AA64EL3
  hFeature_AES := by rw [hsys.feat]; exact h.hFeature_AES
  hFeature_AFP := by rw [hsys.feat]; exact h.hFeature_AFP
  hFeature_AdvSIMD := by rw [hsys.feat]; exact h.hFeature_AdvSIMD
  hFeature_BF16 := by rw [hsys.feat]; exact h.hFeature_BF16
  hFeature_BRBE := by rw [hsys.feat]; exact h.hFeature_BRBE
  hFeature_BTI := by rw [hsys.feat]; exact h.hFeature_BTI
  hFeature_CRC32 := by rw [hsys.feat]; exact h.hFeature_CRC32
  hFeature_DGH := by rw [hsys.feat]; exact h.hFeature_DGH
  hFeature_DIT := by rw [hsys.feat]; exact h.hFeature_DIT
  hFeature_DPB := by rw [hsys.feat]; exact h.hFeature_DPB
  hFeature_DPB2 := by rw [hsys.feat]; exact h.hFeature_DPB2
  hFeature_Debugv8p9 := by rw [hsys.feat]; exact h.hFeature_Debugv8p9
  hFeature_DotProd := by rw [hsys.feat]; exact h.hFeature_DotProd
  hFeature_ECV := by rw [hsys.feat]; exact h.hFeature_ECV
  hFeature_FCMA := by rw [hsys.feat]; exact h.hFeature_FCMA
  hFeature_FHM := by rw [hsys.feat]; exact h.hFeature_FHM
  hFeature_FP := by rw [hsys.feat]; exact h.hFeature_FP
  hFeature_FP16 := by rw [hsys.feat]; exact h.hFeature_FP16
  hFeature_FRINTTS := by rw [hsys.feat]; exact h.hFeature_FRINTTS
  hFeature_FlagM := by rw [hsys.feat]; exact h.hFeature_FlagM
  hFeature_FlagM2 := by rw [hsys.feat]; exact h.hFeature_FlagM2
  hFeature_I8MM := by rw [hsys.feat]; exact h.hFeature_I8MM
  hFeature_JSCVT := by rw [hsys.feat]; exact h.hFeature_JSCVT
  hFeature_LRCPC := by rw [hsys.feat]; exact h.hFeature_LRCPC
  hFeature_LRCPC2 := by rw [hsys.feat]; exact h.hFeature_LRCPC2
  hFeature_LSE := by rw [hsys.feat]; exact h.hFeature_LSE
  hFeature_LSE2 := by rw [hsys.feat]; exact h.hFeature_LSE2
  hFeature_MOPS := by rw [hsys.feat]; exact h.hFeature_MOPS
  hFeature_MTE := by rw [hsys.feat]; exact h.hFeature_MTE
  hFeature_MTE2 := by rw [hsys.feat]; exact h.hFeature_MTE2
  hFeature_PACIMP := by rw [hsys.feat]; exact h.hFeature_PACIMP
  hFeature_PFAR := by rw [hsys.feat]; exact h.hFeature_PFAR
  hFeature_PMULL := by rw [hsys.feat]; exact h.hFeature_PMULL
  hFeature_RDM := by rw [hsys.feat]; exact h.hFeature_RDM
  hFeature_RME := by rw [hsys.feat]; exact h.hFeature_RME
  hFeature_SB := by rw [hsys.feat]; exact h.hFeature_SB
  hFeature_SHA1 := by rw [hsys.feat]; exact h.hFeature_SHA1
  hFeature_SHA256 := by rw [hsys.feat]; exact h.hFeature_SHA256
  hFeature_SHA3 := by rw [hsys.feat]; exact h.hFeature_SHA3
  hFeature_SHA512 := by rw [hsys.feat]; exact h.hFeature_SHA512
  hFeature_SM3 := by rw [hsys.feat]; exact h.hFeature_SM3
  hFeature_SM4 := by rw [hsys.feat]; exact h.hFeature_SM4
  hFeature_SME := by rw [hsys.feat]; exact h.hFeature_SME
  hFeature_SME_F64F64 := by rw [hsys.feat]; exact h.hFeature_SME_F64F64
  hFeature_SME_FA64 := by rw [hsys.feat]; exact h.hFeature_SME_FA64
  hFeature_SME_I16I64 := by rw [hsys.feat]; exact h.hFeature_SME_I16I64
  hFeature_SVE := by rw [hsys.feat]; exact h.hFeature_SVE
  hFeature_SVE2 := by rw [hsys.feat]; exact h.hFeature_SVE2
  hFeature_SVE_AES := by rw [hsys.feat]; exact h.hFeature_SVE_AES
  hFeature_SVE_BitPerm := by rw [hsys.feat]; exact h.hFeature_SVE_BitPerm
  hFeature_SVE_PMULL128 := by rw [hsys.feat]; exact h.hFeature_SVE_PMULL128
  hFeature_SVE_SHA3 := by rw [hsys.feat]; exact h.hFeature_SVE_SHA3
  hFeature_SVE_SM4 := by rw [hsys.feat]; exact h.hFeature_SVE_SM4
  hFeature_TME := by rw [hsys.feat]; exact h.hFeature_TME
  hFeature_WFxT := by rw [hsys.feat]; exact h.hFeature_WFxT
  hDebugBP := by rw [hbr.nbp]; exact h.hDebugBP
  hDebugWP := by rw [hbr.nwp]; exact h.hDebugWP
  hDebugCTX := by rw [hbr.nctx]; exact h.hDebugCTX
  hEDSCR_STATUS := hp.st
  hSPE := hp.spe
  hPA := by rw [hsys.pa]; exact h.hPA
  hEL := hp.el
  hnRW := hp.nrw
  hIL := hp.il
  hE2H := by rw [hsys.hcr]; exact h.hE2H
  hTGE := by rw [hsys.hcr]; exact h.hTGE
  hSCR_NS := by rw [hsys.scr]; exact h.hSCR_NS
  hSCR_NSE := by rw [hsys.scr]; exact h.hSCR_NSE
  hMDSCR_SS := by rw [hsys.mdscr]; exact h.hMDSCR_SS
  hPSTATE_SS := hp.pss
  hOSUC := by rw [hp.edesr]; rfl
  hPMB_E := hp.pmbe
  hSCR_RW := by rw [hsys.scr]; exact h.hSCR_RW
  hSCR_EEL2 := by rw [hsys.scr]; exact h.hSCR_EEL2
  hTBI0 := by rw [hsys.tcr]; exact h.hTBI0
  hTBID0 := by rw [hsys.tcr]; exact h.hTBID0
  hNSPB := by rw [hbr.mdcr3]; exact h.hNSPB
  hNSPBE := by rw [hbr.mdcr3]; exact h.hNSPBE

theorem vhe_step (s fin : SequentialState Regs oracleChoiceSource) (hsys : SysEq2 s.regs fin.regs)
    (h : s.regs.FeatureImpl[54] = true) : fin.regs.FeatureImpl[54] = true := by rw [hsys.feat]; exact h
theorem gcs_step (s fin : SequentialState Regs oracleChoiceSource) (hsys : SysEq2 s.regs fin.regs)
    (h : s.regs.FeatureImpl[245] = false) : fin.regs.FeatureImpl[245] = false := by rw [hsys.feat]; exact h

/-- BranchPinsV2 (BranchPins + FEAT_VHE + FEAT_GCS off) persists along a crux4.1 run (eval, heap-crux v2 Pins2). -/
theorem branchPinsV2_step (s fin : SequentialState Regs oracleChoiceSource) (h : Crypto.BranchV2.BranchPinsV2 s)
    (hsys : SysEq2 s.regs fin.regs) (hp : StepPins fin) (hbr : BrSysEq s.regs fin.regs) : Crypto.BranchV2.BranchPinsV2 fin :=
  ⟨branchPins_step s fin h.base hsys hp hbr, vhe_step s fin hsys h.vhe, gcs_step s fin hsys h.gcs⟩

#print axioms branchPins_step
#print axioms branchPinsV2_step
end Crypto4
