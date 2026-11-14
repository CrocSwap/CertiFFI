import Bridge.CruxGen
import Bridge.PSRest
import Bridge.RootFrame
import Bridge.CruxNonProj
import CryptoBridge.CsincGen
import Bridge.DispCsinc3
import BKf.csincP3
import BKf.csincG3
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.CruxGen ArmBridge.PSRest ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.CruxCore
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.CruxICsinc3LNSym.
namespace ArmBridge.CruxICsinc3

def maddF (u : NativeState) :=
  (u.regs.bank_Bool, u.regs.FeatureImpl, u.regs.PSTATE, u.regs.BTypeNext, u.regs.__BranchTaken, u.regs._PC,
    u.regs.bank_BitVec_64, u.regs.bank_BitVec_32, u.regs.bank_Int, u.regs.ShouldAdvanceSS, u.regs.ShouldAdvanceIT,
    u.regs.__ThisInstrEnc, u.mem, u.events, u.regs.Branchtypetaken, u.regs.__emulator_termination_opcode, u.regs.bank_BitVec_128,
    ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap u.regs, u.regs.bank_Option_InterruptID .__GIC_Pending)

def Guard (t : NativeState) : Prop := t.regs.PSTATE.EL = 0#2 ∧ t.regs.bank_Bool .SPESampleInFlight = false

instance (t : NativeState) : Decidable (Guard t) := by unfold Guard; infer_instance

def RG (Rd Rn Rm : BitVec 5) (t : NativeState) : NativeState := if Guard t then resSt t (((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit)) t) else t

theorem madd_ok (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t : NativeState) :
    ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit)) t = .ok () (resSt t (((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit)) t)) :=
  ArmBridge.RootFrame.ok_of_root _ maddF t _ _ (ArmBridge.BKf.csincP3_complete real Rd Rn Rm t)

set_option maxHeartbeats 40000000 in
theorem madd_frame (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t : NativeState) (hg : Guard t) :
    ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit)) t = .ok () (resSt t (((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit)) t)) ∧ maddF (resSt t (((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit)) t)) = maddF t := by
  obtain ⟨hel, hspe⟩ := hg
  obtain ⟨u', hu⟩ : ∃ u', ArmBridge.BKf.csincP3_native real Rd Rn Rm t = .ok (maddF t) u' := by
    unfold ArmBridge.BKf.csincP3_native
    by_cases hRn : Rd.toNat = 31 <;> by_cases hSPs : t.regs.PSTATE.SP = 0#1 <;>
    · have hRi : ((Rd.toNat : Int) = 31) ↔ Rd.toNat = 31 := by omega
      simp (config := {maxSteps := 50000000}) only [ArmFull.Register.PSTATE_set, ArmFull.Register.SP_EL0_set, ArmBridge.RootFrame.sw_join1, hRn, hRi, hSPs, dite_true, dite_false, ite_true, ite_false, ↓reduceIte, ↓reduceDIte, Bool.false_eq_true, BitVec.reduceEq, ArmBridge.RootFrame.natcast31, ite_self, dite_eq_ite, ArmBridge.RootFrame.ite_sregs, ArmBridge.RootFrame.dite_sregs, ArmBridge.RootFrame.ite_smem, ArmBridge.RootFrame.dite_smem, ArmBridge.RootFrame.ite_sevents, ArmBridge.RootFrame.dite_sevents, ArmBridge.RootFrame.ite_rbank_Bool, ArmBridge.RootFrame.dite_rbank_Bool, ArmBridge.RootFrame.ite_rFeatureImpl, ArmBridge.RootFrame.dite_rFeatureImpl, ArmBridge.RootFrame.ite_rPSTATE, ArmBridge.RootFrame.dite_rPSTATE, ArmBridge.RootFrame.ite_rBTypeNext, ArmBridge.RootFrame.dite_rBTypeNext, ArmBridge.RootFrame.ite_rBranchTaken, ArmBridge.RootFrame.dite_rBranchTaken, ArmBridge.RootFrame.ite_rPC, ArmBridge.RootFrame.dite_rPC, ArmBridge.RootFrame.ite_rbank_BitVec_64, ArmBridge.RootFrame.dite_rbank_BitVec_64, ArmBridge.RootFrame.ite_rbank_BitVec_32, ArmBridge.RootFrame.dite_rbank_BitVec_32, ArmBridge.RootFrame.ite_rbank_Int, ArmBridge.RootFrame.dite_rbank_Int, ArmBridge.RootFrame.ite_rShouldAdvanceSS, ArmBridge.RootFrame.dite_rShouldAdvanceSS, ArmBridge.RootFrame.ite_rShouldAdvanceIT, ArmBridge.RootFrame.dite_rShouldAdvanceIT, ArmBridge.RootFrame.ite_rThisInstrEnc, ArmBridge.RootFrame.dite_rThisInstrEnc, ArmBridge.RootFrame.ite_rBranchtypetaken, ArmBridge.RootFrame.dite_rBranchtypetaken, ArmBridge.RootFrame.ite_remulator_termination_opcode, ArmBridge.RootFrame.dite_remulator_termination_opcode, ArmBridge.RootFrame.ite_rbank_BitVec_128, ArmBridge.RootFrame.dite_rbank_BitVec_128, ArmBridge.RootFrame.ite_pD, ArmBridge.RootFrame.dite_pD, ArmBridge.RootFrame.ite_pA, ArmBridge.RootFrame.dite_pA, ArmBridge.RootFrame.ite_pI, ArmBridge.RootFrame.dite_pI, ArmBridge.RootFrame.ite_pF, ArmBridge.RootFrame.dite_pF, ArmBridge.RootFrame.ite_pEXLOCK, ArmBridge.RootFrame.dite_pEXLOCK, ArmBridge.RootFrame.ite_pPAN, ArmBridge.RootFrame.dite_pPAN, ArmBridge.RootFrame.ite_pUAO, ArmBridge.RootFrame.dite_pUAO, ArmBridge.RootFrame.ite_pDIT, ArmBridge.RootFrame.dite_pDIT, ArmBridge.RootFrame.ite_pTCO, ArmBridge.RootFrame.dite_pTCO, ArmBridge.RootFrame.ite_pPM, ArmBridge.RootFrame.dite_pPM, ArmBridge.RootFrame.ite_pPPEND, ArmBridge.RootFrame.dite_pPPEND, ArmBridge.RootFrame.ite_pBTYPE, ArmBridge.RootFrame.dite_pBTYPE, ArmBridge.RootFrame.ite_pZA, ArmBridge.RootFrame.dite_pZA, ArmBridge.RootFrame.ite_pSM, ArmBridge.RootFrame.dite_pSM, ArmBridge.RootFrame.ite_pALLINT, ArmBridge.RootFrame.dite_pALLINT, ArmBridge.RootFrame.ite_pSS, ArmBridge.RootFrame.dite_pSS, ArmBridge.RootFrame.ite_pIL, ArmBridge.RootFrame.dite_pIL, ArmBridge.RootFrame.ite_pEL, ArmBridge.RootFrame.dite_pEL, ArmBridge.RootFrame.ite_pnRW, ArmBridge.RootFrame.dite_pnRW, ArmBridge.RootFrame.ite_pSP, ArmBridge.RootFrame.dite_pSP, ArmBridge.RootFrame.ite_pQ, ArmBridge.RootFrame.dite_pQ, ArmBridge.RootFrame.ite_pGE, ArmBridge.RootFrame.dite_pGE, ArmBridge.RootFrame.ite_pSSBS, ArmBridge.RootFrame.dite_pSSBS, ArmBridge.RootFrame.ite_pIT, ArmBridge.RootFrame.dite_pIT, ArmBridge.RootFrame.ite_pJ, ArmBridge.RootFrame.dite_pJ, ArmBridge.RootFrame.ite_pT, ArmBridge.RootFrame.dite_pT, ArmBridge.RootFrame.ite_pE, ArmBridge.RootFrame.dite_pE, ArmBridge.RootFrame.ite_pM, ArmBridge.RootFrame.dite_pM, ArmBridge.RootFrame.ite_rgpr, ArmBridge.RootFrame.dite_rgpr, ArmBridge.RootFrame.ite_rSP_EL0, ArmBridge.RootFrame.dite_rSP_EL0, ArmBridge.RootFrame.ite_rZ, ArmBridge.RootFrame.dite_rZ, ArmBridge.RootFrame.ite_pN, ArmBridge.RootFrame.dite_pN, ArmBridge.RootFrame.ite_pZ, ArmBridge.RootFrame.dite_pZ, ArmBridge.RootFrame.ite_pC, ArmBridge.RootFrame.dite_pC, ArmBridge.RootFrame.ite_pV, ArmBridge.RootFrame.dite_pV, ArmBridge.RootFrame.ite_rPMEVCNTSVR_EL1, ArmBridge.RootFrame.dite_rPMEVCNTSVR_EL1, ArmBridge.RootFrame.ite_rSPESampleCounter, ArmBridge.RootFrame.dite_rSPESampleCounter, ArmBridge.RootFrame.ite_rSPERecordData, ArmBridge.RootFrame.dite_rSPERecordData, ArmBridge.RootFrame.ite_rSP_EL3, ArmBridge.RootFrame.dite_rSP_EL3, ArmBridge.RootFrame.ite_rSP_EL2, ArmBridge.RootFrame.dite_rSP_EL2, ArmBridge.RootFrame.ite_rSP_EL1, ArmBridge.RootFrame.dite_rSP_EL1, ArmBridge.RootFrame.ite_rmpam_vpmr_max, ArmBridge.RootFrame.dite_rmpam_vpmr_max, ArmBridge.RootFrame.ite_rSPE_LFSR, ArmBridge.RootFrame.dite_rSPE_LFSR, ArmBridge.RootFrame.ite_rSPESampleOpType, ArmBridge.RootFrame.dite_rSPESampleOpType, ArmBridge.RootFrame.ite_rTSTATE, ArmBridge.RootFrame.dite_rTSTATE, ArmBridge.RootFrame.ite_rFPSR, ArmBridge.RootFrame.dite_rFPSR, ArmBridge.RootFrame.ite_rFPCR, ArmBridge.RootFrame.dite_rFPCR, ArmBridge.RootFrame.ite_rZT0, ArmBridge.RootFrame.dite_rZT0, ArmBridge.RootFrame.ite_rZA, ArmBridge.RootFrame.dite_rZA, ArmBridge.RootFrame.ite_rFFR, ArmBridge.RootFrame.dite_rFFR, ArmBridge.RootFrame.ite_rP, ArmBridge.RootFrame.dite_rP, ArmBridge.RootFrame.ite_rBTypeCompatible, ArmBridge.RootFrame.dite_rBTypeCompatible, ArmBridge.RootFrame.ite_rRC, ArmBridge.RootFrame.dite_rRC, ArmBridge.RootFrame.ite_rPhysicalCount, ArmBridge.RootFrame.dite_rPhysicalCount, ArmBridge.RootFrame.ite_rPMULastThresholdValue, ArmBridge.RootFrame.dite_rPMULastThresholdValue, ArmBridge.RootFrame.ite_rPMUEventAccumulator, ArmBridge.RootFrame.dite_rPMUEventAccumulator, ArmBridge.RootFrame.ite_rVariantImplemented, ArmBridge.RootFrame.dite_rVariantImplemented, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_32_16, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_32_16, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_32_4, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_32_4, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_64_32, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_64_32, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_64_16, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_64_16, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_64_4, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_64_4, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_32_31, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_32_31, ArmBridge.RootFrame.ite_rbank_BitVec_1, ArmBridge.RootFrame.dite_rbank_BitVec_1, ArmBridge.RootFrame.ite_rbank_BitVec_56, ArmBridge.RootFrame.dite_rbank_BitVec_56, ArmBridge.RootFrame.ite_rbank_BitVec_16, ArmBridge.RootFrame.dite_rbank_BitVec_16, ArmBridge.RootFrame.ite_rbank_BitVec_4, ArmBridge.RootFrame.dite_rbank_BitVec_4, ArmBridge.RootFrame.ite_rbank_Vector_Bool_32, ArmBridge.RootFrame.dite_rbank_Vector_Bool_32, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_64_64, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_64_64, ArmBridge.RootFrame.ite_rbank_Option_InterruptID, ArmBridge.RootFrame.dite_rbank_Option_InterruptID, ArmBridge.RootFrame.ite_rbank_BitVec_8, ArmBridge.RootFrame.dite_rbank_BitVec_8, ArmBridge.RootFrame.ite_rbank_BitVec_2, ArmBridge.RootFrame.dite_rbank_BitVec_2, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_64_7, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_64_7, ArmBridge.RootFrame.ite_rbank_Signal, ArmBridge.RootFrame.dite_rbank_Signal, hel, hspe, maddF, ArmCertCT.CT2.mask, ArmCertCT.CT2.maskPSTATE]
      first | exact ⟨_, rfl⟩ | (refine ArmBridge.RootFrame.dite_ok ?_ ?_ <;> intro _ <;> exact ⟨_, rfl⟩)
  exact ArmBridge.RootFrame.frame_of_root _ maddF t u' ((ArmBridge.BKf.csincP3_complete real Rd Rn Rm t).trans hu)

theorem eret_madd (Rd Rn Rm : BitVec 5) :
    (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 1#2 Rn Rd) 31 12 == 879088#20) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg (fun v => BitVec.getLsbD v 14) h
  unfold CryptoBridge.CondSel.condSelWord at this
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
  simp only [BitVec.getLsbD_append] at this
  simp at this

set_option maxHeartbeats 4000000 in
theorem madd_cong (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t1 t2 : NativeState)
    (hg : t1.regs.gpr = t2.regs.gpr) (hsp : t1.regs.SP_EL0 = t2.regs.SP_EL0) (hz : t1.regs._Z = t2.regs._Z) (hps : t1.regs.PSTATE = t2.regs.PSTATE)
    (hs1 : t1.regs.SP_EL1 = t2.regs.SP_EL1) (hs2 : t1.regs.SP_EL2 = t2.regs.SP_EL2) (hs3 : t1.regs.SP_EL3 = t2.regs.SP_EL3)
    (hel : t1.regs.PSTATE.EL = 0#2) (hspe1 : t1.regs.bank_Bool .SPESampleInFlight = false)
    (hspe2 : t2.regs.bank_Bool .SPESampleInFlight = false) :
    (resSt t1 ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit) t1)).regs.gpr = (resSt t2 ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit) t2)).regs.gpr ∧
    (resSt t1 ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit) t1)).regs.SP_EL0 = (resSt t2 ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit) t2)).regs.SP_EL0 ∧
    (resSt t1 ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit) t1)).regs._Z = (resSt t2 ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit) t2)).regs._Z := by
  have hel2 : t2.regs.PSTATE.EL = 0#2 := hps ▸ hel
  have out : ∀ t : NativeState, ((resSt t ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit) t)).regs.gpr, (resSt t ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit) t)).regs.SP_EL0, (resSt t ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit) t)).regs._Z) =
      (ArmBridge.RootFrame.resVal (t.regs.gpr, t.regs.SP_EL0, t.regs._Z) (ArmBridge.BKf.csincG3_native real Rd Rn Rm t)) :=
    fun t => ArmBridge.RootFrame.val_of_root _ (fun u : NativeState => (u.regs.gpr, u.regs.SP_EL0, u.regs._Z)) t _ (ArmBridge.BKf.csincG3_complete real Rd Rn Rm t)
  have e1 := out t1
  have e2 := out t2
  unfold ArmBridge.BKf.csincG3_native at e1 e2
  have key : (ArmBridge.RootFrame.resVal (t1.regs.gpr, t1.regs.SP_EL0, t1.regs._Z) (ArmBridge.BKf.csincG3_native real Rd Rn Rm t1)) =
      (ArmBridge.RootFrame.resVal (t2.regs.gpr, t2.regs.SP_EL0, t2.regs._Z) (ArmBridge.BKf.csincG3_native real Rd Rn Rm t2)) := by
    unfold ArmBridge.RootFrame.resVal ArmBridge.BKf.csincG3_native
    by_cases hRn : Rd.toNat = 31 <;> by_cases hSPs : t2.regs.PSTATE.SP = 0#1 <;>
    · have hRi : ((Rd.toNat : Int) = 31) ↔ Rd.toNat = 31 := by omega
      simp (config := {maxSteps := 50000000}) only [ArmFull.Register.PSTATE_set, ArmFull.Register.SP_EL0_set, ArmBridge.RootFrame.sw_join1, hRn, hRi, hSPs, dite_true, dite_false, ite_true, ite_false, ↓reduceIte, ↓reduceDIte, Bool.false_eq_true, BitVec.reduceEq, ArmBridge.RootFrame.natcast31, ite_self, dite_eq_ite, ArmBridge.RootFrame.ite_sregs, ArmBridge.RootFrame.dite_sregs, ArmBridge.RootFrame.ite_smem, ArmBridge.RootFrame.dite_smem, ArmBridge.RootFrame.ite_sevents, ArmBridge.RootFrame.dite_sevents, ArmBridge.RootFrame.ite_rbank_Bool, ArmBridge.RootFrame.dite_rbank_Bool, ArmBridge.RootFrame.ite_rFeatureImpl, ArmBridge.RootFrame.dite_rFeatureImpl, ArmBridge.RootFrame.ite_rPSTATE, ArmBridge.RootFrame.dite_rPSTATE, ArmBridge.RootFrame.ite_rBTypeNext, ArmBridge.RootFrame.dite_rBTypeNext, ArmBridge.RootFrame.ite_rBranchTaken, ArmBridge.RootFrame.dite_rBranchTaken, ArmBridge.RootFrame.ite_rPC, ArmBridge.RootFrame.dite_rPC, ArmBridge.RootFrame.ite_rbank_BitVec_64, ArmBridge.RootFrame.dite_rbank_BitVec_64, ArmBridge.RootFrame.ite_rbank_BitVec_32, ArmBridge.RootFrame.dite_rbank_BitVec_32, ArmBridge.RootFrame.ite_rbank_Int, ArmBridge.RootFrame.dite_rbank_Int, ArmBridge.RootFrame.ite_rShouldAdvanceSS, ArmBridge.RootFrame.dite_rShouldAdvanceSS, ArmBridge.RootFrame.ite_rShouldAdvanceIT, ArmBridge.RootFrame.dite_rShouldAdvanceIT, ArmBridge.RootFrame.ite_rThisInstrEnc, ArmBridge.RootFrame.dite_rThisInstrEnc, ArmBridge.RootFrame.ite_rBranchtypetaken, ArmBridge.RootFrame.dite_rBranchtypetaken, ArmBridge.RootFrame.ite_remulator_termination_opcode, ArmBridge.RootFrame.dite_remulator_termination_opcode, ArmBridge.RootFrame.ite_rbank_BitVec_128, ArmBridge.RootFrame.dite_rbank_BitVec_128, ArmBridge.RootFrame.ite_pD, ArmBridge.RootFrame.dite_pD, ArmBridge.RootFrame.ite_pA, ArmBridge.RootFrame.dite_pA, ArmBridge.RootFrame.ite_pI, ArmBridge.RootFrame.dite_pI, ArmBridge.RootFrame.ite_pF, ArmBridge.RootFrame.dite_pF, ArmBridge.RootFrame.ite_pEXLOCK, ArmBridge.RootFrame.dite_pEXLOCK, ArmBridge.RootFrame.ite_pPAN, ArmBridge.RootFrame.dite_pPAN, ArmBridge.RootFrame.ite_pUAO, ArmBridge.RootFrame.dite_pUAO, ArmBridge.RootFrame.ite_pDIT, ArmBridge.RootFrame.dite_pDIT, ArmBridge.RootFrame.ite_pTCO, ArmBridge.RootFrame.dite_pTCO, ArmBridge.RootFrame.ite_pPM, ArmBridge.RootFrame.dite_pPM, ArmBridge.RootFrame.ite_pPPEND, ArmBridge.RootFrame.dite_pPPEND, ArmBridge.RootFrame.ite_pBTYPE, ArmBridge.RootFrame.dite_pBTYPE, ArmBridge.RootFrame.ite_pZA, ArmBridge.RootFrame.dite_pZA, ArmBridge.RootFrame.ite_pSM, ArmBridge.RootFrame.dite_pSM, ArmBridge.RootFrame.ite_pALLINT, ArmBridge.RootFrame.dite_pALLINT, ArmBridge.RootFrame.ite_pSS, ArmBridge.RootFrame.dite_pSS, ArmBridge.RootFrame.ite_pIL, ArmBridge.RootFrame.dite_pIL, ArmBridge.RootFrame.ite_pEL, ArmBridge.RootFrame.dite_pEL, ArmBridge.RootFrame.ite_pnRW, ArmBridge.RootFrame.dite_pnRW, ArmBridge.RootFrame.ite_pSP, ArmBridge.RootFrame.dite_pSP, ArmBridge.RootFrame.ite_pQ, ArmBridge.RootFrame.dite_pQ, ArmBridge.RootFrame.ite_pGE, ArmBridge.RootFrame.dite_pGE, ArmBridge.RootFrame.ite_pSSBS, ArmBridge.RootFrame.dite_pSSBS, ArmBridge.RootFrame.ite_pIT, ArmBridge.RootFrame.dite_pIT, ArmBridge.RootFrame.ite_pJ, ArmBridge.RootFrame.dite_pJ, ArmBridge.RootFrame.ite_pT, ArmBridge.RootFrame.dite_pT, ArmBridge.RootFrame.ite_pE, ArmBridge.RootFrame.dite_pE, ArmBridge.RootFrame.ite_pM, ArmBridge.RootFrame.dite_pM, ArmBridge.RootFrame.ite_rgpr, ArmBridge.RootFrame.dite_rgpr, ArmBridge.RootFrame.ite_rSP_EL0, ArmBridge.RootFrame.dite_rSP_EL0, ArmBridge.RootFrame.ite_rZ, ArmBridge.RootFrame.dite_rZ, ArmBridge.RootFrame.ite_pN, ArmBridge.RootFrame.dite_pN, ArmBridge.RootFrame.ite_pZ, ArmBridge.RootFrame.dite_pZ, ArmBridge.RootFrame.ite_pC, ArmBridge.RootFrame.dite_pC, ArmBridge.RootFrame.ite_pV, ArmBridge.RootFrame.dite_pV, ArmBridge.RootFrame.ite_rPMEVCNTSVR_EL1, ArmBridge.RootFrame.dite_rPMEVCNTSVR_EL1, ArmBridge.RootFrame.ite_rSPESampleCounter, ArmBridge.RootFrame.dite_rSPESampleCounter, ArmBridge.RootFrame.ite_rSPERecordData, ArmBridge.RootFrame.dite_rSPERecordData, ArmBridge.RootFrame.ite_rSP_EL3, ArmBridge.RootFrame.dite_rSP_EL3, ArmBridge.RootFrame.ite_rSP_EL2, ArmBridge.RootFrame.dite_rSP_EL2, ArmBridge.RootFrame.ite_rSP_EL1, ArmBridge.RootFrame.dite_rSP_EL1, ArmBridge.RootFrame.ite_rmpam_vpmr_max, ArmBridge.RootFrame.dite_rmpam_vpmr_max, ArmBridge.RootFrame.ite_rSPE_LFSR, ArmBridge.RootFrame.dite_rSPE_LFSR, ArmBridge.RootFrame.ite_rSPESampleOpType, ArmBridge.RootFrame.dite_rSPESampleOpType, ArmBridge.RootFrame.ite_rTSTATE, ArmBridge.RootFrame.dite_rTSTATE, ArmBridge.RootFrame.ite_rFPSR, ArmBridge.RootFrame.dite_rFPSR, ArmBridge.RootFrame.ite_rFPCR, ArmBridge.RootFrame.dite_rFPCR, ArmBridge.RootFrame.ite_rZT0, ArmBridge.RootFrame.dite_rZT0, ArmBridge.RootFrame.ite_rZA, ArmBridge.RootFrame.dite_rZA, ArmBridge.RootFrame.ite_rFFR, ArmBridge.RootFrame.dite_rFFR, ArmBridge.RootFrame.ite_rP, ArmBridge.RootFrame.dite_rP, ArmBridge.RootFrame.ite_rBTypeCompatible, ArmBridge.RootFrame.dite_rBTypeCompatible, ArmBridge.RootFrame.ite_rRC, ArmBridge.RootFrame.dite_rRC, ArmBridge.RootFrame.ite_rPhysicalCount, ArmBridge.RootFrame.dite_rPhysicalCount, ArmBridge.RootFrame.ite_rPMULastThresholdValue, ArmBridge.RootFrame.dite_rPMULastThresholdValue, ArmBridge.RootFrame.ite_rPMUEventAccumulator, ArmBridge.RootFrame.dite_rPMUEventAccumulator, ArmBridge.RootFrame.ite_rVariantImplemented, ArmBridge.RootFrame.dite_rVariantImplemented, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_32_16, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_32_16, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_32_4, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_32_4, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_64_32, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_64_32, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_64_16, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_64_16, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_64_4, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_64_4, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_32_31, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_32_31, ArmBridge.RootFrame.ite_rbank_BitVec_1, ArmBridge.RootFrame.dite_rbank_BitVec_1, ArmBridge.RootFrame.ite_rbank_BitVec_56, ArmBridge.RootFrame.dite_rbank_BitVec_56, ArmBridge.RootFrame.ite_rbank_BitVec_16, ArmBridge.RootFrame.dite_rbank_BitVec_16, ArmBridge.RootFrame.ite_rbank_BitVec_4, ArmBridge.RootFrame.dite_rbank_BitVec_4, ArmBridge.RootFrame.ite_rbank_Vector_Bool_32, ArmBridge.RootFrame.dite_rbank_Vector_Bool_32, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_64_64, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_64_64, ArmBridge.RootFrame.ite_rbank_Option_InterruptID, ArmBridge.RootFrame.dite_rbank_Option_InterruptID, ArmBridge.RootFrame.ite_rbank_BitVec_8, ArmBridge.RootFrame.dite_rbank_BitVec_8, ArmBridge.RootFrame.ite_rbank_BitVec_2, ArmBridge.RootFrame.dite_rbank_BitVec_2, ArmBridge.RootFrame.ite_rbank_Vector_BitVec_64_7, ArmBridge.RootFrame.dite_rbank_Vector_BitVec_64_7, ArmBridge.RootFrame.ite_rbank_Signal, ArmBridge.RootFrame.dite_rbank_Signal, hg, hsp, hz, hps, hs1, hs2, hs3, hel, hel2, hspe1, hspe2]
  have := (out t1).trans (key.trans (out t2).symm)
  simp only [Prod.mk.injEq] at this
  exact this

theorem act_frame (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t : NativeState) :
    ActFrame t (RG Rd Rn Rm t) := by
  unfold RG
  split
  · rename_i hg
    have h := (madd_frame real Rd Rn Rm t hg).2
    unfold maddF at h
    exact ⟨congrArg (fun x => x.1) h, congrArg (fun x => x.2.1) h, (by rw [show (resSt t (((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit)) t)).regs.PSTATE = t.regs.PSTATE from congrArg (fun x => x.2.2.1) h]), congrArg (fun x => x.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem act_cong (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t1 t2 : NativeState) (h : CongIn t1 t2) :
    CongOut (RG Rd Rn Rm t1) (RG Rd Rn Rm t2) := by
  have hel2 : t2.regs.PSTATE.EL = 0#2 := h.ps ▸ h.el0
  by_cases hg1 : Guard t1
  · have hg2 : Guard t2 := ⟨hel2, h.sys.spe.symm.trans hg1.2⟩
    unfold RG
    rw [if_pos hg1, if_pos hg2]
    have hc := madd_cong real Rd Rn Rm t1 t2 h.gpr h.sp h.z h.ps h.spx1 h.spx2 h.spx3 h.el0 hg1.2 hg2.2
    have m1 := (madd_frame real Rd Rn Rm t1 hg1).2
    have m2 := (madd_frame real Rd Rn Rm t2 hg2).2
    unfold maddF at m1 m2
    have e1 : (resSt t1 (((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit)) t1)).mem = t1.mem := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) m1
    have e2 : (resSt t2 (((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit)) t2)).mem = t2.mem := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) m2
    have p1 : (resSt t1 (((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit)) t1)).regs.PSTATE = t1.regs.PSTATE := congrArg (fun x => x.2.2.1) m1
    have p2 : (resSt t2 (((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn 1#1 3#4 Rm 0#1 1#1 : SailM Unit)) t2)).regs.PSTATE = t2.regs.PSTATE := congrArg (fun x => x.2.2.1) m2
    refine ⟨?_, hc.1, hc.2.1, hc.2.2, ?_, ?_, ?_, ?_⟩
    · rw [e1, e2, h.mem]
    all_goals (rw [p1, p2, h.ps])
  · have hg2 : ¬ Guard t2 := fun g2 => hg1 ⟨h.el0, h.sys.spe.trans g2.2⟩
    unfold RG
    rw [if_neg hg1, if_neg hg2]
    exact ⟨h.mem, h.gpr, h.sp, h.z, congrArg ProcState.N h.ps, congrArg ProcState.Z h.ps, congrArg ProcState.C h.ps,
      congrArg ProcState.V h.ps⟩

theorem act_npe (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t : NativeState) :
    ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs (RG Rd Rn Rm t).regs := by
  unfold RG
  split
  · rename_i hg
    have h := (madd_frame real Rd Rn Rm t hg).2
    unfold maddF at h
    exact congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h
  · rfl

theorem act_gic (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t : NativeState) :
    (RG Rd Rn Rm t).regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending := by
  unfold RG
  split
  · rename_i hg
    have h := (madd_frame real Rd Rn Rm t hg).2
    unfold maddF at h
    exact congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) h
  · rfl

end ArmBridge.CruxICsinc3

