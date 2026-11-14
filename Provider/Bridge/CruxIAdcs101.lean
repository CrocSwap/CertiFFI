import Bridge.CruxGen
import Bridge.PSRest
import Bridge.RootFrame
import Bridge.CruxNonProj
import Bridge.AdcBridgeM
import Bridge.DispAdcs101
import BKf.adcsP101
import BKf.adcsG101
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.CruxGen ArmBridge.PSRest ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.CruxCore
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.CruxIAdcs101LNSym.
namespace ArmBridge.CruxIAdcs101

def maddF (u : NativeState) :=
  (u.regs.bank_Bool, u.regs.FeatureImpl, (u.regs.PSTATE.D, u.regs.PSTATE.A, u.regs.PSTATE.I, u.regs.PSTATE.F, u.regs.PSTATE.EXLOCK, u.regs.PSTATE.PAN, u.regs.PSTATE.UAO, u.regs.PSTATE.DIT, u.regs.PSTATE.TCO, u.regs.PSTATE.PM, u.regs.PSTATE.PPEND, u.regs.PSTATE.BTYPE, u.regs.PSTATE.ZA, u.regs.PSTATE.SM, u.regs.PSTATE.ALLINT, u.regs.PSTATE.SS, u.regs.PSTATE.IL, u.regs.PSTATE.EL, u.regs.PSTATE.nRW, u.regs.PSTATE.SP, u.regs.PSTATE.Q, u.regs.PSTATE.GE, u.regs.PSTATE.SSBS, u.regs.PSTATE.IT, u.regs.PSTATE.J, u.regs.PSTATE.T, u.regs.PSTATE.E, u.regs.PSTATE.M), u.regs.BTypeNext, u.regs.__BranchTaken, u.regs._PC,
    u.regs.bank_BitVec_64, u.regs.bank_BitVec_32, u.regs.bank_Int, u.regs.ShouldAdvanceSS, u.regs.ShouldAdvanceIT,
    u.regs.__ThisInstrEnc, u.mem, u.events, u.regs.Branchtypetaken, u.regs.__emulator_termination_opcode, u.regs.bank_BitVec_128,
    ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap u.regs, u.regs.bank_Option_InterruptID .__GIC_Pending)

set_option maxHeartbeats 4000000 in
theorem madd_frame (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t : NativeState) :
    (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t =
      .ok () (resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t)) ∧
    maddF (resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t))
      = maddF t := by
  obtain ⟨u', hu⟩ : ∃ u', ArmBridge.BKf.adcsP101_native real Rd Rn Rm t = .ok (maddF t) u' := by
    unfold ArmBridge.BKf.adcsP101_native
    (try simp only [dif_pos (movz_bound hv)])
    (try simp (config := {maxSteps := 20000000}) only [ArmFull.Register.PSTATE_set])
    first | exact ⟨_, rfl⟩ | (refine ArmBridge.RootFrame.dite_ok ?_ ?_ <;> intro _ <;> first | exact ⟨_, rfl⟩ | (refine ArmBridge.RootFrame.dite_ok ?_ ?_ <;> intro _ <;> exact ⟨_, rfl⟩)) | (split <;> exact ⟨_, rfl⟩)
  exact ArmBridge.RootFrame.frame_of_root _ maddF t u' ((ArmBridge.BKf.adcsP101_complete real Rd Rn Rm t).trans hu)

theorem eret_madd (Rd Rn Rm : BitVec 5) :
    (Sail.BitVec.extractLsb (adcWord 1#1 0#1 1#1 Rm Rn Rd) 31 12 == 879088#20) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg (fun v => BitVec.getLsbD v 14) h
  unfold adcWord at this
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
  simp only [BitVec.getLsbD_append] at this
  simp at this

set_option maxHeartbeats 4000000 in
theorem madd_cong (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t1 t2 : NativeState)
    (hg : t1.regs.gpr = t2.regs.gpr) (hsp : t1.regs.SP_EL0 = t2.regs.SP_EL0) (hz : t1.regs._Z = t2.regs._Z) (hps : t1.regs.PSTATE = t2.regs.PSTATE)
    (hs1 : t1.regs.SP_EL1 = t2.regs.SP_EL1) (hs2 : t1.regs.SP_EL2 = t2.regs.SP_EL2) (hs3 : t1.regs.SP_EL3 = t2.regs.SP_EL3)
    (hel : t1.regs.PSTATE.EL = 0#2)
    (hc : t1.regs.PSTATE.C = t2.regs.PSTATE.C) :
    (resSt t1 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t1)).regs.gpr = (resSt t2 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t2)).regs.gpr ∧
    (resSt t1 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t1)).regs.SP_EL0 = (resSt t2 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t2)).regs.SP_EL0 ∧
    (resSt t1 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t1)).regs._Z = (resSt t2 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t2)).regs._Z ∧
    (resSt t1 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t1)).regs.PSTATE.N = (resSt t2 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t2)).regs.PSTATE.N ∧
    (resSt t1 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t1)).regs.PSTATE.Z = (resSt t2 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t2)).regs.PSTATE.Z ∧
    (resSt t1 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t1)).regs.PSTATE.C = (resSt t2 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t2)).regs.PSTATE.C ∧
    (resSt t1 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t1)).regs.PSTATE.V = (resSt t2 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t2)).regs.PSTATE.V := by
  have hel2 : t2.regs.PSTATE.EL = 0#2 := hps ▸ hel
  have out : ∀ t : NativeState, ((resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t)).regs.gpr, (resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t)).regs.SP_EL0, (resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t)).regs._Z, (resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t)).regs.PSTATE.N, (resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t)).regs.PSTATE.Z, (resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t)).regs.PSTATE.C, (resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t)).regs.PSTATE.V) =
      (ArmBridge.RootFrame.resVal (t.regs.gpr, t.regs.SP_EL0, t.regs._Z, t.regs.PSTATE.N, t.regs.PSTATE.Z, t.regs.PSTATE.C, t.regs.PSTATE.V) (ArmBridge.BKf.adcsG101_native real Rd Rn Rm t)) :=
    fun t => ArmBridge.RootFrame.val_of_root _ (fun u : NativeState => (u.regs.gpr, u.regs.SP_EL0, u.regs._Z, u.regs.PSTATE.N, u.regs.PSTATE.Z, u.regs.PSTATE.C, u.regs.PSTATE.V)) t _ (ArmBridge.BKf.adcsG101_complete real Rd Rn Rm t)
  have e1 := out t1
  have e2 := out t2
  unfold ArmBridge.BKf.adcsG101_native at e1 e2
  have key : (ArmBridge.RootFrame.resVal (t1.regs.gpr, t1.regs.SP_EL0, t1.regs._Z, t1.regs.PSTATE.N, t1.regs.PSTATE.Z, t1.regs.PSTATE.C, t1.regs.PSTATE.V) (ArmBridge.BKf.adcsG101_native real Rd Rn Rm t1)) =
      (ArmBridge.RootFrame.resVal (t2.regs.gpr, t2.regs.SP_EL0, t2.regs._Z, t2.regs.PSTATE.N, t2.regs.PSTATE.Z, t2.regs.PSTATE.C, t2.regs.PSTATE.V) (ArmBridge.BKf.adcsG101_native real Rd Rn Rm t2)) := by
    unfold ArmBridge.RootFrame.resVal ArmBridge.BKf.adcsG101_native
    by_cases hR : ((Rd.toNat : Int) = 31)
    · simp only [ArmFull.Register.PSTATE_set, ArmBridge.RootFrame.sw_join1, hR, dite_true, ArmFull.Register.SP_EL0_set, hg, hsp, hz, hps, hs1, hs2, hs3, hel, hel2, hc]
    · simp only [ArmFull.Register.PSTATE_set, ArmBridge.RootFrame.sw_join1, hR, dite_false]
      simp only [ArmFull.Register.PSTATE_set, ArmBridge.RootFrame.sw_join1, ArmFull.Register.SP_EL0_set, hg, hsp, hz, hps, hs1, hs2, hs3, hel, hel2, hc]
  have := (out t1).trans (key.trans (out t2).symm)
  simp only [Prod.mk.injEq] at this
  exact this

theorem act_frame (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t : NativeState) :
    ActFrame t (resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t)) := by
  have h := (madd_frame real Rd Rn Rm t).2
  unfold maddF at h
  exact ⟨congrArg (fun x => x.1) h, congrArg (fun x => x.2.1) h, erase_of_rest _ _ (congrArg (fun x => x.2.2.1) h), congrArg (fun x => x.2.2.2.1) h,
    congrArg (fun x => x.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.1) h,
    congrArg (fun x => x.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.1) h,
    congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h⟩

theorem act_cong (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t1 t2 : NativeState) (h : CongIn t1 t2) :
    CongOut (resSt t1 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t1)) (resSt t2 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t2)) := by
  have hc := madd_cong real Rd Rn Rm t1 t2 h.gpr h.sp h.z h.ps h.spx1 h.spx2 h.spx3 h.el0 (congrArg ProcState.C h.ps)
  have m1 := (madd_frame real Rd Rn Rm t1).2
  have m2 := (madd_frame real Rd Rn Rm t2).2
  unfold maddF at m1 m2
  have e1 : (resSt t1 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t1)).mem = t1.mem := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) m1
  have e2 : (resSt t2 ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t2)).mem = t2.mem := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) m2
  
  refine ⟨?_, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2⟩
  · rw [e1, e2, h.mem]
  

theorem act_npe (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t : NativeState) :
    ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs (resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t)).regs := by
  have h := (madd_frame real Rd Rn Rm t).2
  unfold maddF at h
  exact congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h

theorem act_gic (real : Type) [Sail.SailReal real] (Rd Rn Rm : BitVec 5) (t : NativeState) :
    (resSt t ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 1#1 0#1 1#1 : SailM Unit) t)).regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending := by
  have h := (madd_frame real Rd Rn Rm t).2
  unfold maddF at h
  exact congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) h

end ArmBridge.CruxIAdcs101

