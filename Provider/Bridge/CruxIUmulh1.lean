import Bridge.CruxGen
import Bridge.PSRest
import Bridge.RootFrame
import Bridge.CruxNonProj
import Bridge.UmulhBridgeM
import Bridge.DispUmulh1
import BKf.umulhP1
import BKf.umulhG1
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.CruxGen ArmBridge.PSRest ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.CruxCore
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.CruxIUmulh1LNSym.
namespace ArmBridge.CruxIUmulh1

def maddF (u : NativeState) :=
  (u.regs.bank_Bool, u.regs.FeatureImpl, u.regs.PSTATE, u.regs.BTypeNext, u.regs.__BranchTaken, u.regs._PC,
    u.regs.bank_BitVec_64, u.regs.bank_BitVec_32, u.regs.bank_Int, u.regs.ShouldAdvanceSS, u.regs.ShouldAdvanceIT,
    u.regs.__ThisInstrEnc, u.mem, u.events, u.regs.Branchtypetaken, u.regs.__emulator_termination_opcode, u.regs.bank_BitVec_128,
    ArmCertCT.CT2.mask ArmBridge.CruxNonProj.bkHeap u.regs, u.regs.bank_Option_InterruptID .__GIC_Pending)

set_option maxHeartbeats 4000000 in
theorem madd_frame (real : Type) [Sail.SailReal real] (Rd Rn Ra Rm : BitVec 5) (t : NativeState) :
    (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t =
      .ok () (resSt t ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t)) ∧
    maddF (resSt t ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t))
      = maddF t := by
  obtain ⟨u', hu⟩ : ∃ u', ArmBridge.BKf.umulhP1_native real Rd Rn Ra Rm t = .ok (maddF t) u' := by
    unfold ArmBridge.BKf.umulhP1_native
    (try simp only [dif_pos (movz_bound hv)])
    (try simp (config := {maxSteps := 20000000}) only [ArmFull.Register.PSTATE_set])
    first | exact ⟨_, rfl⟩ | (refine ArmBridge.RootFrame.dite_ok ?_ ?_ <;> intro _ <;> first | exact ⟨_, rfl⟩ | (refine ArmBridge.RootFrame.dite_ok ?_ ?_ <;> intro _ <;> exact ⟨_, rfl⟩)) | (split <;> exact ⟨_, rfl⟩)
  exact ArmBridge.RootFrame.frame_of_root _ maddF t u' ((ArmBridge.BKf.umulhP1_complete real Rd Rn Ra Rm t).trans hu)

theorem eret_madd (Rm Ra Rn Rd : BitVec 5) :
    (Sail.BitVec.extractLsb (umulhWord 1#1 Rm Ra Rn Rd) 31 12 == 879088#20) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg (fun v => BitVec.getLsbD v 18) h
  unfold umulhWord at this
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
  simp only [BitVec.getLsbD_append] at this
  simp at this

set_option maxHeartbeats 4000000 in
theorem madd_cong (real : Type) [Sail.SailReal real] (Rd Rn Ra Rm : BitVec 5) (t1 t2 : NativeState)
    (hg : t1.regs.gpr = t2.regs.gpr) (hsp : t1.regs.SP_EL0 = t2.regs.SP_EL0) (hz : t1.regs._Z = t2.regs._Z) (hps : t1.regs.PSTATE = t2.regs.PSTATE)
    (hs1 : t1.regs.SP_EL1 = t2.regs.SP_EL1) (hs2 : t1.regs.SP_EL2 = t2.regs.SP_EL2) (hs3 : t1.regs.SP_EL3 = t2.regs.SP_EL3)
    (hel : t1.regs.PSTATE.EL = 0#2) :
    (resSt t1 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t1)).regs.gpr = (resSt t2 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t2)).regs.gpr ∧
    (resSt t1 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t1)).regs.SP_EL0 = (resSt t2 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t2)).regs.SP_EL0 ∧
    (resSt t1 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t1)).regs._Z = (resSt t2 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t2)).regs._Z := by
  have hel2 : t2.regs.PSTATE.EL = 0#2 := hps ▸ hel
  have out : ∀ t : NativeState, ((resSt t ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t)).regs.gpr, (resSt t ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t)).regs.SP_EL0, (resSt t ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t)).regs._Z) =
      (ArmBridge.RootFrame.resVal (t.regs.gpr, t.regs.SP_EL0, t.regs._Z) (ArmBridge.BKf.umulhG1_native real Rd Rn Ra Rm t)) :=
    fun t => ArmBridge.RootFrame.val_of_root _ (fun u : NativeState => (u.regs.gpr, u.regs.SP_EL0, u.regs._Z)) t _ (ArmBridge.BKf.umulhG1_complete real Rd Rn Ra Rm t)
  have e1 := out t1
  have e2 := out t2
  unfold ArmBridge.BKf.umulhG1_native at e1 e2
  have key : (ArmBridge.RootFrame.resVal (t1.regs.gpr, t1.regs.SP_EL0, t1.regs._Z) (ArmBridge.BKf.umulhG1_native real Rd Rn Ra Rm t1)) =
      (ArmBridge.RootFrame.resVal (t2.regs.gpr, t2.regs.SP_EL0, t2.regs._Z) (ArmBridge.BKf.umulhG1_native real Rd Rn Ra Rm t2)) := by
    unfold ArmBridge.RootFrame.resVal ArmBridge.BKf.umulhG1_native
    by_cases hR : ((Rd.toNat : Int) = 31)
    · simp only [ArmFull.Register.PSTATE_set, ArmBridge.RootFrame.sw_join1, hR, dite_true, ArmFull.Register.SP_EL0_set, hg, hsp, hz, hps, hs1, hs2, hs3, hel, hel2]
    · simp only [ArmFull.Register.PSTATE_set, ArmBridge.RootFrame.sw_join1, hR, dite_false]
      simp only [ArmFull.Register.PSTATE_set, ArmBridge.RootFrame.sw_join1, ArmFull.Register.SP_EL0_set, hg, hsp, hz, hps, hs1, hs2, hs3, hel, hel2]
  have := (out t1).trans (key.trans (out t2).symm)
  simp only [Prod.mk.injEq] at this
  exact this

theorem act_frame (real : Type) [Sail.SailReal real] (Rd Rn Ra Rm : BitVec 5) (t : NativeState) :
    ActFrame t (resSt t ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t)) := by
  have h := (madd_frame real Rd Rn Ra Rm t).2
  unfold maddF at h
  exact ⟨congrArg (fun x => x.1) h, congrArg (fun x => x.2.1) h, (by rw [show (resSt t ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t)).regs.PSTATE = t.regs.PSTATE from congrArg (fun x => x.2.2.1) h]), congrArg (fun x => x.2.2.2.1) h,
    congrArg (fun x => x.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.1) h,
    congrArg (fun x => x.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.1) h,
    congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h, congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h⟩

theorem act_cong (real : Type) [Sail.SailReal real] (Rd Rn Ra Rm : BitVec 5) (t1 t2 : NativeState) (h : CongIn t1 t2) :
    CongOut (resSt t1 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t1)) (resSt t2 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t2)) := by
  have hc := madd_cong real Rd Rn Ra Rm t1 t2 h.gpr h.sp h.z h.ps h.spx1 h.spx2 h.spx3 h.el0
  have m1 := (madd_frame real Rd Rn Ra Rm t1).2
  have m2 := (madd_frame real Rd Rn Ra Rm t2).2
  unfold maddF at m1 m2
  have e1 : (resSt t1 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t1)).mem = t1.mem := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) m1
  have e2 : (resSt t2 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t2)).mem = t2.mem := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) m2
  have p1 : (resSt t1 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t1)).regs.PSTATE = t1.regs.PSTATE := congrArg (fun x => x.2.2.1) m1
  have p2 : (resSt t2 ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t2)).regs.PSTATE = t2.regs.PSTATE := congrArg (fun x => x.2.2.1) m2
  refine ⟨?_, hc.1, hc.2.1, hc.2.2, ?_, ?_, ?_, ?_⟩
  · rw [e1, e2, h.mem]
  all_goals (rw [p1, p2, h.ps])

theorem act_npe (real : Type) [Sail.SailReal real] (Rd Rn Ra Rm : BitVec 5) (t : NativeState) :
    ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs (resSt t ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t)).regs := by
  have h := (madd_frame real Rd Rn Ra Rm t).2
  unfold maddF at h
  exact congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h

theorem act_gic (real : Type) [Sail.SailReal real] (Rd Rn Ra Rm : BitVec 5) (t : NativeState) :
    (resSt t ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn 31#5 Rm 1#1 : SailM Unit) t)).regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending := by
  have h := (madd_frame real Rd Rn Ra Rm t).2
  unfold maddF at h
  exact congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) h

end ArmBridge.CruxIUmulh1

