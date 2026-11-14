import CruxMem.LdrbPre
import CruxMem.DispLdrbPost
import Bridge.CruxGen
import CruxMem.NbCommon
import MemM1.MemInv
import Pilot.LoopFrame
import Pilot.ExceptLoop
import Pilot.InvariantLoop
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.CruxGen ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.CruxCore
open CryptoMem.LdstPost ArmCertMem.LdrbPre ArmCertMem.LdrbEval
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CruxMem.CruxLdrbLNSym.
namespace ArmCertMem.CruxLdrb

-- StepRuntime companions referenced by oleans (BK3/BKmin); loaded for a complete environment

/-! LDRB (immediate, post-index; size=00, opc=01) memory-form modelStep crux: `crux_gen` with
`A := decode_ldrb_..._post_idx Rt Rn imm9 1#2 0#2` and `R t := if Pre t then resSt t (A t) else t`. -/

open Classical in
/-- The action result map: the leaf result on `Pre` states, identity elsewhere. -/
noncomputable def ldrbR (s0 : NativeState) (P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page) (TB : Nat → Prop)
    (Rn Rt : BitVec 5) (imm9 : BitVec 9) (t : NativeState) : NativeState :=
  if Pre s0 P4 P2 TB Rn t then resSt t ((decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2 : SailM Unit) t) else t

/-- decode_ldrb_eval under `Pre` (memInv_agrees supplies E17 v3 + DataPins). -/
theorem eval_pre {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {Rn Rt : BitVec 5} (imm9 : BitVec 9) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    {t : NativeState} (hp : Pre s0 P4 P2 TB Rn t) (v : BitVec 8)
    (hv : t.mem[((MemM1.ConsumerB.kmapB P4 P2).pa (addr t Rn)).toNat]? = some v) :
    ldrbR s0 P4 P2 TB Rn Rt imm9 t = resSt t ((decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2 : SailM Unit) t) ∧
    ∃ u, (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2 : SailM Unit) t = .ok () u ∧ u.regs = (ldrbPost t Rn Rt imm9 v).regs ∧ u.mem = t.mem := by
  obtain ⟨hT, -, hD⟩ := MemM1.MemInv.memInv_agrees s0 P4 P2 TB t hp.inv
  obtain ⟨u, hu, hr, hm, -⟩ := decode_ldrb_eval (MemM1.ConsumerB.kmapB P4 P2) _ t imm9 Rn Rt hRn hRt hRnt hT hD hp.be
    hp.f7 hp.f3 hp.perm hp.io v hv
  exact ⟨by unfold ldrbR; rw [if_pos hp], u, hu, hr, hm⟩

theorem act_ok {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {Rn Rt : BitVec 5} (imm9 : BitVec 9) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    {s t : NativeState} (hPre : Pre s0 P4 P2 TB Rn s) (hc : CongIn s t) :
    (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2 : SailM Unit) t = .ok () (ldrbR s0 P4 P2 TB Rn Rt imm9 t) := by
  have hp := pre_congr hc hPre
  obtain ⟨v, hv⟩ := hp.byte
  obtain ⟨hR, u, hu, -⟩ := eval_pre (Rt := Rt) imm9 hRn hRt hRnt hp v hv
  rw [hR, hu]
  rfl

theorem act_frame {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {Rn Rt : BitVec 5} (imm9 : BitVec 9) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (t : NativeState) : ActFrame t (ldrbR s0 P4 P2 TB Rn Rt imm9 t) := by
  by_cases hp : Pre s0 P4 P2 TB Rn t
  · obtain ⟨v, hv⟩ := hp.byte
    obtain ⟨hR, u, hu, hr, -⟩ := eval_pre (Rt := Rt) imm9 hRn hRt hRnt hp v hv
    rw [hR, hu]
    show ActFrame t u
    constructor <;> (rw [hr]; try rfl)
  · have hR : ldrbR s0 P4 P2 TB Rn Rt imm9 t = t := by unfold ldrbR; rw [if_neg hp]
    rw [hR]
    constructor <;> rfl

theorem act_cong {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {Rn Rt : BitVec 5} (imm9 : BitVec 9) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (t1 t2 : NativeState) (hc : CongIn t1 t2) :
    CongOut (ldrbR s0 P4 P2 TB Rn Rt imm9 t1) (ldrbR s0 P4 P2 TB Rn Rt imm9 t2) := by
  by_cases hp1 : Pre s0 P4 P2 TB Rn t1
  · have hp2 := pre_congr hc hp1
    obtain ⟨v, hv⟩ := hp1.byte
    have ha : addr t2 Rn = addr t1 Rn := by simp only [addr, hc.gpr]
    have hv2 : t2.mem[((MemM1.ConsumerB.kmapB P4 P2).pa (addr t2 Rn)).toNat]? = some v := by
      rw [ha, ← hc.mem]; exact hv
    obtain ⟨hR1, u1, hu1, hr1, hm1⟩ := eval_pre (Rt := Rt) imm9 hRn hRt hRnt hp1 v hv
    obtain ⟨hR2, u2, hu2, hr2, hm2⟩ := eval_pre (Rt := Rt) imm9 hRn hRt hRnt hp2 v hv2
    rw [hR1, hR2, hu1, hu2]
    show CongOut u1 u2
    refine ⟨by rw [hm1, hm2, hc.mem], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hr1, hr2]; simp only [ldrbPost, CryptoMem.MemCore.setGpr, hc.gpr]
    · rw [hr1, hr2]; exact hc.sp
    · rw [hr1, hr2]; exact hc.z
    · rw [hr1, hr2]; exact congrArg ProcState.N hc.ps
    · rw [hr1, hr2]; exact congrArg ProcState.Z hc.ps
    · rw [hr1, hr2]; exact congrArg ProcState.C hc.ps
    · rw [hr1, hr2]; exact congrArg ProcState.V hc.ps
  · have hp2 : ¬ Pre s0 P4 P2 TB Rn t2 := fun h => hp1 (pre_congr (congIn_symm hc) h)
    have hR1 : ldrbR s0 P4 P2 TB Rn Rt imm9 t1 = t1 := by unfold ldrbR; rw [if_neg hp1]
    have hR2 : ldrbR s0 P4 P2 TB Rn Rt imm9 t2 = t2 := by unfold ldrbR; rw [if_neg hp2]
    rw [hR1, hR2]
    exact ⟨hc.mem, hc.gpr, hc.sp, hc.z, congrArg ProcState.N hc.ps, congrArg ProcState.Z hc.ps,
      congrArg ProcState.C hc.ps, congrArg ProcState.V hc.ps⟩

theorem act_npe {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {Rn Rt : BitVec 5} (imm9 : BitVec 9) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (t : NativeState) : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs (ldrbR s0 P4 P2 TB Rn Rt imm9 t).regs := by
  by_cases hp : Pre s0 P4 P2 TB Rn t
  · obtain ⟨v, hv⟩ := hp.byte
    obtain ⟨hR, u, hu, hr, -⟩ := eval_pre (Rt := Rt) imm9 hRn hRt hRnt hp v hv
    rw [hR, hu]
    show ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs
    unfold ArmCertCT.CT2.NonProjRegsEq
    rw [hr]
    try rfl
  · have hR : ldrbR s0 P4 P2 TB Rn Rt imm9 t = t := by unfold ldrbR; rw [if_neg hp]
    rw [hR]
    exact ArmCertCT.CT2.NonProjRegsEq.refl _ _

theorem act_gic {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {Rn Rt : BitVec 5} (imm9 : BitVec 9) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (t : NativeState) : (ldrbR s0 P4 P2 TB Rn Rt imm9 t).regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending := by
  by_cases hp : Pre s0 P4 P2 TB Rn t
  · obtain ⟨v, hv⟩ := hp.byte
    obtain ⟨hR, u, hu, hr, -⟩ := eval_pre (Rt := Rt) imm9 hRn hRt hRnt hp v hv
    rw [hR, hu]
    show u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending
    rw [hr]
    try rfl
  · have hR : ldrbR s0 P4 P2 TB Rn Rt imm9 t = t := by unfold ldrbR; rw [if_neg hp]
    rw [hR]

theorem act_um {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {Rn Rt : BitVec 5} (imm9 : BitVec 9) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (t : NativeState) : ArmBridge.BoundaryV2.UnmappedSame (MemM1.ConsumerB.kmapB P4 P2) t (ldrbR s0 P4 P2 TB Rn Rt imm9 t) := by
  by_cases hp : Pre s0 P4 P2 TB Rn t
  · obtain ⟨v, hv⟩ := hp.byte
    obtain ⟨hR, u, hu, hr, hm⟩ := eval_pre (Rt := Rt) imm9 hRn hRt hRnt hp v hv
    rw [hR, hu]
    show ArmBridge.BoundaryV2.UnmappedSame (MemM1.ConsumerB.kmapB P4 P2) t u
    intro q _ _
    rw [hm]
  · have hR : ldrbR s0 P4 P2 TB Rn Rt imm9 t = t := by unfold ldrbR; rw [if_neg hp]
    rw [hR]
    exact ArmBridge.BoundaryV2.UnmappedSame.refl _ _

theorem eret_ldrb (imm9 : BitVec 9) (Rn Rt : BitVec 5) :
    (Sail.BitVec.extractLsb (ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 12 == 879088#20) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg (fun v => BitVec.getLsbD v 19) h
  unfold ldstPostWord at this
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
  simp only [BitVec.getLsbD_append] at this
  simp at this

end ArmCertMem.CruxLdrb

