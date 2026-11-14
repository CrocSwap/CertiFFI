import CruxMem.StpEval
import CruxMem.StpnEval
import CruxMem.CruxLdpn
import CruxMem.LdpEval
import CruxMem.LdrbPre
import CruxMem.DispStpGen
import CryptoMem.Stpn
import Bridge.CruxGen
import CruxMem.NbCommon
import MemM1.MemInv
import Pilot.LoopFrame
import Pilot.ExceptLoop
import Pilot.InvariantLoop
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.CruxGen ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.CruxCore
open CryptoMem.LdstPair ArmCertMem.StpEval ArmCertMem.StpnEval
open ArmCertMem.CruxLdpn (pairAddr)
open ArmCertMem.LdpEval (ldpAddr)
open ArmCertMem.LdrbPre (sysEq2_of_congIn congIn_symm)
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CruxMem.CruxStpnLNSym.
namespace ArmCertMem.CruxStpn

-- StepRuntime companions referenced by oleans (BK3/BKmin); loaded for a complete environment

/-! STP (64-bit, signed offset, general base Rn < 31, 16-aligned) memory-form modelStep crux: `crux_gen` with
`A := decode_stp_gen_..._offset Rt Rn Rt2 imm7 0#1 2#2` and `R t := if Pre t then resSt t (A t) else t`. -/

/-- CongIn-invariant precondition: memory's run invariant, BEPins, FEAT_EL3 bits, address alignment,
    per-access facts at X[Rn] + (SignExtend(imm7) << 3) (permitted for 16 bytes, not MMIO). -/
structure Pre (s0 : NativeState) (P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page) (TB : Nat → Prop)
    (Rn : BitVec 5) (imm7 : BitVec 7) (t : NativeState) : Prop where
  inv : MemM1.MemInv.MemInv s0 P4 P2 TB t
  be : MemM1.MemDataV3.BEPins t.regs
  f7 : t.regs.FeatureImpl[7] = true
  f3 : t.regs.FeatureImpl[3] = false
  al : (pairAddr t Rn imm7).toNat % 16 = 0
  perm : ∀ acc, MemM1.Witness.Acc0 acc → (MemM1.ConsumerB.kmapB P4 P2).permitted (pairAddr t Rn imm7) acc true 16
  io : MemM1.MemReadIF.NotMMIO ((MemM1.ConsumerB.kmapB P4 P2).pa (pairAddr t Rn imm7))

theorem pre_congr {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {Rn : BitVec 5} {imm7 : BitVec 7} {t1 t2 : NativeState} (hc : CongIn t1 t2) (h : Pre s0 P4 P2 TB Rn imm7 t1) :
    Pre s0 P4 P2 TB Rn imm7 t2 := by
  have hs := sysEq2_of_congIn hc
  have hf : t2.regs.FeatureImpl = t1.regs.FeatureImpl := hs.feat
  have ha : pairAddr t2 Rn imm7 = pairAddr t1 Rn imm7 := by simp only [pairAddr, hc.gpr]
  refine ⟨⟨h.inv.1, h.inv.2.1.trans hs, fun p h1 h2 => by rw [← hc.mem]; exact h.inv.2.2 p h1 h2⟩,
    ⟨by rw [← hc.ps]; exact h.be.el0, by rw [← hc.ps]; exact h.be.nrw, by rw [hf]; exact h.be.noRME,
     by rw [hf]; exact h.be.vhe, by rw [hf]; exact h.be.aa64el0, by rw [hs.scr]; exact h.be.ns,
     by rw [hs.hcr]; exact h.be.e2h, by rw [hs.hcr]; exact h.be.tge⟩,
    by rw [hf]; exact h.f7, by rw [hf]; exact h.f3, by rw [ha]; exact h.al,
    by rw [ha]; exact h.perm, by rw [ha]; exact h.io⟩

open Classical in
/-- The action result map: the leaf result on `Pre` states, identity elsewhere. -/
noncomputable def stpnR (s0 : NativeState) (P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page) (TB : Nat → Prop)
    (Rn : BitVec 5) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (t : NativeState) : NativeState :=
  if Pre s0 P4 P2 TB Rn imm7 t then resSt t ((decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2 : SailM Unit) t) else t

theorem eval_pre {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    {t : NativeState} (hp : Pre s0 P4 P2 TB Rn imm7 t) :
    stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t = resSt t ((decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2 : SailM Unit) t) ∧
    ∃ u, (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2 : SailM Unit) t = .ok () u ∧ u.regs = t.regs ∧ u.mem = stpnMem (MemM1.ConsumerB.kmapB P4 P2) t Rn Rt Rt2 imm7 := by
  obtain ⟨hT, -, hD⟩ := MemM1.MemInv.memInv_agrees s0 P4 P2 TB t hp.inv
  obtain ⟨u, hu, hr, hm, -⟩ := decode_stpn_eval (MemM1.ConsumerB.kmapB P4 P2) _ t imm7 Rn Rt Rt2 hRn hRt hRt2 hT hD hp.be
    hp.f7 hp.f3 hp.al hp.perm hp.io
  exact ⟨by unfold stpnR; rw [if_pos hp], u, hu, hr, hm⟩

theorem act_ok {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    {s t : NativeState} (hPre : Pre s0 P4 P2 TB Rn imm7 s) (hc : CongIn s t) :
    (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2 : SailM Unit) t = .ok () (stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t) := by
  obtain ⟨hR, u, hu, -⟩ := eval_pre (Rt := Rt) (Rt2 := Rt2) hRn hRt hRt2 (pre_congr hc hPre)
  rw [hR, hu]
  rfl

theorem act_frame {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (t : NativeState) : ActFrame t (stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t) := by
  by_cases hp : Pre s0 P4 P2 TB Rn imm7 t
  · obtain ⟨hR, u, hu, hr, -⟩ := eval_pre (Rt := Rt) (Rt2 := Rt2) hRn hRt hRt2 hp
    rw [hR, hu]
    show ActFrame t u
    constructor <;> (rw [hr]; try rfl)
  · have hR : stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t = t := by unfold stpnR; rw [if_neg hp]
    rw [hR]
    constructor <;> rfl

theorem act_cong {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (t1 t2 : NativeState) (hc : CongIn t1 t2) :
    CongOut (stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t1) (stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t2) := by
  by_cases hp1 : Pre s0 P4 P2 TB Rn imm7 t1
  · have hp2 := pre_congr hc hp1
    obtain ⟨hR1, u1, hu1, hr1, hm1⟩ := eval_pre (Rt := Rt) (Rt2 := Rt2) hRn hRt hRt2 hp1
    obtain ⟨hR2, u2, hu2, hr2, hm2⟩ := eval_pre (Rt := Rt) (Rt2 := Rt2) hRn hRt hRt2 hp2
    rw [hR1, hR2, hu1, hu2]
    show CongOut u1 u2
    refine ⟨by rw [hm1, hm2]; simp only [stpnMem, stpData, hc.mem, hc.gpr], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hr1, hr2]; exact hc.gpr
    · rw [hr1, hr2]; exact hc.sp
    · rw [hr1, hr2]; exact hc.z
    · rw [hr1, hr2]; exact congrArg ProcState.N hc.ps
    · rw [hr1, hr2]; exact congrArg ProcState.Z hc.ps
    · rw [hr1, hr2]; exact congrArg ProcState.C hc.ps
    · rw [hr1, hr2]; exact congrArg ProcState.V hc.ps
  · have hp2 : ¬ Pre s0 P4 P2 TB Rn imm7 t2 := fun h => hp1 (pre_congr (congIn_symm hc) h)
    have hR1 : stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t1 = t1 := by unfold stpnR; rw [if_neg hp1]
    have hR2 : stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t2 = t2 := by unfold stpnR; rw [if_neg hp2]
    rw [hR1, hR2]
    exact ⟨hc.mem, hc.gpr, hc.sp, hc.z, congrArg ProcState.N hc.ps, congrArg ProcState.Z hc.ps,
      congrArg ProcState.C hc.ps, congrArg ProcState.V hc.ps⟩

theorem act_npe {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (t : NativeState) : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs (stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t).regs := by
  by_cases hp : Pre s0 P4 P2 TB Rn imm7 t
  · obtain ⟨hR, u, hu, hr, -⟩ := eval_pre (Rt := Rt) (Rt2 := Rt2) hRn hRt hRt2 hp
    rw [hR, hu]
    show ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs
    unfold ArmCertCT.CT2.NonProjRegsEq
    rw [hr]
    try rfl
  · have hR : stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t = t := by unfold stpnR; rw [if_neg hp]
    rw [hR]
    exact ArmCertCT.CT2.NonProjRegsEq.refl _ _

theorem act_gic {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (t : NativeState) : (stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t).regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending := by
  by_cases hp : Pre s0 P4 P2 TB Rn imm7 t
  · obtain ⟨hR, u, hu, hr, -⟩ := eval_pre (Rt := Rt) (Rt2 := Rt2) hRn hRt hRt2 hp
    rw [hR, hu]
    show u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending
    rw [hr]
    try rfl
  · have hR : stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t = t := by unfold stpnR; rw [if_neg hp]
    rw [hR]

theorem act_um {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (t : NativeState) : ArmBridge.BoundaryV2.UnmappedSame (MemM1.ConsumerB.kmapB P4 P2) t (stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t) := by
  by_cases hp : Pre s0 P4 P2 TB Rn imm7 t
  · obtain ⟨hR, u, hu, hr, hm⟩ := eval_pre (Rt := Rt) (Rt2 := Rt2) hRn hRt hRt2 hp
    rw [hR, hu]
    show ArmBridge.BoundaryV2.UnmappedSame (MemM1.ConsumerB.kmapB P4 P2) t u
    obtain ⟨-, hM, -⟩ := MemM1.MemInv.memInv_agrees s0 P4 P2 TB t hp.inv
    intro q hq _
    rw [hm]
    simp only [ArmCertMem.StpnEval.stpnMem]
    exact ArmCertMem.NbCommon.um_wfold hM _ _ 16 (hp.perm ArmCertMem.UoffCommon.accU ArmCertMem.UoffCommon.accU_acc0) _ _ q hq
  · have hR : stpnR s0 P4 P2 TB Rn imm7 Rt Rt2 t = t := by unfold stpnR; rw [if_neg hp]
    rw [hR]
    exact ArmBridge.BoundaryV2.UnmappedSame.refl _ _

theorem eret_stpn (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5) :
    (Sail.BitVec.extractLsb (ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 12 == 879088#20) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg (fun v => BitVec.getLsbD v 18) h
  unfold ldstPairOffWord at this
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
  simp only [BitVec.getLsbD_append] at this
  simp at this

end ArmCertMem.CruxStpn

