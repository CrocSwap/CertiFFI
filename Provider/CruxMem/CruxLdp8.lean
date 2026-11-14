import CruxMem.LdpEval
import CruxMem.LdpnEval
import CruxMem.Ldp8Eval
import CruxMem.CruxLdpn
import CruxMem.LdrbPre
import CruxMem.DispLdpGen
import CryptoMem.Ldp8
import Bridge.CruxGen
import CruxMem.NbCommon
import MemM1.MemInv
import Pilot.LoopFrame
import Pilot.ExceptLoop
import Pilot.InvariantLoop
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.CruxGen ArmBridge.Boundary ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.CruxCore
open CryptoMem.LdstPair ArmCertMem.LdpEval ArmCertMem.Ldp8Eval
open ArmCertMem.CruxLdpn (pairAddr)
open ArmCertMem.LdrbPre (sysEq2_of_congIn congIn_symm)
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CruxMem.CruxLdp8LNSym.
namespace ArmCertMem.CruxLdp8

-- StepRuntime companions referenced by oleans (BK3/BKmin); loaded for a complete environment

/-! LDP (64-bit, signed offset, general base Rn < 31, 8- but not 16-aligned: two 8-byte accesses) memory-form modelStep crux: `crux_gen` with
`A := decode_ldp_gen_..._offset Rt Rn Rt2 imm7 1#1 2#2` and `R t := if Pre t then resSt t (A t) else t`. -/

/-- The two loaded 8-byte halves as one 128-bit value: bytes 0..7 at pa1, bytes 8..15 at pa2. -/
def Bytes8x2 (mem : Std.ExtHashMap Nat (BitVec 8)) (pa1 pa2 : Nat) (d : BitVec 128) : Prop :=
  (∀ i < 8, mem[pa1 + i]? = some (d.extractLsb' (8 * i) 8)) ∧ (∀ i < 8, mem[pa2 + i]? = some (d.extractLsb' (8 * (i + 8)) 8))

theorem bytes8x2_unique {mem : Std.ExtHashMap Nat (BitVec 8)} {pa1 pa2 : Nat} {d1 d2 : BitVec 128}
    (h1 : Bytes8x2 mem pa1 pa2 d1) (h2 : Bytes8x2 mem pa1 pa2 d2) : d1 = d2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have key : d1.extractLsb' (8 * (j / 8)) 8 = d2.extractLsb' (8 * (j / 8)) 8 := by
    by_cases hlt : j / 8 < 8
    · exact Option.some.inj ((h1.1 (j / 8) hlt).symm.trans (h2.1 (j / 8) hlt))
    · have hi : j / 8 - 8 < 8 := by omega
      have e : 8 * (j / 8 - 8 + 8) = 8 * (j / 8) := by omega
      have := Option.some.inj ((h1.2 (j / 8 - 8) hi).symm.trans (h2.2 (j / 8 - 8) hi))
      rwa [e] at this
  have e2 := congrArg (fun v => BitVec.getLsbD v (j % 8)) key
  have hm : j % 8 < 8 := Nat.mod_lt _ (by decide)
  have hj' : 8 * (j / 8) + j % 8 = j := Nat.div_add_mod j 8
  simp only [BitVec.getLsbD_extractLsb', hm, decide_true, Bool.true_and, hj'] at e2
  exact e2

/-- CongIn-invariant precondition: memory's run invariant, BEPins, FEAT_EL3 bits, address alignment,
    per-access facts at X[Rn] + (SignExtend(imm7) << 3) (permitted for both 8-byte halves, not MMIO, both 8-byte halves present). -/
structure Pre (s0 : NativeState) (P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page) (TB : Nat → Prop)
    (Rn : BitVec 5) (imm7 : BitVec 7) (t : NativeState) : Prop where
  inv : MemM1.MemInv.MemInv s0 P4 P2 TB t
  be : MemM1.MemDataV3.BEPins t.regs
  f7 : t.regs.FeatureImpl[7] = true
  f3 : t.regs.FeatureImpl[3] = false
  h8 : (pairAddr t Rn imm7).toNat % 8 = 0
  h16 : (pairAddr t Rn imm7).toNat % 16 ≠ 0
  perm1 : ∀ acc, MemM1.Witness.Acc0 acc → (MemM1.ConsumerB.kmapB P4 P2).permitted (pairAddr t Rn imm7) acc true ((8 : Nat) : Int)
  perm2 : ∀ acc, MemM1.Witness.Acc0 acc → (MemM1.ConsumerB.kmapB P4 P2).permitted (BitVec.addInt (pairAddr t Rn imm7) ((8 : Nat) : Int)) acc true ((8 : Nat) : Int)
  io1 : MemM1.MemReadIF.NotMMIO ((MemM1.ConsumerB.kmapB P4 P2).pa (pairAddr t Rn imm7))
  io2 : MemM1.MemReadIF.NotMMIO ((MemM1.ConsumerB.kmapB P4 P2).pa (BitVec.addInt (pairAddr t Rn imm7) ((8 : Nat) : Int)))
  bytes : ∃ d : BitVec 128, Bytes8x2 t.mem ((MemM1.ConsumerB.kmapB P4 P2).pa (pairAddr t Rn imm7)).toNat ((MemM1.ConsumerB.kmapB P4 P2).pa (BitVec.addInt (pairAddr t Rn imm7) ((8 : Nat) : Int))).toNat d

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
    by rw [hf]; exact h.f7, by rw [hf]; exact h.f3, by rw [ha]; exact h.h8, by rw [ha]; exact h.h16, by rw [ha]; exact h.perm1, by rw [ha]; exact h.perm2,
    by rw [ha]; exact h.io1, by rw [ha]; exact h.io2, by rw [ha, ← hc.mem]; exact h.bytes⟩

open Classical in
/-- The action result map: the leaf result on `Pre` states, identity elsewhere. -/
noncomputable def ldp8R (s0 : NativeState) (P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page) (TB : Nat → Prop)
    (Rn : BitVec 5) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (t : NativeState) : NativeState :=
  if Pre s0 P4 P2 TB Rn imm7 t then resSt t ((decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2 : SailM Unit) t) else t

theorem eval_pre {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    {t : NativeState} (hp : Pre s0 P4 P2 TB Rn imm7 t) (d : BitVec 128)
    (hd : Bytes8x2 t.mem ((MemM1.ConsumerB.kmapB P4 P2).pa (pairAddr t Rn imm7)).toNat ((MemM1.ConsumerB.kmapB P4 P2).pa (BitVec.addInt (pairAddr t Rn imm7) ((8 : Nat) : Int))).toNat d) :
    ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t = resSt t ((decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2 : SailM Unit) t) ∧
    ∃ u, (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2 : SailM Unit) t = .ok () u ∧ u.regs = (ldpPost t Rt Rt2 d).regs ∧ u.mem = t.mem := by
  obtain ⟨hT, -, hD⟩ := MemM1.MemInv.memInv_agrees s0 P4 P2 TB t hp.inv
  obtain ⟨u, hu, hr, hm, -⟩ := decode_ldp8_eval (MemM1.ConsumerB.kmapB P4 P2) _ t imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt hT hD hp.be
    hp.f7 hp.f3 hp.h8 hp.h16 hp.perm1 hp.perm2 hp.io1 hp.io2 d hd.1 hd.2
  exact ⟨by unfold ldp8R; rw [if_pos hp], u, hu, hr, hm⟩

theorem act_ok {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    {s t : NativeState} (hPre : Pre s0 P4 P2 TB Rn imm7 s) (hc : CongIn s t) :
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2 : SailM Unit) t = .ok () (ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t) := by
  have hp := pre_congr hc hPre
  obtain ⟨d, hd⟩ := hp.bytes
  obtain ⟨hR, u, hu, -⟩ := eval_pre hRn hRt hRt2 hRtt hp d hd
  rw [hR, hu]
  rfl

theorem act_frame {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (t : NativeState) : ActFrame t (ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t) := by
  by_cases hp : Pre s0 P4 P2 TB Rn imm7 t
  · obtain ⟨d, hd⟩ := hp.bytes
    obtain ⟨hR, u, hu, hr, -⟩ := eval_pre hRn hRt hRt2 hRtt hp d hd
    rw [hR, hu]
    show ActFrame t u
    constructor <;> (rw [hr]; try rfl)
  · have hR : ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t = t := by unfold ldp8R; rw [if_neg hp]
    rw [hR]
    constructor <;> rfl

theorem act_cong {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (t1 t2 : NativeState) (hc : CongIn t1 t2) :
    CongOut (ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t1) (ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t2) := by
  by_cases hp1 : Pre s0 P4 P2 TB Rn imm7 t1
  · have hp2 := pre_congr hc hp1
    obtain ⟨d, hd⟩ := hp1.bytes
    have ha : pairAddr t2 Rn imm7 = pairAddr t1 Rn imm7 := by simp only [pairAddr, hc.gpr]
    have hd2 : Bytes8x2 t2.mem ((MemM1.ConsumerB.kmapB P4 P2).pa (pairAddr t2 Rn imm7)).toNat ((MemM1.ConsumerB.kmapB P4 P2).pa (BitVec.addInt (pairAddr t2 Rn imm7) ((8 : Nat) : Int))).toNat d := by
      rw [ha, ← hc.mem]; exact hd
    obtain ⟨hR1, u1, hu1, hr1, hm1⟩ := eval_pre hRn hRt hRt2 hRtt hp1 d hd
    obtain ⟨hR2, u2, hu2, hr2, hm2⟩ := eval_pre hRn hRt hRt2 hRtt hp2 d hd2
    rw [hR1, hR2, hu1, hu2]
    show CongOut u1 u2
    refine ⟨by rw [hm1, hm2, hc.mem], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hr1, hr2]; simp only [ldpPost, CryptoMem.MemCore.setGpr, hc.gpr]
    · rw [hr1, hr2]; exact hc.sp
    · rw [hr1, hr2]; exact hc.z
    · rw [hr1, hr2]; exact congrArg ProcState.N hc.ps
    · rw [hr1, hr2]; exact congrArg ProcState.Z hc.ps
    · rw [hr1, hr2]; exact congrArg ProcState.C hc.ps
    · rw [hr1, hr2]; exact congrArg ProcState.V hc.ps
  · have hp2 : ¬ Pre s0 P4 P2 TB Rn imm7 t2 := fun h => hp1 (pre_congr (congIn_symm hc) h)
    have hR1 : ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t1 = t1 := by unfold ldp8R; rw [if_neg hp1]
    have hR2 : ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t2 = t2 := by unfold ldp8R; rw [if_neg hp2]
    rw [hR1, hR2]
    exact ⟨hc.mem, hc.gpr, hc.sp, hc.z, congrArg ProcState.N hc.ps, congrArg ProcState.Z hc.ps,
      congrArg ProcState.C hc.ps, congrArg ProcState.V hc.ps⟩

theorem act_npe {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (t : NativeState) : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs (ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t).regs := by
  by_cases hp : Pre s0 P4 P2 TB Rn imm7 t
  · obtain ⟨d, hd⟩ := hp.bytes
    obtain ⟨hR, u, hu, hr, -⟩ := eval_pre hRn hRt hRt2 hRtt hp d hd
    rw [hR, hu]
    show ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap t.regs u.regs
    unfold ArmCertCT.CT2.NonProjRegsEq
    rw [hr]
    try rfl
  · have hR : ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t = t := by unfold ldp8R; rw [if_neg hp]
    rw [hR]
    exact ArmCertCT.CT2.NonProjRegsEq.refl _ _

theorem act_gic {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (t : NativeState) : (ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t).regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending := by
  by_cases hp : Pre s0 P4 P2 TB Rn imm7 t
  · obtain ⟨d, hd⟩ := hp.bytes
    obtain ⟨hR, u, hu, hr, -⟩ := eval_pre hRn hRt hRt2 hRtt hp d hd
    rw [hR, hu]
    show u.regs.bank_Option_InterruptID .__GIC_Pending = t.regs.bank_Option_InterruptID .__GIC_Pending
    rw [hr]
    try rfl
  · have hR : ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t = t := by unfold ldp8R; rw [if_neg hp]
    rw [hR]

theorem act_um {s0 : NativeState} {P4 P2 : BitVec 64 → Option MemM1.ConsumerV2.Page} {TB : Nat → Prop}
    {imm7 : BitVec 7} {Rn Rt Rt2 : BitVec 5} (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (t : NativeState) : ArmBridge.BoundaryV2.UnmappedSame (MemM1.ConsumerB.kmapB P4 P2) t (ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t) := by
  by_cases hp : Pre s0 P4 P2 TB Rn imm7 t
  · obtain ⟨d, hd⟩ := hp.bytes
    obtain ⟨hR, u, hu, hr, hm⟩ := eval_pre hRn hRt hRt2 hRtt hp d hd
    rw [hR, hu]
    show ArmBridge.BoundaryV2.UnmappedSame (MemM1.ConsumerB.kmapB P4 P2) t u
    intro q _ _
    rw [hm]
  · have hR : ldp8R s0 P4 P2 TB Rn imm7 Rt Rt2 t = t := by unfold ldp8R; rw [if_neg hp]
    rw [hR]
    exact ArmBridge.BoundaryV2.UnmappedSame.refl _ _

theorem eret_ldp8 (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5) :
    (Sail.BitVec.extractLsb (ldstPairOffWord 2#2 1#1 imm7 Rt2 Rn Rt) 31 12 == 879088#20) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg (fun v => BitVec.getLsbD v 18) h
  unfold ldstPairOffWord at this
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
  simp only [BitVec.getLsbD_append] at this
  simp at this

end ArmCertMem.CruxLdp8

