-- /: MemClass.Ldp8.run — ACTUAL LDP (64-bit pair, signed offset, base
-- Rn < 31) decode at arbitrary `a` and ANY 8-aligned VA (16-aligned: one LSE2 access; else two
-- 8-byte halves), from the canonical invariant + decision-171 no-update route. Mirrors SDK
-- CruxMem.Ldp8Eval.decode_ldp8_eval with its AgreesV3 read (readV5_ldp8, 8-not-16 only) replaced by
-- loadPair_noupdate (both cases, no premise). Registers = SDK `ldpPost`.
import ArmCertWalk.MemPair
import CruxMem.Ldp8Eval
import CruxMem.CruxLdp8
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemClass.Ldp8
open ArmCertWalk ArmBridge.Draft

abbrev pairAddr (a : NativeState) (Rn : BitVec 5) (imm7 : BitVec 7) : BitVec 64 :=
  a.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemReadD2.AccDR2 acc →
      PairAccess spec config rows mapping (pairAddr a Rn imm7) acc a)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (post : MemM1.MemReadD2.PostRegs2 a.regs)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (lse2 : a.regs.FeatureImpl[111] = true)
    (dcache : currentDCache a.regs = true)
    (h8 : (pairAddr a Rn imm7).toNat % 8 = 0)
    (pa1 pa2 : BitVec 56) (mapped1 : mapping (pairAddr a Rn imm7) = some pa1.toNat)
    (mapped2 : mapping (plus8 (pairAddr a Rn imm7)) = some pa2.toNat)
    (contiguous : (pairAddr a Rn imm7).toNat % 16 = 0 → pa2.toNat = pa1.toNat + 8)
    (mmio1 : MemM1.MemReadIF.NotMMIO pa1) (mmio2 : MemM1.MemReadIF.NotMMIO pa2)
    (data : BitVec 128)
    (bytes1 : ∀ i < 8, a.mem[pa1.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8))
    (bytes2 : ∀ i < 8, a.mem[pa2.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * (i + 8)) 8))
    (raw : RawImageAt spec.imageRows a.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u, (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2 : SailM Unit) a = .ok () u ∧
      u.regs = (ArmCertMem.LdpEval.ldpPost a Rt Rt2 data).regs ∧ u.mem = a.mem ∧
      PairEvents spec (pairAddr a Rn imm7) pa1 pa2
        (.memRead pa1.toNat 16 (some (pairAddr a Rn imm7).toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        (.memRead pa1.toNat 8 (some (pairAddr a Rn imm7).toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        (.memRead pa2.toNat 8 (some (plus8 (pairAddr a Rn imm7)).toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        a.events u.events := by
  unfold decode_ldp_gen_aarch64_instrs_memory_pair_general_offset
  unfold execute_aarch64_instrs_memory_pair_general_post_idx
  have hRtt' : ¬ ((Rt.toNat : Int) = (Rt2.toNat : Int)) := by
    intro h; apply hRtt; apply BitVec.eq_of_toNat_eq; omega
  have hb1 : (((Rt.toNat : Int)) == ((Rt2.toNat : Int))) = false := by simpa using hRtt'
  simp (config := {decide := true}) only [undefined_MemOp, undefined_Constraint, PreSail.internal_pick_at,
    PreSail.chooseAt, PreSail.choose, PreSail.occLabel, PreSail.undefined_bool_at, PreSail.undefined_bitvector_at,
    undefined_bool, undefined_bitvector, modifyGet, hb1, Functor.map, EStateM.map, MonadStateOf.modifyGet,
    EStateM.modifyGet, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind, ite_true, ite_false, dite_true, dite_false,
    hRtt', Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and, beq_iff_eq, bne_iff_ne, ne_eq,
    reduceIte, reduceDIte, Bool.not_true, Bool.not_false, decide_true, decide_false, Bool.or_false, Bool.false_or]
  reduce_closed_nat
  try simp (config := {decide := true}) only [PreSail.assert, ite_true, ite_false, EStateM.pure, pure]
  have rdP : ∀ st : NativeState, (readReg PSTATE : SailM ProcState) st = .ok st.regs.PSTATE st :=
    fun _ => rfl
  have hEL := post.post.el0
  have hNoRME := post.post.noRME
  have hA64 := post.post.nrw
  have hNS := post.post.ns
  simp (config := {decide := true}) only [rdP, hEL]
  name_call_state CreateAccDescGPR as X1
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr⟩ := MemM1.AccGPR.create X1 ArmFull.MemOp.MemOp_LOAD false true
    (by subst hX1; exact hNoRME) (by subst hX1; exact hA64) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact hNS) (by subst hX1; exact hTME)
  have htc' : ((((Rn.toNat : Nat) : Int)) != 31) = true := by
    rw [bne_iff_ne, ne_eq]; omega
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_LOAD false (0#2 != EL0)
      ((((Rn.toNat : Nat) : Int)) != 31) X1 = .ok acc t' := by
    rw [show (0#2 != EL0) = false from rfl, htc']
    exact hcr
  simp only [hcr2]
  have hfr' := hfr
  simp only [S1Normality.Frame] at hfr'
  obtain ⟨htr, htm, hte⟩ := hfr'
  have hX1r : X1.regs = a.regs := by subst hX1; rfl
  have hX1m : X1.mem = a.mem := by subst hX1; rfl
  have hX1e : X1.events = a.events := by subst hX1; rfl
  have htr' : t'.regs = a.regs := htr.trans hX1r
  have htm' : t'.mem = a.mem := htm.trans hX1m
  have hb31 : ((((Rn.toNat : Nat) : Int)) == 31) = false := by
    rw [beq_eq_false_iff_ne, ne_eq]; omega
  have htnn : Sail.Int.toNatChecked ((Rn.toNat : Nat) : Int) = Rn.toNat := rfl
  have hR31n : ¬ Rn.toNat = 31 := by omega
  simp only [hR31n, htnn, ite_false, Bool.false_eq_true]
  simp only [CryptoMem.MemCore.xread64 t' Rn hRn]
  have hl2 : t'.regs.FeatureImpl[111] = true := by rw [htr']; exact lse2
  simp only [MemM1.MemReadD2.lse2_on t' hl2]
  simp (config := {decide := true}) only [ite_true, ite_false, Bool.true_and, Bool.and_true, Bool.not_false,
    Bool.not_true, bne_iff_ne, ne_eq, decide_true, decide_false]
  reduce_closed_nat
  name_call_arg Mem_read__1 3 as addr
  have haddrA : addr = (a.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) := by
    rw [← haddr, htr']
    first | rfl | (simp [Sail.BitVec.signExtend, sign_extend]) | (congr 1)
  rw [haddrA]
  have pairT : PairAccess spec config rows mapping (pairAddr a Rn imm7) acc t' := by
    obtain ⟨p16, p8⟩ := perAcc acc hA0 hAD
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨m, d, x⟩ := p16 h
      exact ⟨m, d, x.of_regs htr'⟩
    · obtain ⟨⟨m1, d1, x1⟩, ⟨m2, d2, x2⟩⟩ := p8 h
      exact ⟨⟨m1, d1, x1.of_regs htr'⟩, ⟨m2, d2, x2.of_regs htr'⟩⟩
  obtain ⟨t4, hmr, hr4, hm4, hev⟩ := loadPair_noupdate spec config rows mapping t' (pairAddr a Rn imm7) h8 acc hAD pairT
    (current_s1_frame current htr' htm') (by rw [htr']; exact mode) (by rw [htr']; exact debug)
    (by rw [htr']; exact post) (by rw [htr']; exact lse2) (by rw [htr']; exact dcache) pa1 pa2 mapped1 mapped2
    contiguous mmio1 mmio2 (by rw [htm']; exact raw) (by rw [htr']; exact noUpd acc hA0) data
    (by intro i hi; rw [htm']; exact bytes1 i hi) (by intro i hi; rw [htm']; exact bytes2 i hi)
  simp only [EStateM.bind, EStateM.map, hmr]
  have hgpr : acc.acctype = .AccessType_GPR := hAW.base.gpr
  have h4r : t4.regs = a.regs := hr4.trans htr'
  have hE0E : Sail.BitVec.extractLsb (t4.regs.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1 := by
    rw [h4r]; exact post.post.e0e
  obtain ⟨t5, hbe, hf5⟩ := MemM1.MemReadDBE.be_false t4 (by rw [h4r]; exact post.post.el0) (by rw [h4r]; exact post.post.nrw)
    (by rw [h4r]; exact post.post.noRME) (by rw [h4r]; exact post.post.vhe) (by rw [h4r]; exact post.post.aa64el0)
    (by rw [h4r]; exact post.post.ns) (by rw [h4r]; exact post.post.e2h) (by rw [h4r]; exact post.post.tge) hE0E
  rw [hgpr]
  simp only [hbe]
  have h5r : t5.regs = a.regs := hf5.1.trans h4r
  simp only [Bool.false_eq_true, ite_false, EStateM.pure]
  have htn : Sail.Int.toNatChecked ((Rt.toNat : Nat) : Int) = Rt.toNat := rfl
  have htn2 : Sail.Int.toNatChecked ((Rt2.toNat : Nat) : Int) = Rt2.toNat := rfl
  simp only [htn, htn2]
  simp only [CryptoMem.MemCore.xset t5 Rt hRt 64 (Or.inr rfl), CryptoMem.MemCore.xset _ Rt2 hRt2 64 (Or.inr rfl)]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hspe : t5.regs.bank_Bool .SPESampleInFlight = false := by rw [h5r]; exact post.post.spe
  have rdBT : ∀ st : NativeState, (readReg BTypeNext : SailM (BitVec 2)) st = .ok st.regs.BTypeNext st := fun _ => rfl
  have rdBr : ∀ st : NativeState, (readReg __BranchTaken : SailM Bool) st = .ok st.regs.__BranchTaken st :=
    fun _ => rfl
  have rdPC : ∀ st : NativeState, (readReg _PC : SailM (BitVec 64)) st = .ok st.regs._PC st := fun _ => rfl
  have wrP : ∀ (st : NativeState) (v : ProcState), (writeReg PSTATE v : SailM Unit) st =
      .ok () { st with regs := { st.regs with PSTATE := v } } := fun _ _ => rfl
  have wrPC : ∀ (st : NativeState) (v : BitVec 64), (writeReg _PC v : SailM Unit) st =
      .ok () { st with regs := { st.regs with _PC := v } } := fun _ _ => rfl
  try simp only [rdB, rdBT, rdBr, rdPC, wrP, wrPC, CryptoMem.MemCore.setGpr, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, Bool.cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  have h5m : t5.mem = a.mem := hf5.2.1.trans (hm4.trans htm')
  refine ⟨?_, h5m, ?_⟩
  · simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr]
    rw [h5r]
    try rfl
  · rw [hf5.2.2]
    have e : t'.events = a.events := by rw [hte, hX1e]
    rw [← e]; exact hev

#print axioms run

/-- (1)-(5): canonical frames. -/
theorem frames (a u : NativeState) (Rt Rt2 : BitVec 5) (data : BitVec 128) (hr : u.regs = (ArmCertMem.LdpEval.ldpPost a Rt Rt2 data).regs) :
    ArmBridge.CruxGen.ActFrame a u ∧
    ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs u.regs ∧
    u.regs.bank_Option_InterruptID .__GIC_Pending = a.regs.bank_Option_InterruptID .__GIC_Pending ∧
    u.regs.PhysicalCount = a.regs.PhysicalCount ∧ u.regs.SP_EL0 = a.regs.SP_EL0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> (rw [hr]; try rfl)
  · unfold ArmCertCT.CT2.NonProjRegsEq
    rw [hr]
    try rfl
  · rw [hr]; try rfl
  · rw [hr]; try rfl
  · rw [hr]; try rfl

#print axioms frames
end MemClass.Ldp8
