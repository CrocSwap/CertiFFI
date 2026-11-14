import CryptoMem.Ldp8
import CruxMem.LdpEval
import CruxMem.StpEval
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmCertMem.Ldp8Eval
open ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2

/-! decode_ldp8_eval: LDP (64-bit, signed offset, base Rn < 31) at an 8- but not 16-aligned VA: TWO single-copy 8-byte reads, each with its own translation (readV5_ldp8 shape); crypto bridge-mem-v4 `CryptoMem.Ldp8.ldp8_bridge` native part, `brReset s1` := `t`. -/

set_option maxHeartbeats 8000000 in
theorem decode_ldp8_eval (m : ConsumerMap) (walk : BitVec 64 → List Nat) (t : NativeState)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (hT : MemM1.MemDataV3.AgreesV3 m walk t)
    (hD : ArmCert.Premises.TranslationAgreesV3.DataPins t)
    (hB : MemM1.MemDataV3.BEPins t.regs)
    (hEL3A64 : t.regs.FeatureImpl[7] = true) (hNoEL3A32 : t.regs.FeatureImpl[3] = false)
    (h8 : (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)).toNat % 8 = 0) (h16 : (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)).toNat % 16 ≠ 0)
    (hperm1 : ∀ acc, MemM1.Witness.Acc0 acc → m.permitted (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) acc true ((8 : Nat) : Int))
    (hperm2 : ∀ acc, MemM1.Witness.Acc0 acc → m.permitted (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int)) acc true ((8 : Nat) : Int))
    (hio1 : MemM1.MemReadIF.NotMMIO (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)))) (hio2 : MemM1.MemReadIF.NotMMIO (m.pa (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int))))
    (data : BitVec 128)
    (hd1 : ∀ i < 8, t.mem[(m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3))).toNat + i]? = some (data.extractLsb' (8 * i) 8))
    (hd2 : ∀ i < 8, t.mem[(m.pa (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int))).toNat + i]? = some (data.extractLsb' (8 * (i + 8)) 8)) :
    ∃ u, (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2 : SailM Unit) t = .ok () u ∧
      u.regs = (ArmCertMem.LdpEval.ldpPost t Rt Rt2 data).regs ∧ u.mem = t.mem ∧
      ∃ ad1 ti1 W1 ad2 ti2 W2, u.events = t.events ++ #[Event.translationStart ti1] ++ W1 ++
        #[Event.translationEnd ad1, .memRead (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3))).toNat 8 (some (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)).toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false,
          Event.translationStart ti2] ++ W2 ++
        #[Event.translationEnd ad2, .memRead (m.pa (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int))).toNat 8 (some (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int)).toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
        ArmCert.Premises.TranslationAgreesV3.TTWReadsOK walk (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) W1 ∧
        ArmCert.Premises.TranslationAgreesV3.TTWReadsOK walk (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int)) W2 := by
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
  have hEL := hB.el0
  have hNoRME := hB.noRME
  have hA64 := hB.nrw
  have hNS := hB.ns
  have hTME : t.regs.FeatureImpl[227] = false := hD.tmeOff
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
  have hX1r : X1.regs = t.regs := by subst hX1; rfl
  have hX1m : X1.mem = t.mem := by subst hX1; rfl
  have hX1e : X1.events = t.events := by subst hX1; rfl
  have htr' : t'.regs = t.regs := htr.trans hX1r
  have htm' : t'.mem = t.mem := htm.trans hX1m
  have hB' : MemM1.MemDataV3.BEPins t'.regs := by
    rw [htr']; exact hB
  have hb31 : ((((Rn.toNat : Nat) : Int)) == 31) = false := by
    rw [beq_eq_false_iff_ne, ne_eq]; omega
  have htnn : Sail.Int.toNatChecked ((Rn.toNat : Nat) : Int) = Rn.toNat := rfl
  have hR31n : ¬ Rn.toNat = 31 := by omega
  simp only [hR31n, htnn, ite_false, Bool.false_eq_true]
  simp only [CryptoMem.MemCore.xread64 t' Rn hRn]
  have hl2 : t'.regs.FeatureImpl[111] = true := by rw [htr']; exact hD.lse2
  simp only [MemM1.MemReadD2.lse2_on t' hl2]
  simp (config := {decide := true}) only [ite_true, ite_false, Bool.true_and, Bool.and_true, Bool.not_false,
    Bool.not_true, bne_iff_ne, ne_eq, decide_true, decide_false]
  reduce_closed_nat
  name_call_arg Mem_read__1 3 as addr
  have haddrA : addr = (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) := by
    rw [← haddr, htr']
    first | rfl | (simp [Sail.BitVec.signExtend, sign_extend]) | (congr 1)
  rw [haddrA]
  have hT3 : MemM1.MemDataV3.AgreesV3 m walk t' := CryptoMem.MemCore.agrees_congr hT htr' htm'
  have hD3 : ArmCert.Premises.TranslationAgreesV3.DataPins t' := CryptoMem.MemCore.dp_congr hD htr'
  have hB3 : MemM1.MemDataV3.BEPins t'.regs := by
    rw [htr']; exact hB
  have hm1 : ∀ i < 8, t'.mem[(m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3))).toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8) := by
    intro i hi; rw [htm']; exact hd1 i hi
  have hm2 : ∀ i < 8, t'.mem[(m.pa (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int))).toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * (i + 8)) 8) := by
    intro i hi; rw [htm']; exact hd2 i hi
  obtain ⟨ad1, ti1, W1, ad2, ti2, W2, t4, hmr, hev, hW1, hW2, hr4, hm4⟩ := MemM1.MemPair8V5.readV5_ldp8 m walk t' hT3 hD3 hB3
    (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) h8 h16 acc hAD (hperm1 acc hA0) (hperm2 acc hA0) hio1 hio2 data hm1 hm2
  simp only [EStateM.bind, EStateM.map, hmr]
  have hgpr : acc.acctype = .AccessType_GPR := hAW.base.gpr
  have h4r : t4.regs = t.regs := hr4.trans htr'
  have hE0E : Sail.BitVec.extractLsb (t4.regs.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1 := by
    rw [h4r]; exact hD.e0e
  obtain ⟨t5, hbe, hf5⟩ := MemM1.MemReadDBE.be_false t4 (by rw [h4r]; exact hB.el0) (by rw [h4r]; exact hB.nrw)
    (by rw [h4r]; exact hB.noRME) (by rw [h4r]; exact hB.vhe) (by rw [h4r]; exact hB.aa64el0)
    (by rw [h4r]; exact hB.ns) (by rw [h4r]; exact hB.e2h) (by rw [h4r]; exact hB.tge) hE0E
  rw [hgpr]
  simp only [hbe]
  have h5r : t5.regs = t.regs := hf5.1.trans h4r
  simp only [Bool.false_eq_true, ite_false, EStateM.pure]
  have htn : Sail.Int.toNatChecked ((Rt.toNat : Nat) : Int) = Rt.toNat := rfl
  have htn2 : Sail.Int.toNatChecked ((Rt2.toNat : Nat) : Int) = Rt2.toNat := rfl
  simp only [htn, htn2]
  simp only [CryptoMem.MemCore.xset t5 Rt hRt 64 (Or.inr rfl), CryptoMem.MemCore.xset _ Rt2 hRt2 64 (Or.inr rfl)]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hspe : t5.regs.bank_Bool .SPESampleInFlight = false := by rw [h5r]; exact hD.spe
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
  have h5m : t5.mem = t.mem := hf5.2.1.trans (hm4.trans htm')
  refine ⟨?_, h5m, ?_⟩
  · simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr]
    rw [h5r]
    try rfl
  · exact ⟨ad1, ti1, W1, ad2, ti2, W2, by rw [hf5.2.2, hev, hte, hX1e], hW1, hW2⟩

#print axioms decode_ldp8_eval
end ArmCertMem.Ldp8Eval
