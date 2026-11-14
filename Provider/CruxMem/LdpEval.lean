import CryptoMem.Ldp
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmCertMem.LdpEval
open ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2

/-! decode_ldp_eval: LDP (64-bit, signed offset, base SP, opc=10 L=1) decode leaf evaluated directly on `t`.
The inline unfolding is crypto's `CryptoMem.Ldp.ldp_bridge` (bridge-mem-v1), native part, `brReset s1` := `t`. -/

/-- The access address SP_EL0 + (SignExtend(imm7) << 3). -/
abbrev ldpAddr (t : NativeState) (imm7 : BitVec 7) : BitVec 64 := t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)

/-- Low / high doubleword of the loaded 16 bytes (LSE2 single access, little-endian). -/
def ldpLo (d : BitVec 128) : BitVec 64 :=
  Sail.BitVec.zeroExtend (BitVec.castWidth (BitVec.castWidth (Sail.BitVec.extractLsb (BitVec.castWidth d : BitVec 128) 63 0) : BitVec 64) : BitVec 64) 64
def ldpHi (d : BitVec 128) : BitVec 64 :=
  Sail.BitVec.zeroExtend (BitVec.castWidth (BitVec.castWidth (Sail.BitVec.extractLsb (BitVec.castWidth d : BitVec 128) 127 64) : BitVec 64) : BitVec 64) 64

/-- The register file after the leaf: X[Rt] := lo, X[Rt2] := hi; no writeback. -/
def ldpPost (t : NativeState) (Rt Rt2 : BitVec 5) (d : BitVec 128) : NativeState :=
  CryptoMem.MemCore.setGpr (CryptoMem.MemCore.setGpr t (GPRSummary.key Rt.toNat) (ldpLo d)) (GPRSummary.key Rt2.toNat) (ldpHi d)

set_option maxHeartbeats 8000000 in
theorem decode_ldp_eval (m : ConsumerMap) (walk : BitVec 64 → List Nat) (t : NativeState)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (hT : MemM1.MemDataV3.AgreesV3 m walk t)
    (hD : ArmCert.Premises.TranslationAgreesV3.DataPins t)
    (hB : MemM1.MemDataV3.BEPins t.regs)
    (hEL3A64 : t.regs.FeatureImpl[7] = true) (hNoEL3A32 : t.regs.FeatureImpl[3] = false)
    (hsp : t.regs.SP_EL0.toNat % 16 = 0)
    (hal : (t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)).toNat % 16 = 0)
    (hperm : ∀ acc, MemM1.Witness.Acc0 acc → m.permitted (t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)) acc true 16)
    (hio : MemM1.MemReadIF.NotMMIO (m.pa (t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3))))
    (data : BitVec 128) (hdata : ∀ i < 16, t.mem[(m.pa (t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3))).toNat + i]? =
        some (data.extractLsb' (8 * i) 8)) :
    ∃ u, (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2 : SailM Unit) t = .ok () u ∧
      u.regs = (ldpPost t Rt Rt2 data).regs ∧ u.mem = t.mem ∧
      ∃ ad ti W, u.events = t.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memRead (m.pa (t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3))).toNat 16
          (some (t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)).toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
        ArmCert.Premises.TranslationAgreesV3.TTWReadsOK walk (t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)) W := by
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
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr⟩ := MemM1.AccGPR.create X1 ArmFull.MemOp.MemOp_LOAD false false
    (by subst hX1; exact hNoRME) (by subst hX1; exact hA64) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact hNS) (by subst hX1; exact hTME)
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_LOAD false (0#2 != EL0)
      ((((31#5 : BitVec 5).toNat : Nat) : Int) != 31) X1 = .ok acc t' := by
    rw [show (0#2 != EL0) = false from rfl, show ((((31#5 : BitVec 5).toNat : Nat) : Int) != 31) = false from rfl]
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
  have hspt : t'.regs.SP_EL0.toNat % 16 = 0 := by rw [htr']; exact hsp
  obtain ⟨t3, hcs, hf3⟩ := CryptoMem.PairNative.cspa_ok t' hB'.el0 hB'.nrw hB'.noRME hB'.vhe hB'.aa64el0 hB'.ns
    hB'.e2h hB'.tge hspt
  simp only [hcs]
  obtain ⟨h3r, h3m, h3e⟩ := hf3
  have hEL3 : t3.regs.PSTATE.EL = 0#2 := by rw [h3r]; exact hB'.el0
  simp only [CryptoMem.PairNative.spread t3 hEL3]
  have hl2 : t3.regs.FeatureImpl[111] = true := by rw [h3r, htr']; exact hD.lse2
  simp only [MemM1.MemReadD2.lse2_on t3 hl2]
  simp (config := {decide := true}) only [ite_true, ite_false, Bool.true_and, Bool.and_true, Bool.not_false,
    Bool.not_true, bne_iff_ne, ne_eq, decide_true, decide_false]
  reduce_closed_nat
  name_call_arg Mem_read__1 3 as addr
  have h3r' : t3.regs = t.regs := h3r.trans htr'
  have h3m' : t3.mem = t.mem := h3m.trans htm'
  have haddrA : addr = (t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)) := by
    rw [← haddr, h3r']
    first | rfl | (simp [Sail.BitVec.signExtend, sign_extend]) | (congr 1)
  rw [haddrA]
  have hT3 : MemM1.MemDataV3.AgreesV3 m walk t3 := CryptoMem.MemCore.agrees_congr hT h3r' h3m'
  have hD3 : ArmCert.Premises.TranslationAgreesV3.DataPins t3 := CryptoMem.MemCore.dp_congr hD h3r'
  have hB3 : MemM1.MemDataV3.BEPins t3.regs := by
    rw [h3r']; exact hB
  have hmem : ∀ i < 16, t3.mem[(m.pa (t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3))).toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8) := by
    intro i hi; rw [h3m']; exact hdata i hi
  obtain ⟨ad, ti, W, t4, hmr, hev, hW, hr4, hm4⟩ := MemM1.MemDataV5.readV5_ldp m walk t3 hT3 hD3 hB3
    (t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)) hal acc hAD (hperm acc hA0) hio data hmem
  simp only [EStateM.bind, EStateM.map, hmr]
  have hgpr : acc.acctype = .AccessType_GPR := hAW.base.gpr
  have h4r : t4.regs = t.regs := hr4.trans h3r'
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
  have h5m : t5.mem = t.mem := hf5.2.1.trans (hm4.trans h3m')
  refine ⟨?_, h5m, ad, ti, W, ?_, hW⟩
  · simp only [ldpPost, CryptoMem.MemCore.setGpr]
    rw [h5r]
    try rfl
  · rw [hf5.2.2, hev, h3e, hte, hX1e]

#print axioms decode_ldp_eval
end ArmCertMem.LdpEval
