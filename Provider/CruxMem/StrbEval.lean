import CryptoMem.Strb
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmCertMem.StrbEval
open ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1

/-! decode_strb_eval: the STRB (immediate, post-index, size=00 opc=00) decode leaf evaluated directly on a
state `t`, under premises on `t` itself. The inline unfolding is crypto's `CryptoMem.Strb.strb_bridge`
(bridge-mem-v1), native part only, with `brReset s1` replaced by `t`. -/

/-- The register file after the leaf: only the writeback X[Rn] := X[Rn] + SignExtend(imm9). -/
def strbPost (t : NativeState) (Rn : BitVec 5) (imm9 : BitVec 9) : NativeState :=
  CryptoMem.MemCore.setGpr t (GPRSummary.key Rn.toNat)
    (Sail.BitVec.zeroExtend (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + sign_extend imm9 64) 64)

/-- The memory after the leaf: the byte setWidth 8 X[Rt] written at PA m.pa X[Rn]. -/
def strbMem (m : ConsumerMap) (t : NativeState) (Rn Rt : BitVec 5) : Std.ExtHashMap Nat (BitVec 8) :=
  MemM1.MemWriteD1.wfold t.mem (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val])).toNat 1
    (MemM1.MemWriteD4.wbyte (BitVec.setWidth (1 * 8) (t.regs.gpr[(GPRSummary.key Rt.toNat).val])))

set_option maxHeartbeats 4000000 in
theorem decode_strb_eval (m : ConsumerMap) (walk : BitVec 64 → List Nat) (t : NativeState)
    (imm9 : BitVec 9) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (hT : MemM1.MemDataV3.AgreesV3 m walk t)
    (hD : ArmCert.Premises.TranslationAgreesV3.DataPins t)
    (hB : MemM1.MemDataV3.BEPins t.regs)
    (hEL3A64 : t.regs.FeatureImpl[7] = true) (hNoEL3A32 : t.regs.FeatureImpl[3] = false)
    (hperm : ∀ acc, MemM1.Witness.Acc0 acc → m.permitted (t.regs.gpr[(GPRSummary.key Rn.toNat).val]) acc true 1)
    (hio : MemM1.MemReadIF.NotMMIO (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val]))) :
    ∃ u, (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 0#2 0#2 : SailM Unit) t = .ok () u ∧
      u.regs = (strbPost t Rn imm9).regs ∧ u.mem = strbMem m t Rn Rt ∧
      ∃ ad ti W, u.events = t.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memWrite (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val])).toNat 1
          (some (t.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat) MemM1.MemWriteD4.akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 1) (BitVec.setWidth (1 * 8) (t.regs.gpr[(GPRSummary.key Rt.toNat).val])))) none] ∧
        ArmCert.Premises.TranslationAgreesV3.TTWReadsOK walk (t.regs.gpr[(GPRSummary.key Rn.toNat).val]) W := by
  unfold decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  unfold execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have hRnt' : ¬ ((Rn.toNat : Int) = (Rt.toNat : Int)) := by
    intro h; apply hRnt; apply BitVec.eq_of_toNat_eq; omega
  have hRn' : ¬ ((Rn.toNat : Int) = 31) := by omega
  have hb1 : (((Rn.toNat : Int)) == ((Rt.toNat : Int))) = false := by simpa using hRnt'
  have hb2 : (((Rn.toNat : Int)) != 31) = true := by simpa using hRn'
  have htn : Sail.Int.toNatChecked ((Rn.toNat : Nat) : Int) = Rn.toNat := rfl
  have htt : Sail.Int.toNatChecked ((Rt.toNat : Nat) : Int) = Rt.toNat := rfl
  have hR31 : ¬ Rn.toNat = 31 := by omega
  simp (config := {decide := true}) only [undefined_MemOp, undefined_Constraint, PreSail.internal_pick_at,
    PreSail.chooseAt, PreSail.occLabel, PreSail.undefined_bool_at, PreSail.undefined_bitvector_at,
    undefined_bool, undefined_bitvector, modifyGet, hb1, hb2, htn, htt, hR31, Functor.map, EStateM.map, MonadStateOf.modifyGet, EStateM.modifyGet, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind, ite_true, ite_false, dite_true, dite_false,
    hRnt', hRn', Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and, beq_iff_eq, bne_iff_ne, ne_eq,
    reduceIte, reduceDIte, Bool.not_true, Bool.not_false, decide_true, decide_false]
  have rdP : ∀ st : NativeState, (readReg PSTATE : SailM ProcState) st = .ok st.regs.PSTATE st :=
    fun _ => rfl
  have hEL := hB.el0
  have hNoRME := hB.noRME
  have hA64 := hB.nrw
  have hNS := hB.ns
  have hTME : t.regs.FeatureImpl[227] = false := hD.tmeOff
  simp (config := {decide := true}) only [rdP, hEL]
  name_call_state CreateAccDescGPR as X1
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr⟩ := MemM1.AccGPR.create X1 ArmFull.MemOp.MemOp_STORE false true
    (by subst hX1; exact hNoRME) (by subst hX1; exact hA64) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact hNS) (by subst hX1; exact hTME)
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_STORE false (0#2 != EL0)
      (ArmFull.MemOp.MemOp_STORE != ArmFull.MemOp.MemOp_PREFETCH && (true || true)) X1 = .ok acc t' := by
    rw [show (0#2 != EL0) = false from rfl,
      show (ArmFull.MemOp.MemOp_STORE != ArmFull.MemOp.MemOp_PREFETCH && (true || true)) = true from rfl]
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
  simp only [CryptoMem.MemCore.xread64 t' Rn hRn]
  reduce_closed_nat
  simp only [CryptoMem.Strb.xread8 t' Rt hRt]
  name_call_arg Mem_set 1 as dv
  have haddr : t'.regs.gpr[(GPRSummary.key Rn.toNat).val] = t.regs.gpr[(GPRSummary.key Rn.toNat).val] := by
    rw [htr']
  have hdat : dv = (BitVec.setWidth (1 * 8) (t.regs.gpr[(GPRSummary.key Rt.toNat).val])) := by
    rw [← hdv, htr']
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb, BitVec.castWidth]
  have hT' : MemM1.MemDataV3.AgreesV3 m walk t' := CryptoMem.MemCore.agrees_congr hT htr' htm'
  have hD' : ArmCert.Premises.TranslationAgreesV3.DataPins t' := CryptoMem.MemCore.dp_congr hD htr'
  have hB' : MemM1.MemDataV3.BEPins t'.regs := by rw [htr']; exact hB
  obtain ⟨ad, ti, W, t2, hms, hev, hW, hr2, hm2, hmp⟩ := MemM1.MemDataV5.strbV5 m walk t' hT' hD' hB'
    (t'.regs.gpr[(GPRSummary.key Rn.toNat).val]) acc dv hAW (by rw [haddr]; exact hperm acc hA0)
    (by rw [haddr]; exact hio)
  simp only [hms]
  try simp only [PreSail.assert, ite_true, pure, EStateM.pure]
  simp only [CryptoMem.MemCore.xset _ Rn hRn 64 (Or.inr rfl)]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hspe : t2.regs.bank_Bool .SPESampleInFlight = false := by rw [hr2, htr']; exact hD.spe
  try simp only [rdB, CryptoMem.MemCore.setGpr, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, Bool.cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  have hr2' : t2.regs = t.regs := hr2.trans htr'
  have hte' : t'.events = t.events := hte.trans hX1e
  refine ⟨?_, ?_, ad, ti, W, ?_, haddr ▸ hW⟩
  · simp only [strbPost, CryptoMem.MemCore.setGpr, haddr]
    rw [hr2']
    try rfl
  · rw [hm2, htm', haddr, hdat]; rfl
  · rw [hev, hte', haddr, hdat]

#print axioms decode_strb_eval
end ArmCertMem.StrbEval
