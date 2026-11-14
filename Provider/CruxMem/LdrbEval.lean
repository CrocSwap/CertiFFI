import CryptoMem.Ldrb
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmCertMem.LdrbEval
open ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1

/-! decode_ldrb_eval: the LDRB (immediate, post-index, size=00 opc=01) decode leaf evaluated directly on a
state `t` (no brReset, no formStep), under premises on `t` itself. The inline unfolding is crypto's
`CryptoMem.Ldrb.ldrb_bridge` (bridge-mem-v1), native part only. -/

/-- The value written to X[Rt]: the loaded byte, zero-extended (via the 32-bit W-register write). -/
def ldrbVal (v : BitVec 8) : BitVec 64 :=
  Sail.BitVec.zeroExtend (BitVec.castWidth (Sail.BitVec.zeroExtend (BitVec.castWidth v : BitVec 8) 32) : BitVec 32) 64

/-- The register file after the leaf: X[Rt] := ldrbVal v, then X[Rn] := X[Rn] + SignExtend(imm9). -/
def ldrbPost (t : NativeState) (Rn Rt : BitVec 5) (imm9 : BitVec 9) (v : BitVec 8) : NativeState :=
  CryptoMem.MemCore.setGpr (CryptoMem.MemCore.setGpr t (GPRSummary.key Rt.toNat) (ldrbVal v)) (GPRSummary.key Rn.toNat)
    (Sail.BitVec.zeroExtend (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + sign_extend imm9 64) 64)

set_option maxHeartbeats 4000000 in
theorem decode_ldrb_eval (m : ConsumerMap) (walk : BitVec 64 → List Nat) (t : NativeState)
    (imm9 : BitVec 9) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (hT : MemM1.MemDataV3.AgreesV3 m walk t)
    (hD : ArmCert.Premises.TranslationAgreesV3.DataPins t)
    (hB : MemM1.MemDataV3.BEPins t.regs)
    (hEL3A64 : t.regs.FeatureImpl[7] = true) (hNoEL3A32 : t.regs.FeatureImpl[3] = false)
    (hperm : ∀ acc, MemM1.Witness.Acc0 acc → m.permitted (t.regs.gpr[(GPRSummary.key Rn.toNat).val]) acc true 1)
    (hio : MemM1.MemReadIF.NotMMIO (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val])))
    (v : BitVec 8) (hv : t.mem[(m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val])).toNat]? = some v) :
    ∃ u, (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2 : SailM Unit) t = .ok () u ∧
      u.regs = (ldrbPost t Rn Rt imm9 v).regs ∧ u.mem = t.mem ∧
      ∃ ad ti W, u.events = t.events ++ #[Event.translationStart ti] ++ W ++
        #[Event.translationEnd ad, .memRead (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val])).toNat 1
          (some (t.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false] ∧
        ArmCert.Premises.TranslationAgreesV3.TTWReadsOK walk (t.regs.gpr[(GPRSummary.key Rn.toNat).val]) W := by
  unfold decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
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
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr⟩ := MemM1.AccGPR.create X1 ArmFull.MemOp.MemOp_LOAD false true
    (by subst hX1; exact hNoRME) (by subst hX1; exact hA64) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact hNS) (by subst hX1; exact hTME)
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_LOAD false (0#2 != EL0)
      (ArmFull.MemOp.MemOp_LOAD != ArmFull.MemOp.MemOp_PREFETCH && (true || true)) X1 = .ok acc t' := by
    rw [show (0#2 != EL0) = false from rfl,
      show (ArmFull.MemOp.MemOp_LOAD != ArmFull.MemOp.MemOp_PREFETCH && (true || true)) = true from rfl]
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
  have haddr : t'.regs.gpr[(GPRSummary.key Rn.toNat).val] = t.regs.gpr[(GPRSummary.key Rn.toNat).val] := by
    rw [htr']
  have hmem : ∀ i < 1, t'.mem[(m.pa t'.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat + i]? =
      some ((v : BitVec (1 * 8)).extractLsb' (8 * i) 8) := by
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [htm', haddr]
    simpa using hv
  have hT' : MemM1.MemDataV3.AgreesV3 m walk t' := CryptoMem.MemCore.agrees_congr hT htr' htm'
  have hD' : ArmCert.Premises.TranslationAgreesV3.DataPins t' := CryptoMem.MemCore.dp_congr hD htr'
  have hB' : MemM1.MemDataV3.BEPins t'.regs := by rw [htr']; exact hB
  obtain ⟨ad, ti, W, t2, hmr, hev, hW, hr2, hm2⟩ := MemM1.MemDataV5.readV5_ldrb m walk t' hT' hD' hB'
    (t'.regs.gpr[(GPRSummary.key Rn.toNat).val]) acc hAD (by rw [haddr]; exact hperm acc hA0) (by rw [haddr]; exact hio)
    v hmem
  simp only [hmr]
  simp only [PreSail.assert, ite_true, pure, EStateM.pure]
  simp only [CryptoMem.MemCore.xset t2 Rt hRt 32 (Or.inl rfl), CryptoMem.MemCore.xset _ Rn hRn 64 (Or.inr rfl)]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hspe : t2.regs.bank_Bool .SPESampleInFlight = false := by rw [hr2, htr']; exact hD.spe
  try simp only [rdB, CryptoMem.MemCore.setGpr, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  have hr2' : t2.regs = t.regs := hr2.trans htr'
  have hm2' : t2.mem = t.mem := hm2.trans htm'
  have hte' : t'.events = t.events := hte.trans hX1e
  refine ⟨?_, hm2', ad, ti, W, ?_, haddr ▸ hW⟩
  · simp only [ldrbPost, CryptoMem.MemCore.setGpr, haddr]
    rw [hr2']
    rfl
  · rw [hev, hte', haddr]

#print axioms decode_ldrb_eval
end ArmCertMem.LdrbEval
