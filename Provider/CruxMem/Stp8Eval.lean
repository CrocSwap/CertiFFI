import CryptoMem.Stp8
import CruxMem.LdpEval
import CruxMem.StpEval
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmCertMem.Stp8Eval
open ArmBridge.Draft ArmCert.Premises.TranslationAgreesV1 ArmBridge.BoundaryV2

/-! decode_stp8_eval: STP (64-bit, signed offset, base Rn < 31) at an 8- but not 16-aligned VA: TWO single-copy 8-byte writes, each with its own translation (stpV5_8 shape); needs E17 v3 after the first write (hAA). crypto bridge-mem-v4 `CryptoMem.Stp8.stp8_bridge` native part, `brReset s1` := `t`. -/

/-- The memory after the leaf: bytes 0..7 of X[Rt2] ++ X[Rt] at m.pa a, then bytes 8..15 at m.pa (a + 8). -/
def stp8Mem (m : ConsumerMap) (t : NativeState) (Rn Rt Rt2 : BitVec 5) (imm7 : BitVec 7) : Std.ExtHashMap Nat (BitVec 8) :=
  MemM1.MemWriteD1.wfold (MemM1.MemWriteD1.wfold t.mem (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3))).toNat 8 (fun j => (ArmCertMem.StpEval.stpData t Rt Rt2).extractLsb' (8 * j) 8))
    (m.pa (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int))).toNat 8 (fun j => (ArmCertMem.StpEval.stpData t Rt Rt2).extractLsb' (8 * (j + 8)) 8)

set_option maxHeartbeats 8000000 in
theorem decode_stp8_eval (m : ConsumerMap) (walk : BitVec 64 → List Nat) (t : NativeState)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (hT : MemM1.MemDataV3.AgreesV3 m walk t)
    (hD : ArmCert.Premises.TranslationAgreesV3.DataPins t)
    (hB : MemM1.MemDataV3.BEPins t.regs)
    (hEL3A64 : t.regs.FeatureImpl[7] = true) (hNoEL3A32 : t.regs.FeatureImpl[3] = false)
    (h8 : (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)).toNat % 8 = 0) (h16 : (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)).toNat % 16 ≠ 0)
    (hperm1 : ∀ acc, MemM1.Witness.Acc0 acc → m.permitted (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) acc true ((8 : Nat) : Int))
    (hperm2 : ∀ acc, MemM1.Witness.Acc0 acc → m.permitted (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int)) acc true ((8 : Nat) : Int))
    (hio1 : MemM1.MemReadIF.NotMMIO (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)))) (hio2 : MemM1.MemReadIF.NotMMIO (m.pa (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int))))
    (hAA : ∀ g, MemM1.MemPair8V5.AgreesAfter m walk t (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3))) g) :
    ∃ u, (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2 : SailM Unit) t = .ok () u ∧
      u.regs = t.regs ∧ u.mem = stp8Mem m t Rn Rt Rt2 imm7 ∧
      ∃ ad1 ti1 W1 ad2 ti2 W2, u.events = t.events ++ #[Event.translationStart ti1] ++ W1 ++
        #[Event.translationEnd ad1,
          .memWrite (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3))).toNat 8 (some (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)).toNat) MemM1.MemWriteD4.akPlain (some ((ArmCertMem.StpEval.stpData t Rt Rt2).extractLsb' 0 64)) none,
          Event.translationStart ti2] ++ W2 ++
        #[Event.translationEnd ad2,
          .memWrite (m.pa (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int))).toNat 8 (some (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int)).toNat) MemM1.MemWriteD4.akPlain (some ((ArmCertMem.StpEval.stpData t Rt Rt2).extractLsb' 64 64)) none] ∧
        ArmCert.Premises.TranslationAgreesV3.TTWReadsOK walk (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) W1 ∧
        ArmCert.Premises.TranslationAgreesV3.TTWReadsOK walk (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int)) W2 := by
  unfold decode_stp_gen_aarch64_instrs_memory_pair_general_offset
  unfold execute_aarch64_instrs_memory_pair_general_post_idx
  have hml : (ArmFull.MemOp.MemOp_STORE == ArmFull.MemOp.MemOp_LOAD) = false := rfl
  simp (config := {decide := true}) only [undefined_MemOp, undefined_Constraint, PreSail.internal_pick_at,
    PreSail.chooseAt, PreSail.choose, PreSail.occLabel, PreSail.undefined_bool_at, PreSail.undefined_bitvector_at,
    undefined_bool, undefined_bitvector, modifyGet, hml, Functor.map, EStateM.map, MonadStateOf.modifyGet,
    EStateM.modifyGet, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind, ite_true, ite_false, dite_true, dite_false,
    Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and, beq_iff_eq, bne_iff_ne, ne_eq,
    reduceIte, reduceDIte, Bool.not_true, Bool.not_false, decide_true, decide_false, Bool.or_false, Bool.false_or]
  reduce_closed_nat2
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
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr⟩ := MemM1.AccGPR.create X1 ArmFull.MemOp.MemOp_STORE false true
    (by subst hX1; exact hNoRME) (by subst hX1; exact hA64) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact hNS) (by subst hX1; exact hTME)
  have htc' : ((((Rn.toNat : Nat) : Int)) != 31) = true := by
    rw [bne_iff_ne, ne_eq]; omega
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_STORE false (0#2 != EL0)
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
  have hR31n : ¬ Rn.toNat = 31 := by omega
  have htnn : Sail.Int.toNatChecked ((Rn.toNat : Nat) : Int) = Rn.toNat := rfl
  simp only [hR31n, htnn, ite_false, Bool.false_eq_true]
  simp only [CryptoMem.MemCore.xread64 t' Rn hRn]
  have hl2 : t'.regs.FeatureImpl[111] = true := by rw [htr']; exact hD.lse2
  have htn : Sail.Int.toNatChecked ((Rt.toNat : Nat) : Int) = Rt.toNat := rfl
  have htn2 : Sail.Int.toNatChecked ((Rt2.toNat : Nat) : Int) = Rt2.toNat := rfl
  simp only [htn, htn2, CryptoMem.MemCore.xread64 t' Rt hRt, CryptoMem.MemCore.xread64 t' Rt2 hRt2, Functor.map,
    EStateM.map, EStateM.bind]
  simp only [MemM1.MemReadD2.lse2_on t' hl2]
  simp (config := {decide := true}) only [ite_true, ite_false, Bool.true_and, Bool.and_true, Bool.not_false,
    Bool.not_true, bne_iff_ne, ne_eq, decide_true, decide_false]
  reduce_closed_nat2
  simp (config := {decide := true}) only [PreSail.internal_pick_at, PreSail.chooseAt, PreSail.choose,
    PreSail.occLabel, PreSail.undefined_bitvector_at, undefined_bitvector, modifyGet, Functor.map, EStateM.map,
    MonadStateOf.modifyGet, EStateM.modifyGet, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind,
    EStateM.bind]
  have hgpr : acc.acctype = .AccessType_GPR := hAW.base.gpr
  rw [hgpr]
  name_app_state BigEndian 2 as u4
  have hu4r : u4.regs = t.regs := by rw [← hu4]; exact htr'
  have hu4m : u4.mem = t.mem := by rw [← hu4]; exact htm'
  have hu4e : u4.events = t'.events := by rw [← hu4]
  have hE0E : Sail.BitVec.extractLsb (u4.regs.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1 := by
    rw [hu4r]; exact hD.e0e
  obtain ⟨t4, hbe, hf4⟩ := MemM1.MemReadDBE.be_false u4 (by rw [hu4r]; exact hB.el0) (by rw [hu4r]; exact hB.nrw)
    (by rw [hu4r]; exact hB.noRME) (by rw [hu4r]; exact hB.vhe) (by rw [hu4r]; exact hB.aa64el0)
    (by rw [hu4r]; exact hB.ns) (by rw [hu4r]; exact hB.e2h) (by rw [hu4r]; exact hB.tge) hE0E
  simp only [hbe, Bool.false_eq_true, ite_false]
  name_call_arg Mem_set__1 1 as dv
  name_call_arg Mem_set__1 5 as addr
  have haddrA : addr = (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) := by
    rw [← haddr, htr']
    first | rfl | (simp [Sail.BitVec.signExtend, sign_extend]) | (congr 1)
  rw [haddrA]
  have h4r : t4.regs = t.regs := hf4.1.trans hu4r
  have h4m : t4.mem = t.mem := hf4.2.1.trans hu4m
  have hT4 : MemM1.MemDataV3.AgreesV3 m walk t4 := CryptoMem.MemCore.agrees_congr hT h4r h4m
  have hD4 : ArmCert.Premises.TranslationAgreesV3.DataPins t4 := CryptoMem.MemCore.dp_congr hD h4r
  have hB4 : MemM1.MemDataV3.BEPins t4.regs := by
    rw [h4r]; exact hB
  have hAA4 : MemM1.MemPair8V5.AgreesAfter m walk t4 (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3))) (fun j => dv.extractLsb' (8 * j) 8) := by
    intro s2 hr hm
    exact hAA _ s2 (hr.trans h4r) (by rw [hm, h4m]; try rfl)
  obtain ⟨ad1, ti1, W1, ad2, ti2, W2, t5, hms, hev, hW1, hW2, hr5, hm5⟩ := MemM1.MemPair8V5.stpV5_8 m walk t4 hT4 hD4 hB4
    (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) h8 h16 acc dv hAW (hperm1 acc hA0) (hperm2 acc hA0) hio1 hio2 hAA4
  simp only [hms]
  have hmp : ∀ q, t5.mem[q]? = if (m.pa (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int))).toNat ≤ q ∧ q < (m.pa (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int))).toNat + 8 then some (dv.extractLsb' (8 * (q - (m.pa (BitVec.addInt (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) ((8 : Nat) : Int))).toNat + 8)) 8)
      else if (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3))).toNat ≤ q ∧ q < (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3))).toNat + 8 then some (dv.extractLsb' (8 * (q - (m.pa (t.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3))).toNat)) 8) else t.mem[q]? := by
    intro q; rw [hm5, MemM1.MemWriteD1.wfold_get, MemM1.MemWriteD1.wfold_get, h4m]
  have hdat : dv = (BitVec.cast (by decide : 64 + 64 = 16 * 8) (BitVec.append (t.regs.gpr[(GPRSummary.key Rt2.toNat).val]) (t.regs.gpr[(GPRSummary.key Rt.toNat).val]))) := by
    rw [← hdv, htr']
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.castWidth, BitVec.toNat_append]
  rw [hdat] at hev hmp
  have h5r : t5.regs = t.regs := hr5.trans h4r
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
  try simp only [rdB, rdBT, rdBr, rdPC, wrP, wrPC, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, Bool.cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  refine ⟨h5r, ?_, ad1, ti1, W1, ad2, ti2, W2, ?_, hW1, hW2⟩
  · rw [hm5, h4m, hdat]; rfl
  · first | (rw [hev, hf4.2.2, hu4e, hte, hX1e]; rfl) | (rw [hev, hf4.2.2, hu4e, h3e, hte, hX1e]; rfl) | (rw [hev, hf4.2.2, hu4e, hte, hX1e]) | (rw [hev, hf4.2.2, hu4e, h3e, hte, hX1e])

#print axioms decode_stp8_eval
end ArmCertMem.Stp8Eval
