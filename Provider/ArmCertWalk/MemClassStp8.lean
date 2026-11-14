-- /: MemClass.Stp8.run — ACTUAL STP (64-bit pair, signed offset, base
-- Rn < 31) decode at arbitrary `a` and ANY 8-aligned VA (16-aligned: one LSE2 16-byte store; else two
-- 8-byte halves, the second translated on the post-first-write state), from the canonical invariant +
-- decision-171 no-update route. Mirrors SDK CruxMem.Stp8Eval.decode_stp8_eval with its AgreesV3 store
-- (stpV5_8 + AgreesAfter premise) replaced by storePair_noupdate (no premise).
import ArmCertWalk.MemPair
import CruxMem.Stp8Eval
import CruxMem.CruxStpn
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemClass.Stp8
open ArmCertWalk ArmBridge.Draft

abbrev pairAddr (a : NativeState) (Rn : BitVec 5) (imm7 : BitVec 7) : BitVec 64 :=
  a.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc →
      PairAccess spec config rows mapping (pairAddr a Rn imm7) acc a)
    (preW : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc → MemM1.MemWriteD6.PreW acc a.regs)
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
    (outside1 : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa1.toNat + i))
    (raw : RawImageAt spec.imageRows a.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u, (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2 : SailM Unit) a = .ok () u ∧
      u.regs = a.regs ∧
      u.mem = MemM1.MemWriteD1.wfold (MemM1.MemWriteD1.wfold a.mem pa1.toNat 8
          (fun j => (ArmCertMem.StpEval.stpData a Rt Rt2).extractLsb' (8 * j) 8))
        pa2.toNat 8 (fun j => (ArmCertMem.StpEval.stpData a Rt Rt2).extractLsb' (8 * (j + 8)) 8) ∧
      PairEvents spec (pairAddr a Rn imm7) pa1 pa2
        (.memWrite pa1.toNat 16 (some (pairAddr a Rn imm7).toNat) MemM1.MemWriteD4.akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) (ArmCertMem.StpEval.stpData a Rt Rt2))) none)
        (.memWrite pa1.toNat 8 (some (pairAddr a Rn imm7).toNat) MemM1.MemWriteD4.akPlain
          (some ((ArmCertMem.StpEval.stpData a Rt Rt2).extractLsb' 0 64)) none)
        (.memWrite pa2.toNat 8 (some (plus8 (pairAddr a Rn imm7)).toNat) MemM1.MemWriteD4.akPlain
          (some ((ArmCertMem.StpEval.stpData a Rt Rt2).extractLsb' 64 64)) none)
        a.events u.events := by
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
  have hEL := post.post.el0
  have hNoRME := post.post.noRME
  have hA64 := post.post.nrw
  have hNS := post.post.ns
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
  have hX1r : X1.regs = a.regs := by subst hX1; rfl
  have hX1m : X1.mem = a.mem := by subst hX1; rfl
  have hX1e : X1.events = a.events := by subst hX1; rfl
  have htr' : t'.regs = a.regs := htr.trans hX1r
  have htm' : t'.mem = a.mem := htm.trans hX1m
  have hR31n : ¬ Rn.toNat = 31 := by omega
  have htnn : Sail.Int.toNatChecked ((Rn.toNat : Nat) : Int) = Rn.toNat := rfl
  simp only [hR31n, htnn, ite_false, Bool.false_eq_true]
  simp only [CryptoMem.MemCore.xread64 t' Rn hRn]
  have hl2 : t'.regs.FeatureImpl[111] = true := by rw [htr']; exact lse2
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
  have hu4r : u4.regs = a.regs := by rw [← hu4]; exact htr'
  have hu4m : u4.mem = a.mem := by rw [← hu4]; exact htm'
  have hu4e : u4.events = t'.events := by rw [← hu4]
  have hE0E : Sail.BitVec.extractLsb (u4.regs.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1 := by
    rw [hu4r]; exact post.post.e0e
  obtain ⟨t4, hbe, hf4⟩ := MemM1.MemReadDBE.be_false u4 (by rw [hu4r]; exact post.post.el0) (by rw [hu4r]; exact post.post.nrw)
    (by rw [hu4r]; exact post.post.noRME) (by rw [hu4r]; exact post.post.vhe) (by rw [hu4r]; exact post.post.aa64el0)
    (by rw [hu4r]; exact post.post.ns) (by rw [hu4r]; exact post.post.e2h) (by rw [hu4r]; exact post.post.tge) hE0E
  simp only [hbe, Bool.false_eq_true, ite_false]
  name_call_arg Mem_set__1 1 as dv
  name_call_arg Mem_set__1 5 as addr
  have haddrA : addr = (a.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) := by
    rw [← haddr, htr']
    first | rfl | (simp [Sail.BitVec.signExtend, sign_extend]) | (congr 1)
  rw [haddrA]
  have h4r : t4.regs = a.regs := hf4.1.trans hu4r
  have h4m : t4.mem = a.mem := hf4.2.1.trans hu4m
  have pairT : PairAccess spec config rows mapping (pairAddr a Rn imm7) acc t4 := by
    obtain ⟨p16, p8⟩ := perAcc acc hA0 hAW
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨m, d, x⟩ := p16 h
      exact ⟨m, d, x.of_regs h4r⟩
    · obtain ⟨⟨m1, d1, x1⟩, ⟨m2, d2, x2⟩⟩ := p8 h
      exact ⟨⟨m1, d1, x1.of_regs h4r⟩, ⟨m2, d2, x2.of_regs h4r⟩⟩
  obtain ⟨t5, hms, hr5, hm5, hev⟩ := storePair_noupdate spec config rows mapping t4 (pairAddr a Rn imm7) h8 acc hAW pairT
    (current_s1_frame current h4r h4m) (by rw [h4r]; exact mode) (by rw [h4r]; exact debug)
    (by rw [h4r]; exact post) (by rw [h4r]; exact preW acc hA0 hAW) (by rw [h4r]; exact lse2)
    (by rw [h4r]; exact dcache) pa1 pa2 mapped1 mapped2 contiguous mmio1 mmio2 outside1
    (by rw [h4m]; exact raw) (by rw [h4r]; exact noUpd acc hA0) dv
  simp only [hms]
  have hdat : dv = (BitVec.cast (by decide : 64 + 64 = 16 * 8) (BitVec.append (a.regs.gpr[(GPRSummary.key Rt2.toNat).val]) (a.regs.gpr[(GPRSummary.key Rt.toNat).val]))) := by
    rw [← hdv, htr']
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.castWidth, BitVec.toNat_append]
  rw [hdat] at hev
  have h5r : t5.regs = a.regs := hr5.trans h4r
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
  try simp only [rdB, rdBT, rdBr, rdPC, wrP, wrPC, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, Bool.cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  refine ⟨h5r, ?_, ?_⟩
  · rw [hm5, h4m, hdat]; rfl
  · have e : t4.events = a.events := by
      rw [hf4.2.2]
      first | (rw [hu4e, hte, hX1e]) | (rw [hu4e, h3e, hte, hX1e])
    rw [e] at hev
    exact hev
#print axioms run

/-- (1)-(5): canonical frames. -/
theorem frames (a u : NativeState) (hr : u.regs = a.regs) :
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

/-- certiffi (i)+(ii): the store writes exactly the two 8-byte windows, neither a table byte. -/
theorem footprint {domain : QueryDomain} (spec : TopologyImageSpec domain) (mem : Mem) (pa1 pa2 : BitVec 56)
    (g1 g2 : Nat → BitVec 8)
    (outside1 : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa1.toNat + i))
    (outside2 : ∀ i < 8, ¬ (rowsFootprint spec.imageRows).byte (pa2.toNat + i)) :
    WritesOnly (fun x => (pa1.toNat ≤ x ∧ x < pa1.toNat + 8) ∨ (pa2.toNat ≤ x ∧ x < pa2.toNat + 8))
      (fun x => mem[x]?) (fun x => (MemM1.MemWriteD1.wfold (MemM1.MemWriteD1.wfold mem pa1.toNat 8 g1) pa2.toNat 8 g2)[x]?) ∧
    Separated (rowsFootprint spec.imageRows).byte
      (fun x => (pa1.toNat ≤ x ∧ x < pa1.toNat + 8) ∨ (pa2.toNat ≤ x ∧ x < pa2.toNat + 8)) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have n1 : ¬ (pa1.toNat ≤ x ∧ x < pa1.toNat + 8) := fun h => hx (Or.inl h)
    have n2 : ¬ (pa2.toNat ≤ x ∧ x < pa2.toNat + 8) := fun h => hx (Or.inr h)
    simp only [MemM1.MemWriteD1.wfold_get, n1, n2, ↓reduceIte]
  · intro x table hx
    rcases hx with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · have := outside1 (x - pa1.toNat) (by omega)
      rw [show pa1.toNat + (x - pa1.toNat) = x by omega] at this
      exact this table
    · have := outside2 (x - pa2.toNat) (by omega)
      rw [show pa2.toNat + (x - pa2.toNat) = x by omega] at this
      exact this table

#print axioms footprint
end MemClass.Stp8
