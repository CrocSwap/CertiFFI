-- Heap-v2 SP pair actions using the actual TCO preparation before translation.
import ArmCertWalk.MemClassLdp
import ArmCertWalk.MemClassStp
import HeapV2StepCerts.AccShape
import HeapDefaultTagCheck.PairRead
import HeapDefaultTagCheck.PairStore
import ArmCertWalk.MemClassLdp8
import ArmCertWalk.MemClassStp8
import DefaultStoreNoUpdate

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model NativeMteTagCheck NativeMteTagCheck.StatusTrace ReleaseProfile

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false

namespace MemClass.Ldp8
open ArmCertWalk ArmBridge.Draft

theorem runDefaultTagCheck {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      PairAccess spec config rows mapping (pairAddr a Rn imm7) acc a)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (post : MemM1.MemReadD.PostRegs a.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue a)
    (statusRows : TagStatusRows a (a.choiceOcc.getD 1354 0) 2)
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
    (noUpd : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u draws, (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2 : SailM Unit) a = .ok () u ∧
      u.regs = (ArmCertMem.LdpEval.ldpPost a Rt Rt2 data).regs ∧ u.mem = a.mem ∧
      PairEvents spec (pairAddr a Rn imm7) pa1 pa2
        (.memRead pa1.toNat 16 (some (pairAddr a Rn imm7).toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        (.memRead pa1.toNat 8 (some (pairAddr a Rn imm7).toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        (.memRead pa2.toNat 8 (some (plus8 (pairAddr a Rn imm7)).toNat) (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false)
        a.events u.events ∧ ChoiceDelta a u draws ∧ draws ≤ 2 := by
  rw [exists_comm]
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
  have hEL := post.el0
  have hNoRME := post.noRME
  have hA64 := post.nrw
  have hNS := post.ns
  simp (config := {decide := true}) only [rdP, hEL]
  name_call_state CreateAccDescGPR as X1
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr, hshape⟩ := HeapV2StepCerts.AccShape.create' X1 ArmFull.MemOp.MemOp_LOAD false true (Or.inl rfl)
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
  have dX1 : ChoiceDelta a X1 0 := by
    subst hX1
    exact ⟨rfl,by simp [Std.ExtHashMap.getD_insert]⟩
  have dCtor := DefaultDescriptorChoice.create_gpr_preserves .MemOp_LOAD false false true X1 acc t' hcr
  have dPrefix : ChoiceDelta a t' 0 := choice_delta_trans dX1 dCtor
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
  have perAccT : ∀ prepared, DataShape false prepared → PairAccess spec config rows mapping (pairAddr a Rn imm7) prepared t' := by
    intro prepared hp
    obtain ⟨p16,p8⟩ := perAcc prepared hp
    refine ⟨fun h => ?_,fun h => ?_⟩
    · obtain ⟨m,d,x⟩ := p16 h
      exact ⟨m,d,x.of_regs htr'⟩
    · obtain ⟨⟨m1,d1,x1⟩,⟨m2,d2,x2⟩⟩ := p8 h
      exact ⟨⟨m1,d1,x1.of_regs htr'⟩,⟨m2,d2,x2.of_regs htr'⟩⟩
  have rowsT : TagStatusRows t' (t'.choiceOcc.getD 1354 0) 2 := by
    unfold TagStatusRows at *
    rw [dPrefix.1,dPrefix.2,Nat.add_zero]
    exact statusRows
  obtain ⟨t4,draws,hmr,hr4,hm4,hev,d4,bound⟩ := HeapDefaultTagCheck.PairRead.loadPair_noupdate spec config rows mapping
    t' (pairAddr a Rn imm7) h8 acc hAD hshape perAccT
    (current_s1_frame current htr' htm') (by rw [htr']; exact mode) (by rw [htr']; exact debug)
    (by rw [htr']; exact post) catalogue (HeapDefaultTagCheck.Halves.default_of_regs controls htr') rowsT hshape.el
    (by rw [htr']; exact lse2) (by rw [htr']; exact dcache) pa1 pa2 mapped1 mapped2 contiguous mmio1 mmio2
    (by rw [htm']; exact raw) (by rw [htr']; exact noUpd) data
    (by intro i hi; rw [htm']; exact bytes1 i hi) (by intro i hi; rw [htm']; exact bytes2 i hi)
  simp only [EStateM.bind, EStateM.map, hmr]
  have hgpr : acc.acctype = .AccessType_GPR := hAW.base.gpr
  have h4r : t4.regs = a.regs := hr4.trans htr'
  have hE0E : Sail.BitVec.extractLsb (t4.regs.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1 := by
    rw [h4r]; exact post.e0e
  obtain ⟨t5, hbe, hf5⟩ := MemM1.MemReadDBE.be_false t4 (by rw [h4r]; exact post.el0) (by rw [h4r]; exact post.nrw)
    (by rw [h4r]; exact post.noRME) (by rw [h4r]; exact post.vhe) (by rw [h4r]; exact post.aa64el0)
    (by rw [h4r]; exact post.ns) (by rw [h4r]; exact post.e2h) (by rw [h4r]; exact post.tge) hE0E
  have dBE := TagCheckFrames.bigEndian_preserves .AccessType_GPR t4 false t5 hbe
  have dFinal : ChoiceDelta a t5 draws := by
    simpa only [Nat.zero_add,Nat.add_zero] using choice_delta_trans (choice_delta_trans dPrefix d4) dBE
  have bound2 : draws ≤ 2 := by split at bound <;> omega
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
  have hspe : t5.regs.bank_Bool .SPESampleInFlight = false := by rw [h5r]; exact post.spe
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
  refine ⟨draws,?_,h5m,?_,dFinal,bound2⟩
  · simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr]
    rw [h5r]
    try rfl
  · rw [hf5.2.2]
    have e : t'.events = a.events := by rw [hte, hX1e]
    rw [← e]; exact hev

#print axioms runDefaultTagCheck
end MemClass.Ldp8

namespace MemClass.Stp8
open ArmCertWalk ArmBridge.Draft

theorem runDefaultTagCheck {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      PairAccess spec config rows mapping (pairAddr a Rn imm7) acc a)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (post : MemM1.MemReadD.PostRegs a.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue a)
    (statusRows : TagStatusRows a (a.choiceOcc.getD 1354 0) 2)
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
    (noUpd : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u draws, (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2 : SailM Unit) a = .ok () u ∧
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
        a.events u.events ∧ ChoiceDelta a u draws ∧ draws ≤ 2 := by
  rw [exists_comm]
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
  have hEL := post.el0
  have hNoRME := post.noRME
  have hA64 := post.nrw
  have hNS := post.ns
  simp (config := {decide := true}) only [rdP, hEL]
  name_call_state CreateAccDescGPR as X1
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr, hshape⟩ := HeapV2StepCerts.AccShape.create' X1 ArmFull.MemOp.MemOp_STORE false true (Or.inr rfl)
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
  have dX1 : ChoiceDelta a X1 0 := by
    subst hX1
    exact ⟨rfl,by simp [Std.ExtHashMap.getD_insert]⟩
  have dCtor := DefaultDescriptorChoice.create_gpr_preserves .MemOp_STORE false false true X1 acc t' hcr
  have dPrefix : ChoiceDelta a t' 0 := choice_delta_trans dX1 dCtor
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
    rw [hu4r]; exact post.e0e
  obtain ⟨t4, hbe, hf4⟩ := MemM1.MemReadDBE.be_false u4 (by rw [hu4r]; exact post.el0) (by rw [hu4r]; exact post.nrw)
    (by rw [hu4r]; exact post.noRME) (by rw [hu4r]; exact post.vhe) (by rw [hu4r]; exact post.aa64el0)
    (by rw [hu4r]; exact post.ns) (by rw [hu4r]; exact post.e2h) (by rw [hu4r]; exact post.tge) hE0E
  simp only [hbe, Bool.false_eq_true, ite_false]
  name_call_arg Mem_set__1 1 as dv
  name_call_arg Mem_set__1 5 as addr
  have haddrA : addr = (a.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)) := by
    rw [← haddr, htr']
    first | rfl | (simp [Sail.BitVec.signExtend, sign_extend]) | (congr 1)
  rw [haddrA]
  have h4r : t4.regs = a.regs := hf4.1.trans hu4r
  have h4m : t4.mem = a.mem := hf4.2.1.trans hu4m
  have h4e : t4.events = a.events := by
    rw [hf4.2.2]
    first | rw [hu4e, hte, hX1e] | rw [hu4e, h3e, hte, hX1e]
  have du4 : ChoiceDelta t' u4 0 := by
    rw [← hu4]
    exact ⟨rfl,by simp [Std.ExtHashMap.getD_insert]⟩
  have dBE := TagCheckFrames.bigEndian_preserves .AccessType_GPR u4 false t4 hbe
  have d4 : ChoiceDelta a t4 0 := choice_delta_trans (choice_delta_trans dPrefix du4) dBE
  have rowsT : TagStatusRows t4 (t4.choiceOcc.getD 1354 0) 2 := by
    unfold TagStatusRows at *
    rw [d4.1,d4.2,Nat.add_zero]
    exact statusRows
  have perAccT : ∀ prepared, DataShape true prepared → PairAccess spec config rows mapping (pairAddr a Rn imm7) prepared t4 := by
    intro prepared hp
    obtain ⟨p16,p8⟩ := perAcc prepared hp
    refine ⟨fun h => ?_,fun h => ?_⟩
    · obtain ⟨m,d,x⟩ := p16 h
      exact ⟨m,d,x.of_regs h4r⟩
    · obtain ⟨⟨m1,d1,x1⟩,⟨m2,d2,x2⟩⟩ := p8 h
      exact ⟨⟨m1,d1,x1.of_regs h4r⟩,⟨m2,d2,x2.of_regs h4r⟩⟩
  obtain ⟨t5,draws,hms,hr5,hm5,hev,d5,bound⟩ := HeapDefaultTagCheck.PairStore.storePair_noupdate spec config rows mapping
    t4 (pairAddr a Rn imm7) h8 acc hAW hshape perAccT
    (current_s1_frame current h4r h4m) (by rw [h4r]; exact mode) (by rw [h4r]; exact debug)
    (by rw [h4r]; exact post) catalogue (HeapDefaultTagCheck.Halves.default_of_regs controls h4r) rowsT hshape.el
    (by rw [h4r]; exact lse2) (by rw [h4r]; exact dcache) pa1 pa2 mapped1 mapped2 contiguous mmio1 mmio2 outside1
    (by rw [h4m]; exact raw) (by rw [h4r]; exact noUpd) dv
  have dFinal : ChoiceDelta a t5 draws := by
    simpa only [Nat.zero_add] using choice_delta_trans d4 d5
  have bound2 : draws ≤ 2 := by split at bound <;> omega
  simp only [hms]
  have hdat : dv = (BitVec.cast (by decide : 64 + 64 = 16 * 8) (BitVec.append (a.regs.gpr[(GPRSummary.key Rt2.toNat).val]) (a.regs.gpr[(GPRSummary.key Rt.toNat).val]))) := by
    rw [← hdv, htr']
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.castWidth, BitVec.toNat_append]
  rw [hdat] at hev
  have h5r : t5.regs = a.regs := hr5.trans h4r
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hspe : t5.regs.bank_Bool .SPESampleInFlight = false := by rw [h5r]; exact post.spe
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
  refine ⟨draws,h5r,?_,?_,dFinal,bound2⟩
  · rw [hm5, h4m, hdat]; rfl
  · have e : t4.events = a.events := by
      rw [hf4.2.2]
      first | (rw [hu4e, hte, hX1e]) | (rw [hu4e, h3e, hte, hX1e])
    rw [e] at hev
    exact hev
#print axioms runDefaultTagCheck
end MemClass.Stp8
