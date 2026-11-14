-- Heap-v2 SP pair actions using the actual TCO preparation before translation.
import ArmCertWalk.MemClassLdp
import ArmCertWalk.MemClassStp
import HeapV2StepCerts.AccShape
import HeapDefaultTagCheck.Access
import DefaultPairNoUpdate
import ArmCertWalk.MemClassLdp8
import ArmCertWalk.MemClassStp8
import DefaultStoreNoUpdate

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model NativeMteTagCheck NativeMteTagCheck.StatusTrace ReleaseProfile

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false

namespace MemClass.Ldp
open ArmCertWalk ArmBridge.Draft ArmCertMem.LdpEval

theorem runDefaultTagCheck {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (hRtt : Rt ≠ Rt2)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      domain (query a imm7 acc) ∧ ∃ data : S1AccessData spec config rows (query a imm7 acc),
        CurrentS1AccessAt spec config rows mapping (query a imm7 acc) data a)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (post : MemM1.MemReadD.PostRegs a.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue a)
    (statusRows : TagStatusRows a (a.choiceOcc.getD 1354 0) 1)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (lse2 : a.regs.FeatureImpl[111] = true)
    (dcache : currentDCache a.regs = true)
    (hsp : a.regs.SP_EL0.toNat % 16 = 0) (hal : (ldpAddr a imm7).toNat % 16 = 0)
    (pa : BitVec 56) (mapped : mapping (ldpAddr a imm7) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (data : BitVec 128) (bytes : ∀ i < 16, a.mem[pa.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8))
    (raw : RawImageAt spec.imageRows a.mem)
    (noUpd : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u draws, (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2 : SailM Unit) a = .ok () u ∧
      u.regs = (ldpPost a Rt Rt2 data).regs ∧ u.mem = a.mem ∧
      ChoiceDelta a u draws ∧ draws ≤ 1 ∧
      ∃ ad mid, NoUpdateTraffic spec (ldpAddr a imm7) a.events ad mid ∧
        u.events = mid.push (.memRead pa.toNat 16 (some (ldpAddr a imm7).toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) := by
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
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr, hshape⟩ := HeapV2StepCerts.AccShape.create' X1 ArmFull.MemOp.MemOp_LOAD false false (Or.inl rfl)
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
  have hX1r : X1.regs = a.regs := by subst hX1; rfl
  have hX1m : X1.mem = a.mem := by subst hX1; rfl
  have hX1e : X1.events = a.events := by subst hX1; rfl
  have htr' : t'.regs = a.regs := htr.trans hX1r
  have htm' : t'.mem = a.mem := htm.trans hX1m
  have dX1 : ChoiceDelta a X1 0 := by
    subst hX1
    exact ⟨rfl, by simp [Std.ExtHashMap.getD_insert]⟩
  have dCtor := DefaultDescriptorChoice.create_gpr_preserves .MemOp_LOAD false false false X1 acc t' hcr
  have dPrefix : ChoiceDelta a t' 0 := choice_delta_trans dX1 dCtor
  have hspt : t'.regs.SP_EL0.toNat % 16 = 0 := by rw [htr']; exact hsp
  obtain ⟨t3, hcs, hf3⟩ := CryptoMem.PairNative.cspa_ok t' (by rw [htr']; exact post.el0) (by rw [htr']; exact post.nrw) (by rw [htr']; exact post.noRME) (by rw [htr']; exact post.vhe) (by rw [htr']; exact post.aa64el0) (by rw [htr']; exact post.ns)
    (by rw [htr']; exact post.e2h) (by rw [htr']; exact post.tge) hspt
  simp only [hcs]
  have dSP := DefaultDescriptorChoice.sp_alignment_preserves t' () t3 hcs
  have d3 : ChoiceDelta a t3 0 := choice_delta_trans dPrefix dSP
  obtain ⟨h3r, h3m, h3e⟩ := hf3
  have hEL3 : t3.regs.PSTATE.EL = 0#2 := by rw [h3r, htr']; exact post.el0
  simp only [CryptoMem.PairNative.spread t3 hEL3]
  have hl2 : t3.regs.FeatureImpl[111] = true := by rw [h3r, htr']; exact lse2
  simp only [MemM1.MemReadD2.lse2_on t3 hl2]
  simp (config := {decide := true}) only [ite_true, ite_false, Bool.true_and, Bool.and_true, Bool.not_false,
    Bool.not_true, bne_iff_ne, ne_eq, decide_true, decide_false]
  reduce_closed_nat
  name_call_arg Mem_read__1 3 as addr
  have h3r' : t3.regs = a.regs := h3r.trans htr'
  have h3m' : t3.mem = a.mem := h3m.trans htm'
  have haddrA : addr = (a.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)) := by
    rw [← haddr, h3r']
    first | rfl | (simp [Sail.BitVec.signExtend, sign_extend]) | (congr 1)
  rw [haddrA]
  have allowed3 : TagStatusOK t3 := HeapDefaultTagCheck.Access.status_at statusRows d3 (by decide)
  obtain ⟨ad,mid,t4,draws,hmr,traffic,vaddr,hev,hr4,hm4,d4,bound⟩ :=
    DefaultPairNoUpdate.load16 spec config rows mapping t3 (ldpAddr a imm7) hal acc hAD hshape
      (fun prepared hp => by
        obtain ⟨m,d,x⟩ := perAcc prepared hp
        exact ⟨m,d,x.of_regs h3r'⟩)
      (current_s1_frame current h3r' h3m')
      (by rw [h3r']; exact mode) (by rw [h3r']; exact debug) (by rw [h3r']; exact post)
      catalogue (controls.transport ⟨h3r',h3m',h3e.trans (hte.trans hX1e)⟩) allowed3 hshape.el
      (by rw [h3r']; exact lse2) (by rw [h3r']; exact dcache) pa mapped mmio
      (by rw [h3m']; exact raw) (by rw [h3r']; exact noUpd)
      data (by intro i hi; rw [h3m']; exact bytes i hi)
  simp only [EStateM.bind, EStateM.map, hmr]
  have hgpr : acc.acctype = .AccessType_GPR := hAW.base.gpr
  have h4r : t4.regs = a.regs := hr4.trans h3r'
  have hE0E : Sail.BitVec.extractLsb (t4.regs.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1 := by
    rw [h4r]; exact post.e0e
  obtain ⟨t5, hbe, hf5⟩ := MemM1.MemReadDBE.be_false t4 (by rw [h4r]; exact post.el0) (by rw [h4r]; exact post.nrw)
    (by rw [h4r]; exact post.noRME) (by rw [h4r]; exact post.vhe) (by rw [h4r]; exact post.aa64el0)
    (by rw [h4r]; exact post.ns) (by rw [h4r]; exact post.e2h) (by rw [h4r]; exact post.tge) hE0E
  have dBE := TagCheckFrames.bigEndian_preserves .AccessType_GPR t4 false t5 hbe
  have dFinal : ChoiceDelta a t5 draws := by
    simpa only [Nat.zero_add,Nat.add_zero] using choice_delta_trans (choice_delta_trans d3 d4) dBE
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
  have h5m : t5.mem = a.mem := hf5.2.1.trans (hm4.trans h3m')
  have kind : AccessDescriptor_to_Access_kind acc = .AK_explicit { variety := .AV_plain, strength := .AS_normal } :=
    MemM1.MemReadD2.kind_eq2 acc hAD
  have hev0 : t3.events = a.events := by rw [h3e, hte, hX1e]
  refine ⟨draws, ?_, h5m, dFinal, bound, ad, mid, by rw [← hev0]; exact traffic, ?_⟩
  · simp only [ldpPost, CryptoMem.MemCore.setGpr]
    rw [h5r]
    try rfl
  · rw [hf5.2.2, hev, kind]

#print axioms runDefaultTagCheck
end MemClass.Ldp

namespace MemClass.Stp
open ArmCertWalk ArmBridge.Draft ArmCertMem.StpEval
open ArmCertMem.LdpEval (ldpAddr)

theorem runDefaultTagCheck {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      domain (query a imm7 acc) ∧ (∃ data : S1AccessData spec config rows (query a imm7 acc),
        CurrentS1AccessAt spec config rows mapping (query a imm7 acc) data a))
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (post : MemM1.MemReadD.PostRegs a.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue a)
    (statusRows : TagStatusRows a (a.choiceOcc.getD 1354 0) 1)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (lse2 : a.regs.FeatureImpl[111] = true)
    (dcache : currentDCache a.regs = true)
    (hsp : a.regs.SP_EL0.toNat % 16 = 0) (hal : (ldpAddr a imm7).toNat % 16 = 0)
    (pa : BitVec 56) (mapped : mapping (ldpAddr a imm7) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (raw : RawImageAt spec.imageRows a.mem)
    (noUpd : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u draws, (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 0#1 2#2 : SailM Unit) a = .ok () u ∧
      u.regs = a.regs ∧ u.mem = MemM1.MemWriteD1.wfold a.mem pa.toNat 16 (MemM1.MemWriteD4.wbyte (stpData a Rt Rt2)) ∧
      ChoiceDelta a u draws ∧ draws ≤ 1 ∧
      ∃ ad mid, NoUpdateTraffic spec (ldpAddr a imm7) a.events ad mid ∧
        u.events = mid.push (.memWrite pa.toNat 16 (some (ldpAddr a imm7).toNat) MemM1.MemWriteD4.akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) (stpData a Rt Rt2))) none) := by
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
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr, hshape⟩ := HeapV2StepCerts.AccShape.create' X1 ArmFull.MemOp.MemOp_STORE false false (Or.inr rfl)
    (by subst hX1; exact hNoRME) (by subst hX1; exact hA64) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact hNS) (by subst hX1; exact hTME)
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_STORE false (0#2 != EL0)
      ((((31#5 : BitVec 5).toNat : Nat) : Int) != 31) X1 = .ok acc t' := by
    rw [show (0#2 != EL0) = false from rfl, show ((((31#5 : BitVec 5).toNat : Nat) : Int) != 31) = false from rfl]
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
    exact ⟨rfl, by simp [Std.ExtHashMap.getD_insert]⟩
  have dCtor := DefaultDescriptorChoice.create_gpr_preserves .MemOp_STORE false false false X1 acc t' hcr
  have dPrefix : ChoiceDelta a t' 0 := choice_delta_trans dX1 dCtor
  have hspt : t'.regs.SP_EL0.toNat % 16 = 0 := by rw [htr']; exact hsp
  obtain ⟨t3, hcs, hf3⟩ := CryptoMem.PairNative.cspa_ok t' (by rw [htr']; exact post.el0) (by rw [htr']; exact post.nrw) (by rw [htr']; exact post.noRME) (by rw [htr']; exact post.vhe) (by rw [htr']; exact post.aa64el0) (by rw [htr']; exact post.ns)
    (by rw [htr']; exact post.e2h) (by rw [htr']; exact post.tge) hspt
  simp only [hcs]
  have dSP := DefaultDescriptorChoice.sp_alignment_preserves t' () t3 hcs
  have d3 : ChoiceDelta a t3 0 := choice_delta_trans dPrefix dSP
  obtain ⟨h3r, h3m, h3e⟩ := hf3
  have hEL3 : t3.regs.PSTATE.EL = 0#2 := by rw [h3r, htr']; exact post.el0
  simp only [CryptoMem.PairNative.spread t3 hEL3]
  have hl2 : t3.regs.FeatureImpl[111] = true := by rw [h3r, htr']; exact lse2
  have htn : Sail.Int.toNatChecked ((Rt.toNat : Nat) : Int) = Rt.toNat := rfl
  have htn2 : Sail.Int.toNatChecked ((Rt2.toNat : Nat) : Int) = Rt2.toNat := rfl
  simp only [htn, htn2, CryptoMem.MemCore.xread64 t3 Rt hRt, CryptoMem.MemCore.xread64 t3 Rt2 hRt2, Functor.map,
    EStateM.map, EStateM.bind]
  simp only [MemM1.MemReadD2.lse2_on t3 hl2]
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
  have h3r' : t3.regs = a.regs := h3r.trans htr'
  have h3m' : t3.mem = a.mem := h3m.trans htm'
  have hu4r : u4.regs = a.regs := by rw [← hu4]; exact h3r'
  have hu4m : u4.mem = a.mem := by rw [← hu4]; exact h3m'
  have hu4e : u4.events = t3.events := by rw [← hu4]
  have hE0E : Sail.BitVec.extractLsb (u4.regs.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1 := by
    rw [hu4r]; exact post.e0e
  obtain ⟨t4, hbe, hf4⟩ := MemM1.MemReadDBE.be_false u4 (by rw [hu4r]; exact post.el0) (by rw [hu4r]; exact post.nrw)
    (by rw [hu4r]; exact post.noRME) (by rw [hu4r]; exact post.vhe) (by rw [hu4r]; exact post.aa64el0)
    (by rw [hu4r]; exact post.ns) (by rw [hu4r]; exact post.e2h) (by rw [hu4r]; exact post.tge) hE0E
  simp only [hbe, Bool.false_eq_true, ite_false]
  name_call_arg Mem_set__1 1 as dv
  name_call_arg Mem_set__1 5 as addr
  have haddrA : addr = (a.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)) := by
    rw [← haddr, h3r']
    first | rfl | (simp [Sail.BitVec.signExtend, sign_extend]) | (congr 1)
  rw [haddrA]
  have h4r : t4.regs = a.regs := hf4.1.trans hu4r
  have h4m : t4.mem = a.mem := hf4.2.1.trans hu4m
  have h4e : t4.events = a.events := hf4.2.2.trans (hu4e.trans (h3e.trans (hte.trans hX1e)))
  have du4 : ChoiceDelta t3 u4 0 := by
    rw [← hu4]
    exact ⟨rfl, by simp [Std.ExtHashMap.getD_insert]⟩
  have dBE := TagCheckFrames.bigEndian_preserves .AccessType_GPR u4 false t4 hbe
  have d4 : ChoiceDelta a t4 0 := choice_delta_trans (choice_delta_trans d3 du4) dBE
  have allowed : TagStatusOK a := HeapDefaultTagCheck.Access.status_at statusRows (choice_delta_refl a) (by decide)
  obtain ⟨ad,mid,t5,draws,hms,traffic,_,hev,h5r,hm5,d5,bound⟩ :=
    DefaultStoreNoUpdate.pair spec config rows mapping a t4 ⟨h4r,h4m,h4e,d4⟩
      (ldpAddr a imm7) hal acc hAW hshape hshape.el catalogue controls allowed dv
      (by rw [h4r]; exact lse2) (fun prepared hp => perAcc prepared hp)
      current mode post debug dcache pa mapped raw noUpd mmio
  simp only [hms]
  have hdat : dv = (BitVec.cast (by decide : 64 + 64 = 16 * 8) (BitVec.append (a.regs.gpr[(GPRSummary.key Rt2.toNat).val]) (a.regs.gpr[(GPRSummary.key Rt.toNat).val]))) := by
    rw [← hdv, h3r']
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.castWidth, BitVec.toNat_append]
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
  refine ⟨draws,h5r,?_,d5,bound,ad,mid,traffic,?_⟩
  · rw [hm5, hdat]; rfl
  · rw [hev, hdat, MemM1.MemWriteD7.akT acc hAW]; rfl

#print axioms runDefaultTagCheck
end MemClass.Stp

