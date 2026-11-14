-- Memory (runtime14 memory classes): MemClass.StpPre.run — ACTUAL STP (64-bit pair, PRE-INDEX, base SP, SP := SP + off)
-- decode at arbitrary `a`: one LSE2 16-byte store (adapted from MemClass.Stp.run per CruxMem.StpPreEval), from the canonical invariant + decision-171
-- no-update route. Mirrors SDK CruxMem.StpEval.decode_stp_eval with its AgreesV3 store (stpV5)
-- replaced by MemWriteD7.stp_lse2_strong fed by translate_noupdate_at (no premise).
import ArmCertWalk.DataNoUpdate
import MemM1.MemWriteD7
import MemM1.MemReadDBE
import MemM1.AccGPR
import CryptoMem.MemCore
import CryptoMem.PairNative
import CryptoMem.Tac
import CryptoMem.Tac2
import ArmCertR14.SpSet
import ArmCertR14.Value
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemClass.StpPre
open ArmCertWalk ArmBridge.Draft

/-- The access address SP + (signExtend imm7 << 3) (pre-index: also the new SP). -/
abbrev ldpAddr (t : NativeState) (imm7 : BitVec 7) : BitVec 64 := t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)

/-- The stored 16 bytes: X[Rt2] ++ X[Rt] (X[Rt] at the low address). -/
def stpData (t : NativeState) (Rt Rt2 : BitVec 5) : BitVec (16 * 8) :=
  BitVec.cast (by decide : 64 + 64 = 16 * 8)
    (BitVec.append (t.regs.gpr[(GPRSummary.key Rt2.toNat).val]) (t.regs.gpr[(GPRSummary.key Rt.toNat).val]))

def query (a : NativeState) (imm7 : BitVec 7) (acc : AccessDescriptor) : AccessQuery :=
  ⟨ldpAddr a imm7, ⟨acc, true⟩, ((16 : Nat) : Int)⟩

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc →
      domain (query a imm7 acc) ∧ (∃ data : S1AccessData spec config rows (query a imm7 acc),
        CurrentS1AccessAt spec config rows mapping (query a imm7 acc) data a) ∧
      MemM1.MemWriteD6.PreW acc a.regs)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (post : MemM1.MemReadD2.PostRegs2 a.regs)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (lse2 : a.regs.FeatureImpl[111] = true)
    (dcache : currentDCache a.regs = true)
    (hsp : a.regs.SP_EL0.toNat % 16 = 0) (hal : (ldpAddr a imm7).toNat % 16 = 0)
    (pa : BitVec 56) (mapped : mapping (ldpAddr a imm7) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (raw : RawImageAt spec.imageRows a.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u, (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt 31#5 Rt2 imm7 0#1 2#2 : SailM Unit) a = .ok () u ∧
      u.regs = { a.regs with SP_EL0 := ldpAddr a imm7 } ∧ u.mem = MemM1.MemWriteD1.wfold a.mem pa.toNat 16 (MemM1.MemWriteD4.wbyte (stpData a Rt Rt2)) ∧
      ∃ ad mid, NoUpdateTraffic spec (ldpAddr a imm7) a.events ad mid ∧
        u.events = mid.push (.memWrite pa.toNat 16 (some (ldpAddr a imm7).toNat) MemM1.MemWriteD4.akPlain
          (some (Sail.BitVec.castWidth (m := 8 * 16) (stpData a Rt Rt2))) none) := by
  unfold decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx
  unfold execute_aarch64_instrs_memory_pair_general_post_idx
  have hml : (ArmFull.MemOp.MemOp_STORE == ArmFull.MemOp.MemOp_LOAD) = false := rfl
  have hn31 : ((((31#5 : BitVec 5).toNat : Nat) : Int) != 31) = false := rfl
  simp (config := {decide := true}) only [undefined_MemOp, undefined_Constraint, PreSail.internal_pick_at,
    PreSail.chooseAt, PreSail.choose, PreSail.occLabel, PreSail.undefined_bool_at, PreSail.undefined_bitvector_at,
    undefined_bool, undefined_bitvector, modifyGet, hml, hn31, Bool.and_false, Functor.map, EStateM.map, MonadStateOf.modifyGet,
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
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_STORE false (0#2 != EL0) true X1 = .ok acc t' := by
    rw [show (0#2 != EL0) = false from rfl]
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
  have hspt : t'.regs.SP_EL0.toNat % 16 = 0 := by rw [htr']; exact hsp
  obtain ⟨t3, hcs, hf3⟩ := CryptoMem.PairNative.cspa_ok t' (by rw [htr']; exact post.post.el0) (by rw [htr']; exact post.post.nrw) (by rw [htr']; exact post.post.noRME) (by rw [htr']; exact post.post.vhe) (by rw [htr']; exact post.post.aa64el0) (by rw [htr']; exact post.post.ns)
    (by rw [htr']; exact post.post.e2h) (by rw [htr']; exact post.post.tge) hspt
  simp only [hcs]
  obtain ⟨h3r, h3m, h3e⟩ := hf3
  have hEL3 : t3.regs.PSTATE.EL = 0#2 := by rw [h3r, htr']; exact post.post.el0
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
    rw [hu4r]; exact post.post.e0e
  obtain ⟨t4, hbe, hf4⟩ := MemM1.MemReadDBE.be_false u4 (by rw [hu4r]; exact post.post.el0) (by rw [hu4r]; exact post.post.nrw)
    (by rw [hu4r]; exact post.post.noRME) (by rw [hu4r]; exact post.post.vhe) (by rw [hu4r]; exact post.post.aa64el0)
    (by rw [hu4r]; exact post.post.ns) (by rw [hu4r]; exact post.post.e2h) (by rw [hu4r]; exact post.post.tge) hE0E
  simp only [hbe, Bool.false_eq_true, ite_false]
  name_call_arg Mem_set__1 1 as dv
  name_call_arg Mem_set__1 5 as addr
  have haddrA : addr = (a.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)) := by
    rw [← haddr, h3r']
    try first | rfl | (simp [Sail.BitVec.signExtend, sign_extend]) | (congr 1)
  rw [haddrA]
  have h4r : t4.regs = a.regs := hf4.1.trans hu4r
  have h4m : t4.mem = a.mem := hf4.2.1.trans hu4m
  obtain ⟨member, ⟨data, access⟩, preW⟩ := perAcc acc hA0 hAW
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hAW.base.gpr]; rfl
  obtain ⟨u, ad, t1, t5, fu, tcall, hms, hev, hr5, hm5, _⟩ := MemM1.MemWriteD7.stp_lse2_strong
    (a.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3)) hal acc t4 dv hAW pa
    (by rw [h4r]; exact preW) (by rw [h4r]; exact post.post.spe) (by rw [h4r]; exact lse2)
    (fun u ur um => by
      obtain ⟨ad, t1, call, f, p, n, i, o, v, r, m, _⟩ := translate_noupdate_at spec config rows mapping
        (query a imm7 acc) member data a u (ur.trans h4r) (um.trans h4m) current access mode
        post.post.aa64el0 debug post.post.spe notFetch dcache pa mapped raw (noUpd acc hA0)
      exact ⟨ad, t1, call, f, p, n, i, o, v, r.trans (ur.trans h4r).symm, m.trans (um.trans h4m).symm⟩)
    mmio
  obtain ⟨ad', t1', call', _, _, _, _, _, _, _, _, traffic⟩ := translate_noupdate_at spec config rows mapping
    (query a imm7 acc) member data a u (fu.1.trans h4r) (fu.2.1.trans h4m) current access mode
    post.post.aa64el0 debug post.post.spe notFetch dcache pa mapped raw (noUpd acc hA0)
  have same := tcall.symm.trans call'
  simp only [EStateM.Result.ok.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  simp only [hms]
  have hdat : dv = (BitVec.cast (by decide : 64 + 64 = 16 * 8) (BitVec.append (a.regs.gpr[(GPRSummary.key Rt2.toNat).val]) (a.regs.gpr[(GPRSummary.key Rt.toNat).val]))) := by
    rw [← hdv, h3r']
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.castWidth, BitVec.toNat_append]
  have h5r : t5.regs = a.regs := hr5.trans h4r
  have h5el : t5.regs.PSTATE.EL = 0#2 := by rw [h5r]; exact post.post.el0
  simp only [ArmCertR14.SpSet.sp_set_el0 t5 _ h5el]
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
  refine ⟨by first | (rw [h5r]) | (simp only [h5r]) | rfl, ?_, ad, t1.events, ?_, ?_⟩
  · first | (rw [hm5, h4m, hdat]; rfl) | (rw [hm5, h4m, hdat])
  · have uEv : u.events = a.events := by rw [fu.2.2, hf4.2.2, hu4e, h3e, hte, hX1e]
    rw [← uEv]; exact traffic
  · first | (rw [hev, hdat]; rfl) | (rw [hev, hdat])

#print axioms run


/-- Bits of a 64 ++ 64 append (BitVec.append form). -/
theorem app_bit (x y : BitVec 64) (i : Nat) :
    (BitVec.append x y).getLsbD i = if i < 64 then y.getLsbD i else x.getLsbD (i - 64) :=
  BitVec.getLsbD_append (x := x) (y := y) (i := i)

/-- Bytes of the stored pair: X[Rt] at the low 8, X[Rt2] at the high 8. -/
theorem stp_bit (a : NativeState) (Rt Rt2 : BitVec 5) (n : Nat) :
    (Sail.BitVec.castWidth (m := 8 * 16) (stpData a Rt Rt2)).getLsbD n =
      if n < 64 then (a.regs.gpr[(GPRSummary.key Rt.toNat).val]).getLsbD n
      else (a.regs.gpr[(GPRSummary.key Rt2.toNat).val]).getLsbD (n - 64) := by
  have e : (Sail.BitVec.castWidth (m := 8 * 16) (stpData a Rt Rt2)) = stpData a Rt Rt2 := Sail.BitVec.castWidth_eq _
  rw [e]
  unfold stpData
  rw [BitVec.getLsbD_cast, app_bit]

theorem stpByte_lo (a : NativeState) (Rt Rt2 : BitVec 5) (k : Nat) (hk : k < 8) :
    MemM1.MemWriteD4.wbyte (stpData a Rt Rt2) k = ArmCertValue.MemRegion.byteOf (a.regs.gpr[(GPRSummary.key Rt.toNat).val]) k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [ArmCertValue.MemRegion.byteOf_getLsbD _ _ _ hi]
  simp only [MemM1.MemWriteD4.wbyte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [stp_bit, if_pos (by omega)]

theorem stpByte_hi (a : NativeState) (Rt Rt2 : BitVec 5) (k : Nat) (hk : k < 8) :
    MemM1.MemWriteD4.wbyte (stpData a Rt Rt2) (8 + k) = ArmCertValue.MemRegion.byteOf (a.regs.gpr[(GPRSummary.key Rt2.toNat).val]) k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [ArmCertValue.MemRegion.byteOf_getLsbD _ _ _ hi]
  simp only [MemM1.MemWriteD4.wbyte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [stp_bit, if_neg (by omega), show 8 * (8 + k) + i - 64 = 8 * k + i by omega]

/-- Value-layer effect (ArmCert-only statement): SP := SP + c (c the decided offset), MemVHolds [.store Rt r w,
.store Rt2 r (w + 1)] when the 16 VAs of words w, w + 1 map linearly onto pa.. and other tracked bytes miss. -/
theorem value (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List ArmCertValue.Region)
    (a u : NativeState) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (pa : Nat) (c : Int)
    (hc : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 c)
    (hr : u.regs = { a.regs with SP_EL0 := ldpAddr a imm7 })
    (hm : u.mem = MemM1.MemWriteD1.wfold a.mem pa 16 (MemM1.MemWriteD4.wbyte (stpData a Rt Rt2)))
    (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ k : Nat, k < 16 → mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + 8 * (w : Int) + (k : Int))) = some (pa + k))
    (miss : ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words →
      ArmCertR14.Value.ByteFree [.store (.x (GPRSummary.key Rt.toNat)) r w, .store (.x (GPRSummary.key Rt2.toNat)) r (w + 1)] r' j' →
      ∀ q, mapping (BitVec.ofInt 64 ((pinv r'.pin : Int) + r'.off + j')) = some q → ¬ (pa ≤ q ∧ q < pa + 16)) :
    HeapV2StepCerts.RegBind.Holds [(.sp, .set .sp c)] a u ∧
      HeapV2StepCerts.Flags.nzcv u.regs = HeapV2StepCerts.Flags.nzcv a.regs ∧
      ArmCertValue.MemVHolds mapping pinv regions
        [.store (.x (GPRSummary.key Rt.toNat)) r w, .store (.x (GPRSummary.key Rt2.toNat)) r (w + 1)] a u := by
  refine ⟨ArmCertR14.Value.holds_sp a u c (by rw [hr]) (by rw [hr, ldpAddr, hc]), by rw [hr]; rfl, ?_⟩
  exact ArmCertR14.Value.memV_storePair mapping pinv regions a u _ _ r w pa _
    (fun k hk => by rw [hm, MemM1.MemWriteD1.wfold_get, if_pos (by omega), show pa + k - pa = k by omega])
    (fun q hq => by rw [hm, MemM1.MemWriteD1.wfold_get, if_neg hq])
    (fun k hk => stpByte_lo a Rt Rt2 k hk) (fun k hk => stpByte_hi a Rt Rt2 k hk) lin miss

#print axioms value
end MemClass.StpPre
