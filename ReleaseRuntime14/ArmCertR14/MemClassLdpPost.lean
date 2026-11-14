-- Memory (runtime14 memory classes): MemClass.LdpPost.run — ACTUAL LDP (64-bit pair, POST-INDEX, base SP: load at SP, then
-- SP := SP + off) decode at arbitrary `a`: one LSE2 16-byte load (adapted from MemClass.Ldp.run per CruxMem.LdpPostEval), from the canonical invariant + decision-171
-- no-update route. Mirrors SDK CruxMem.LdpEval.decode_ldp_eval with its AgreesV3 read (readV5_ldp)
-- replaced by load16_noupdate (no premise). Registers = SDK `ldpPost`.
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
namespace MemClass.LdpPost
open ArmCertWalk ArmBridge.Draft

/-- The access address: SP itself (post-index). -/
abbrev ldpAddr (t : NativeState) (imm7 : BitVec 7) : BitVec 64 := t.regs.SP_EL0

/-- Low / high doubleword of the loaded 16 bytes (LSE2 single access, little-endian). -/
def ldpLo (d : BitVec 128) : BitVec 64 :=
  Sail.BitVec.zeroExtend (BitVec.castWidth (BitVec.castWidth (Sail.BitVec.extractLsb (BitVec.castWidth d : BitVec 128) 63 0) : BitVec 64) : BitVec 64) 64
def ldpHi (d : BitVec 128) : BitVec 64 :=
  Sail.BitVec.zeroExtend (BitVec.castWidth (BitVec.castWidth (Sail.BitVec.extractLsb (BitVec.castWidth d : BitVec 128) 127 64) : BitVec 64) : BitVec 64) 64

/-- The state after Sail's own `writeReg SP_EL0 v`. -/
def spWrite (s : NativeState) (v : BitVec 64) : NativeState :=
  match (writeReg SP_EL0 v : SailM Unit) s with
  | .ok _ s2 => s2
  | .error _ s2 => s2

/-- Sail's `writeReg SP_EL0` is exactly the SP_EL0 field update (definitional). -/
theorem spWrite_eq (s : NativeState) (v : BitVec 64) : spWrite s v = { s with regs := { s.regs with SP_EL0 := v } } := rfl

/-- The register file after the leaf: X[Rt] := lo, X[Rt2] := hi (provider setGpr), then SP_EL0 := SP + (signExtend imm7 << 3)
    through Sail `writeReg SP_EL0`. -/
def ldpPost (t : NativeState) (Rt Rt2 : BitVec 5) (imm7 : BitVec 7) (d : BitVec 128) : NativeState :=
  let u := CryptoMem.MemCore.setGpr (CryptoMem.MemCore.setGpr t (GPRSummary.key Rt.toNat) (ldpLo d)) (GPRSummary.key Rt2.toNat) (ldpHi d)
  spWrite u (t.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3))

def query (a : NativeState) (imm7 : BitVec 7) (acc : AccessDescriptor) : AccessQuery :=
  ⟨ldpAddr a imm7, ⟨acc, true⟩, ((16 : Nat) : Int)⟩

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (hRtt : Rt ≠ Rt2)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemReadD2.AccDR2 acc →
      domain (query a imm7 acc) ∧ ∃ data : S1AccessData spec config rows (query a imm7 acc),
        CurrentS1AccessAt spec config rows mapping (query a imm7 acc) data a)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (post : MemM1.MemReadD2.PostRegs2 a.regs)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (lse2 : a.regs.FeatureImpl[111] = true)
    (dcache : currentDCache a.regs = true)
    (hsp : a.regs.SP_EL0.toNat % 16 = 0) (hal : (ldpAddr a imm7).toNat % 16 = 0)
    (pa : BitVec 56) (mapped : mapping (ldpAddr a imm7) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (data : BitVec 128) (bytes : ∀ i < 16, a.mem[pa.toNat + i]? = some ((data : BitVec (16 * 8)).extractLsb' (8 * i) 8))
    (raw : RawImageAt spec.imageRows a.mem)
    (noUpd : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u, (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt 31#5 Rt2 imm7 1#1 2#2 : SailM Unit) a = .ok () u ∧
      u.regs = (ldpPost a Rt Rt2 imm7 data).regs ∧ u.mem = a.mem ∧
      ∃ ad mid, NoUpdateTraffic spec (ldpAddr a imm7) a.events ad mid ∧
        u.events = mid.push (.memRead pa.toNat 16 (some (ldpAddr a imm7).toNat)
          (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) false) := by
  unfold decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx
  unfold execute_aarch64_instrs_memory_pair_general_post_idx
  have hRtt' : ¬ ((Rt.toNat : Int) = (Rt2.toNat : Int)) := by
    intro h; apply hRtt; apply BitVec.eq_of_toNat_eq; omega
  have hb1 : (((Rt.toNat : Int)) == ((Rt2.toNat : Int))) = false := by simpa using hRtt'
  have hn31 : ((((31#5 : BitVec 5).toNat : Nat) : Int) != 31) = false := rfl
  simp (config := {decide := true}) only [undefined_MemOp, undefined_Constraint, PreSail.internal_pick_at,
    PreSail.chooseAt, PreSail.choose, PreSail.occLabel, PreSail.undefined_bool_at, PreSail.undefined_bitvector_at,
    undefined_bool, undefined_bitvector, modifyGet, hb1, hn31, Bool.and_false, Functor.map, EStateM.map, MonadStateOf.modifyGet,
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
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_LOAD false (0#2 != EL0) true X1 = .ok acc t' := by
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
  simp only [MemM1.MemReadD2.lse2_on t3 hl2]
  simp (config := {decide := true}) only [ite_true, ite_false, Bool.true_and, Bool.and_true, Bool.not_false,
    Bool.not_true, bne_iff_ne, ne_eq, decide_true, decide_false]
  reduce_closed_nat
  name_call_arg Mem_read__1 3 as addr
  have h3r' : t3.regs = a.regs := h3r.trans htr'
  have h3m' : t3.mem = a.mem := h3m.trans htm'
  have haddrA : addr = a.regs.SP_EL0 := by
    rw [← haddr, h3r']
    try first | rfl | (simp [Sail.BitVec.signExtend, sign_extend]) | (congr 1)
  rw [haddrA]
  obtain ⟨member, dataQ, access⟩ := perAcc acc hA0 hAD
  obtain ⟨ad, mid, t4, hmr, traffic, vaddr, hev, hr4, hm4⟩ := load16_noupdate spec config rows mapping t3
    (ldpAddr a imm7) hal acc hAD member dataQ (current_s1_frame current h3r' h3m') (access.of_regs h3r')
    (by rw [h3r']; exact mode) (by rw [h3r']; exact debug) (by rw [h3r']; exact post) (by rw [h3r']; exact lse2)
    (by rw [h3r']; exact dcache) pa mapped mmio (by rw [h3m']; exact raw)
    (by rw [h3r']; exact noUpd acc hA0) data (by intro i hi; rw [h3m']; exact bytes i hi)
  simp only [EStateM.bind, EStateM.map, hmr]
  have hgpr : acc.acctype = .AccessType_GPR := hAW.base.gpr
  have h4r : t4.regs = a.regs := hr4.trans h3r'
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
  have h5el : t5.regs.PSTATE.EL = 0#2 := by rw [h5r]; exact post.post.el0
  simp (disch := first | exact h5el | (simp only [CryptoMem.MemCore.setGpr]; exact h5el)) only [ArmCertR14.SpSet.sp_set_el0]
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
  have h5m : t5.mem = a.mem := hf5.2.1.trans (hm4.trans h3m')
  have kind : AccessDescriptor_to_Access_kind acc = .AK_explicit { variety := .AV_plain, strength := .AS_normal } :=
    MemM1.MemReadD2.kind_eq2 acc hAD
  have hev0 : t3.events = a.events := by rw [h3e, hte, hX1e]
  refine ⟨?_, h5m, ad, mid, by rw [← hev0]; exact traffic, ?_⟩
  · simp only [ldpPost, spWrite_eq, CryptoMem.MemCore.setGpr]
    rw [h5r]
    try rfl
  · rw [hf5.2.2, hev, kind]

#print axioms run


theorem lo_byte (d : BitVec 128) (k : Nat) (hk : k < 8) :
    ArmCertValue.MemRegion.byteOf (ldpLo d) k = d.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [ArmCertValue.MemRegion.byteOf_getLsbD _ _ _ hi]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ldpLo, Sail.BitVec.zeroExtend, Sail.BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb']

theorem hi_byte (d : BitVec 128) (k : Nat) (hk : k < 8) :
    ArmCertValue.MemRegion.byteOf (ldpHi d) k = d.extractLsb' (8 * (8 + k)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [ArmCertValue.MemRegion.byteOf_getLsbD _ _ _ hi]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ldpHi, Sail.BitVec.zeroExtend, Sail.BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb']

/-- Value-layer effect (ArmCert-only statement): X[Rt], X[Rt2] clobbered, SP := SP + c, NZCV unchanged,
MemVHolds [.load Rt r w, .load Rt2 r (w + 1)] when words w, w + 1's 16 VAs map linearly onto pa.. holding the datum. -/
theorem value (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List ArmCertValue.Region)
    (a u : NativeState) (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRtt : Rt ≠ Rt2) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (data : BitVec 128) (pa : Nat) (c : Int)
    (hc : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 c)
    (hr : u.regs = (ldpPost a Rt Rt2 imm7 data).regs) (hm : u.mem = a.mem)
    (hin : ∀ k, k < 16 → a.mem[pa + k]? = some (data.extractLsb' (8 * k) 8))
    (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ k : Nat, k < 16 → mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + 8 * (w : Int) + (k : Int))) = some (pa + k)) :
    HeapV2StepCerts.RegBind.Holds [(.x (GPRSummary.key Rt.toNat), .drop), (.x (GPRSummary.key Rt2.toNat), .drop), (.sp, .set .sp c)] a u ∧
      HeapV2StepCerts.Flags.nzcv u.regs = HeapV2StepCerts.Flags.nzcv a.regs ∧
      ArmCertValue.MemVHolds mapping pinv regions
        [.load (.x (GPRSummary.key Rt.toNat)) r w, .load (.x (GPRSummary.key Rt2.toNat)) r (w + 1)] a u := by
  have hg : u.regs.gpr = ((a.regs.gpr.set (GPRSummary.key Rt.toNat).val (ldpLo data) (GPRSummary.key Rt.toNat).isLt).set
      (GPRSummary.key Rt2.toNat).val (ldpHi data) (GPRSummary.key Rt2.toNat).isLt) := by
    rw [hr]; rfl
  have hne : (GPRSummary.key Rt2.toNat).val ≠ (GPRSummary.key Rt.toNat).val := by
    have k1 : ∀ n : Fin 31, (GPRSummary.key n.val).val = n.val := by decide
    rw [k1 ⟨Rt2.toNat, hRt2⟩, k1 ⟨Rt.toNat, hRt⟩]
    intro h; exact hRtt (BitVec.eq_of_toNat_eq h.symm)
  have vlo : u.regs.gpr[(GPRSummary.key Rt.toNat).val] = ldpLo data := by
    rw [hg, Vector.getElem_set_ne _ _ hne, Vector.getElem_set_self]
  have vhi : u.regs.gpr[(GPRSummary.key Rt2.toNat).val] = ldpHi data := by
    rw [hg, Vector.getElem_set_self]
  refine ⟨ArmCertR14.Value.holds_pair_sp a u _ _ c _ _ hg (by rw [hr]; show a.regs.SP_EL0 + (BitVec.signExtend 64 imm7 <<< 3) = _; rw [hc]),
    by rw [hr]; rfl, ?_⟩
  refine ArmCertR14.Value.memV_loadPair mapping pinv regions a u _ _ r w pa (fun k => data.extractLsb' (8 * k) 8) hm hin
    (fun k hk => ?_) (fun k hk => ?_) lin
  · show _ = ArmCertValue.MemRegion.byteOf (u.regs.gpr[(GPRSummary.key Rt.toNat).val]) k
    rw [vlo, lo_byte data k hk]
  · show _ = ArmCertValue.MemRegion.byteOf (u.regs.gpr[(GPRSummary.key Rt2.toNat).val]) k
    rw [vhi, hi_byte data k hk]

#print axioms value
end MemClass.LdpPost
