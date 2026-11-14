import NativeAccess.HighStore
import HeapV2StepCerts.MemRunD
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace NativeAccess.LdpBytes
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open ArmBridge.Draft NativeAccess.Trace
attribute [local implicit_reducible] EStateM Arch.arch_ak

theorem nadg_rcw (s : Trace.State) (acc : AccessDescriptor) (t : Trace.State)
    (run : MemM1.AccGPR.nadg_native s = .ok acc t) : acc.rcw = false := by
  delta MemM1.AccGPR.nadg_native at run
  injection run with value state
  subst value
  rfl

/-- A field of the actual past descriptor constructor, omitted by older
descriptor projections. It is derived from the frozen constructor. -/
theorem create_rcw (s : Trace.State) (memop : ArmFull.MemOp) (nontemporal tagchecked : Bool)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hEL : s.regs.PSTATE.EL = 0#2)
    (hTME : s.regs.FeatureImpl[227] = false)
    (acc : AccessDescriptor) (t : Trace.State)
    (run : CreateAccDescGPR memop nontemporal false tagchecked s = .ok acc t) : acc.rcw = false := by
  have hn : NewAccDesc .AccessType_GPR s = MemM1.AccGPR.nadg_native s :=
    MemM1.AccGPR.nadg_eq s hNoRME hA64 hEL3A64 hNoEL3A32 hEL
  have frame := MemM1.AccGPR.nadg_frame s hEL
  cases native : MemM1.AccGPR.nadg_native s with
  | error error u =>
    rw [native] at frame
    exact frame.elim
  | ok base u =>
    rw [native] at frame
    have ht : HaveTME () u = .ok false u :=
      MemM1.AccGPR.tme_off u (by rw [frame.1]; exact hTME)
    have baseRcw := nadg_rcw s base u native
    unfold CreateAccDescGPR at run
    simp only [Bind.bind,EStateM.bind,hn,native,ht,Pure.pure,EStateM.pure,
      Bool.not_false,Bool.false_eq_true,ite_true,ite_false] at run
    have fields := congrArg AccessDescriptor.rcw (EStateM.Result.ok.inj run).1
    exact fields.symm.trans baseRcw

theorem plain_of_created {acc : AccessDescriptor} (base : MemM1.Witness.Acc0 acc)
    (read : AccDR2 acc) (rcw : acc.rcw = false) : Plain acc := by
  refine ⟨?_,rcw,base.ls64,read.exclusive,read.atomicop,read.acqsc,read.acqpc,read.relsc⟩
  rw [read.gpr]
  rfl

#print axioms create_rcw
#print axioms plain_of_created

theorem profile_of_regs {p : AccessProfile} {s t : Trace.State}
    (pins : ProfileAt p s) (regs : t.regs = s.regs) : ProfileAt p t := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [regs]; exact pins.lse2
  · rw [regs]; exact pins.lrcpc3
  · rcases pins.host with ⟨el,nrw,aa,rme,vhe,ns,e2h,tge⟩
    constructor <;> rw [regs] <;> assumption
  · rw [regs]; exact pins.alignment_disabled

def pairAddr (s : NativeState) (Rn : BitVec 5) (imm7 : BitVec 7) : BitVec 64 :=
  s.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.signExtend 64 imm7 <<< 3)

-- Adapted checked PROOF skeleton (not ISA definitions) from Memory RunLdpRn16.
-- Source SHA256 2758ff993fa659f0b9d9340c1a5d6a7a92e43f4fa237ab6657ea536394a74d7e. No data-address alignment premise is inherited.
open ArmCertMem.LdpEval ArmCertMem.StpEval

theorem run (a : NativeState) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (profile : AccessProfile) (pins : ProfileAt profile a)
    (lse2 : a.regs.FeatureImpl[111] = true)
    (unaligned : Logical.accessAligned (pairAddr a Rn imm7) 16 true = false)
    (notJoin : (a.regs.FeatureImpl[111] &&
      (Align_bits (BitVec.subInt (BitVec.addInt (pairAddr a Rn imm7) ((16 : Nat) : Int)) 1) 16 ==
        Align_bits (pairAddr a Rn imm7) 16)) = false)
    (domains : Fin 16 → BitVec 64 → Prop)
    (specs : (j : Fin 16) → TopologyImageSpec (fun q => domains j q.va))
    (configs : Fin 16 → AttributeConfig) (rows : Fin 16 → List PermissionRow)
    (mapping : Fin 16 → BitVec 64 → Option Nat) (pa : Fin 16 → BitVec 56)
    (current : ∀ j : Fin 16, CurrentS1At (specs j) (configs j) (rows j) a)
    (member : ∀ j : Fin 16, domains j (BitVec.addInt (pairAddr a Rn imm7) (j.val : Int)))
    (certs : ∀ acc, DataShape false acc → ∀ j : Fin 16,
      S1AccessData (specs j) (configs j) (rows j) (Loops.byteQuery (pairAddr a Rn imm7) acc false j.val))
    (access : ∀ acc (shape : DataShape false acc) (j : Fin 16),
      CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
        (Loops.byteQuery (pairAddr a Rn imm7) acc false j.val) (certs acc shape j) a)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs) (post : PostRegs2 a.regs)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (dcache : currentDCache a.regs = true)
    (mapped : ∀ j : Fin 16, mapping j (BitVec.addInt (pairAddr a Rn imm7) (j.val : Int)) = some (pa j).toNat)
    (mmio : ∀ j : Fin 16, NotMMIO (pa j)) (data : BitVec 128)
    (bytes : ∀ j : Fin 16, a.mem[(pa j).toNat]? = some (data.extractLsb' (8 * j.val) 8))
    (raw : ∀ j : Fin 16, RawImageAt (specs j).imageRows a.mem)
    (noUpd : ∀ acc, DataShape false acc → ∀ j : Fin 16,
      NoUpdateRows {(specs j).params with haft := hostHAFT a.regs} acc (specs j).imageRows = true) :
    ∃ u, (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2 : SailM Unit) a = .ok () u ∧
      u.regs = (ldpPost a Rt Rt2 data).regs ∧ u.mem = a.mem ∧
      ∃ (memEnd : Trace.State) (calls : List ReadCall) (acc : AccessDescriptor) (aligned : Bool),
        ReadChain a calls memEnd ∧ u.events = memEnd.events ∧
        calls.map ReadCall.request = Loops.byteAccess 0 (pairAddr a Rn imm7) acc false 0 ::
          (List.range' 1 15).map (Loops.byteAccess 0 (pairAddr a Rn imm7) acc aligned) := by

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
  have hEL := post.post.el0
  have hNoRME := post.post.noRME
  have hA64 := post.post.nrw
  have hNS := post.post.ns
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
  have rcw := create_rcw X1 .MemOp_LOAD false true
    (by subst hX1; exact hNoRME) (by subst hX1; exact hA64)
    (by subst hX1; exact hEL3A64) (by subst hX1; exact hNoEL3A32)
    (by subst hX1; exact hEL) (by subst hX1; exact hTME) acc t' hcr
  have plain := plain_of_created hA0 hAD rcw
  rcases Plans.read_bytes_low (Or.inr rfl) 0 (pairAddr a Rn imm7) acc true unaligned data hAD
      domains specs configs rows mapping pa mapped mmio t' profile (profile_of_regs pins htr')
      (by rw [htr']; exact notJoin) plain member (certs acc hshape)
      (fun j => current_s1_frame (current j) htr' htm')
      (fun j => (access acc hshape j).of_regs htr')
      (by rw [htr']; exact mode) (by rw [htr']; exact debug)
      (by rw [htr']; exact post) (by rw [htr']; exact dcache)
      (by intro j; rw [htm']; exact raw j)
      (by intro j; rw [htr']; exact noUpd acc hshape j)
      (by intro j; rw [htm']; exact bytes j) with
    ⟨t4,calls,aligned,logical,chain,requests⟩
  have hmr : Mem_read__1 (pairAddr a Rn imm7) 16 acc true t' = .ok data t4 := by
    have hsize : (((((16 : Nat) == 1 || (16 : Nat) == 2) || (16 : Nat) == 4) || (16 : Nat) == 8) || (16 : Nat) == 16) = true := by decide
    unfold Mem_read__1
    simp only [hsize,ArmFull.assert,PreSail.assert,Bind.bind,EStateM.bind,Functor.map,EStateM.map,
      Pure.pure,EStateM.pure,logical,Sail.BitVec.castWidth_eq,ite_true]
  have hr4 := chain.registers
  have hm4 := chain.memory
  simp only [pairAddr] at hmr
  simp only [EStateM.bind, EStateM.map, hmr]
  have hgpr : acc.acctype = .AccessType_GPR := hAW.base.gpr
  have h4r : t4.regs = a.regs := hr4.trans htr'
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
  have h5m : t5.mem = a.mem := hf5.2.1.trans (hm4.trans htm')
  refine ⟨?_,h5m,t4,calls,acc,aligned,?_,?_,requests⟩
  · simp only [ldpPost,CryptoMem.MemCore.setGpr]
    rw [h5r]
    try rfl
  · exact Loops.readChain_prepend ⟨htr',htm',hte.trans hX1e⟩ chain
  · exact hf5.2.2

#print axioms run
end NativeAccess.LdpBytes
