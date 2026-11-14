import NativeAccess.LdpSplit
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace NativeAccess.StpBytes
open S1Normality MemM1.NoFault MemM1.MemReadIF MemM1.MemReadD MemM1.MemReadD2
open MemM1.MemWriteD1 MemM1.MemWriteD2 MemM1.MemWriteD3 MemM1.MemWriteD5 MemM1.MemWriteD6
open ArmBridge.Draft NativeAccess.Trace NativeAccess.LdpBytes
open ArmCertMem.LdpEval ArmCertMem.StpEval
attribute [local implicit_reducible] EStateM Arch.arch_ak

theorem run (a : NativeState) (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (profile : AccessProfile) (pins : ProfileAt profile a) (lse2 : a.regs.FeatureImpl[111] = true)
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
    (certs : ∀ acc, DataShape true acc → ∀ j : Fin 16,
      S1AccessData (specs j) (configs j) (rows j) (Loops.byteQuery (pairAddr a Rn imm7) acc false j.val))
    (access : ∀ acc (shape : DataShape true acc) (j : Fin 16),
      CurrentS1AccessAt (specs j) (configs j) (rows j) (mapping j)
        (Loops.byteQuery (pairAddr a Rn imm7) acc false j.val) (certs acc shape j) a)
    (pre : ∀ acc, DataShape true acc → PreW acc a.regs)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs) (post : PostRegs2 a.regs)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (dcache : currentDCache a.regs = true)
    (mapped : ∀ j : Fin 16, mapping j (BitVec.addInt (pairAddr a Rn imm7) (j.val : Int)) = some (pa j).toNat)
    (mmio : ∀ j : Fin 16, NotMMIO (pa j))
    (outside : ∀ j k : Fin 16, ¬ (rowsFootprint (specs k).imageRows).byte (pa j).toNat)
    (raw : ∀ j : Fin 16, RawImageAt (specs j).imageRows a.mem)
    (noUpd : ∀ acc, DataShape true acc → ∀ j : Fin 16,
      NoUpdateRows {(specs j).params with haft := hostHAFT a.regs} acc (specs j).imageRows = true) :
    ∃ u, (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2 : SailM Unit) a = .ok () u ∧
      u.regs = a.regs ∧ ∃ (memEnd : Trace.State) (calls : List WriteCall) (acc : AccessDescriptor) (aligned : Bool),
        WriteChain a calls memEnd ∧ u.mem = memEnd.mem ∧ u.events = memEnd.events ∧
        calls.map WriteCall.request = Loops.byteAccess 0 (pairAddr a Rn imm7) acc false 0 ::
          (List.range' 1 15).map (Loops.byteAccess 0 (pairAddr a Rn imm7) acc aligned) ∧
        ∀ call ∈ calls, StoreLoops.ByteWitness 0 0 1 (pairAddr a Rn imm7) acc false (stpData a Rt Rt2) pa call ∨
          StoreLoops.ByteWitness 0 1 15 (pairAddr a Rn imm7) acc aligned (stpData a Rt Rt2) pa call := by

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
  have htnn : Sail.Int.toNatChecked ((Rn.toNat : Nat) : Int) = Rn.toNat := rfl
  have hR31n : ¬ Rn.toNat = 31 := by omega
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
  have rcw := LdpBytes.create_rcw X1 .MemOp_STORE false true
    (by subst hX1; exact hNoRME) (by subst hX1; exact hA64)
    (by subst hX1; exact hEL3A64) (by subst hX1; exact hNoEL3A32)
    (by subst hX1; exact hEL) (by subst hX1; exact hTME) acc t' hcr
  have plain := LdpBytes.plain_of_created hA0 hAD rcw
  rcases StoreLoops.store_bytes_low_order (Or.inr rfl) 0 (pairAddr a Rn imm7) acc true false
      unaligned dv hAW domains specs configs rows mapping pa mapped mmio outside t4 profile
      (LdpBytes.profile_of_regs pins h4r) (by rw [h4r]; exact notJoin)
      (by simp only [Bool.and_false]) plain (by rw [h4r]; exact pre acc hshape)
      member (certs acc hshape) (fun j => current_s1_frame (current j) h4r h4m)
      (fun j => (access acc hshape j).of_regs h4r)
      (by rw [h4r]; exact mode) (by rw [h4r]; exact post.post.aa64el0)
      (by rw [h4r]; exact debug) (by rw [h4r]; exact post.post.spe)
      (Or.inr (by rw [h4r]; exact post.noMTE2)) (by rw [h4r]; exact dcache)
      (by intro j; rw [h4m]; exact raw j) (by intro j; rw [h4r]; exact noUpd acc hshape j) with
    ⟨t5,calls,aligned,logical,chain,requests,witness⟩
  have hms : Mem_set__1 (pairAddr a Rn imm7) 16 acc true dv t4 = .ok () t5 := by
    unfold Mem_set__1
    simpa only [Sail.BitVec.castWidth_eq] using logical
  simp only [pairAddr] at hms
  simp only [hms]
  have hr5 := chain.registers
  have hdat : dv = (BitVec.cast (by decide : 64 + 64 = 16 * 8) (BitVec.append (a.regs.gpr[(GPRSummary.key Rt2.toNat).val]) (a.regs.gpr[(GPRSummary.key Rt.toNat).val]))) := by
    rw [← hdv, htr']
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.castWidth, BitVec.toNat_append]
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
  have dataEq : dv = stpData a Rt Rt2 := by
    rw [hdat]
    rfl
  rw [dataEq] at witness
  refine ⟨h5r,t5,calls,acc,aligned,?_,rfl,rfl,requests,witness⟩
  apply StoreLoops.chain_prepend _ chain
  exact ⟨h4r,h4m,hf4.2.2.trans (hu4e.trans (hte.trans hX1e))⟩

#print axioms run
end NativeAccess.StpBytes
