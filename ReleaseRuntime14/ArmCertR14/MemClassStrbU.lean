-- Memory (runtime14 memory classes): MemClass.StrbU.run, the ACTUAL STR (immediate, unsigned offset, 64-bit, Rn < 31,
-- no writeback) decode at an arbitrary state a, from the canonical invariant + decision-171 no-update route. Mirrors
-- MemClass.Strb.run with DataAccessEvents.native_data_write_events at size 1. Registers unchanged; memory = 1 bytes at pa.
import ArmCertWalk.DataAccessEvents
import MemM1.MemWriteD7
import MemM1.AccGPR
import CryptoMem.MemCore
import CryptoMem.Tac
import CryptoMem.Tac2
import ArmCertR14.Value
import ArmCertR14.XRead
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false
namespace MemClass.StrbU
open ArmCertWalk ArmBridge.Draft

/-- The access address X[Rn] + (imm12 << 3). -/
def addr (a : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) : BitVec 64 :=
  a.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.zeroExtend 64 imm12 <<< 0)

/-- The 8-byte data query for descriptor acc. -/
def query (a : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) (acc : AccessDescriptor) : AccessQuery :=
  ⟨addr a Rn imm12, ⟨acc, true⟩, ((1 : Nat) : Int)⟩

/-- The stored datum: X[Rt] (low 8 bytes). -/
def stData (a : NativeState) (Rt : BitVec 5) : BitVec (1 * 8) :=
  BitVec.setWidth (1 * 8) (a.regs.gpr[(GPRSummary.key Rt.toNat).val])

/-- Actual translation traffic then the n-byte write, from before (no-update form). -/
def StoreEvents {domain : QueryDomain} (spec : TopologyImageSpec domain) (va : BitVec 64) (pa : BitVec 56) (n : Nat)
    (before : Array Event) (kind : Access_kind arm_acc_type) (value : BitVec (8 * n)) (after : Array Event) : Prop :=
  ∃ (info : TranslationStartInfo) (walk : List (Nat × Bool × Array Event))
    (leaf : Nat × Bool × Array Event) (middle : Array Event) (address : AddressDescriptor),
    TranslateTrafficFrom (before.push (.translationStart info)) walk leaf middle ∧
    (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧
    ((spec.logicalRows.map (·.logical)).Nodup → walk.map (·.1) = declaredSlots spec.logicalRows spec.layout va) ∧
    address.vaddress = va ∧
    after = (middle.push (.translationEnd address)).push (.memWrite pa.toNat n (some va.toNat) kind (some value) none)

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm12 : BitVec 12) (Rn Rt : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc →
      domain (query a Rn imm12 acc) ∧ (∃ data : S1AccessData spec config rows (query a Rn imm12 acc),
        CurrentS1AccessAt spec config rows mapping (query a Rn imm12 acc) data a) ∧
      MemM1.MemWriteD6.PreW acc a.regs)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (pr : MemM1.MemReadD2.PostRegs2 a.regs)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false)
    (pa : BitVec 56) (mapped : mapping (addr a Rn imm12) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (raw : RawImageAt spec.imageRows a.mem)
    (none : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u, (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 0#2 : SailM Unit) a = .ok () u ∧
      u.regs = a.regs ∧
      u.mem = MemM1.MemWriteD1.wfold a.mem pa.toNat 1
        (fun j => (Sail.BitVec.castWidth (m := 8 * 1) (stData a Rt)).extractLsb' (8 * j) 8) ∧
      StoreEvents spec (addr a Rn imm12) pa 1 a.events MemM1.MemWriteD4.akPlain
        (Sail.BitVec.castWidth (m := 8 * 1) (stData a Rt)) u.events := by
  unfold decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned
  unfold execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have hRn' : ¬ ((Rn.toNat : Int) = 31) := by omega
  have hb2 : (((Rn.toNat : Int)) != 31) = true := by simpa using hRn'
  have htn : Sail.Int.toNatChecked ((Rn.toNat : Nat) : Int) = Rn.toNat := rfl
  have htt : Sail.Int.toNatChecked ((Rt.toNat : Nat) : Int) = Rt.toNat := rfl
  have hR31 : ¬ Rn.toNat = 31 := by omega
  simp (config := {decide := true}) only [undefined_MemOp, undefined_Constraint, PreSail.internal_pick_at,
    PreSail.chooseAt, PreSail.choose, PreSail.occLabel, PreSail.undefined_bool_at, PreSail.undefined_bitvector_at,
    undefined_bool, undefined_bitvector, modifyGet, hb2, htn, htt, hR31, Functor.map, EStateM.map, MonadStateOf.modifyGet, EStateM.modifyGet, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind, ite_true, ite_false, dite_true, dite_false,
    hRn', Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and, beq_iff_eq, bne_iff_ne, ne_eq,
    reduceIte, reduceDIte, Bool.not_true, Bool.not_false, decide_true, decide_false]
  have rdP : ∀ st : NativeState, (readReg PSTATE : SailM ProcState) st = .ok st.regs.PSTATE st :=
    fun _ => rfl
  have hEL := pr.post.el0
  simp (config := {decide := true}) only [rdP, hEL]
  name_call_state CreateAccDescGPR as X1
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr⟩ := MemM1.AccGPR.create X1 ArmFull.MemOp.MemOp_STORE false true
    (by subst hX1; exact pr.post.noRME) (by subst hX1; exact pr.post.nrw) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact pr.post.ns) (by subst hX1; exact hTME)
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_STORE false (0#2 != EL0)
      (ArmFull.MemOp.MemOp_STORE != ArmFull.MemOp.MemOp_PREFETCH && (false || true)) X1 = .ok acc t' := by
    rw [show (0#2 != EL0) = false from rfl,
      show (ArmFull.MemOp.MemOp_STORE != ArmFull.MemOp.MemOp_PREFETCH && (false || true)) = true from rfl]
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
  have hte' : t'.events = a.events := hte.trans hX1e
  simp only [CryptoMem.MemCore.xread64 t' Rn hRn]
  reduce_closed_nat
  simp only [ArmCertR14.XRead.xread8 t' Rt hRt]
  name_call_arg Mem_set 1 as dv
  name_call_arg Mem_set 4 as ad0
  have haddrA : ad0 = addr a Rn imm12 := by
    rw [← had0, htr']
    first | rfl | (simp [Sail.BitVec.zeroExtend, addr]) | (congr 1)
  rw [haddrA]
  have hdat : dv = stData a Rt := by
    rw [← hdv, htr']
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb, BitVec.castWidth, stData, CryptoMem.MemCore.brReset]
  obtain ⟨member, ⟨dataQ, access⟩, preW⟩ := perAcc acc hA0 hAW
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hAW.base.gpr]; rfl
  obtain ⟨address, translated, final, faultOut, clean, _, _, eventsT, hms, hev, hr2, hm2⟩ :=
    native_data_write_events spec config rows mapping (query a Rn imm12 acc) member dataQ t'
      (current_s1_frame current htr' htm') (access.of_regs htr')
      (by rw [htr']; exact mode) (by rw [htr']; exact pr.post.aa64el0)
      (by rw [htr']; exact debug) (by rw [htr']; exact pr.post.spe)
      1 (by simp [MemM1.MemWriteD1.SizeOK]) hAW (by rw [htr']; exact preW) rfl rfl (Nat.mod_one _) pa mapped mmio dv
  obtain ⟨_, out, _, _, _, _, _, _, vaddr, _, _, _, _, registers, _⟩ := clean
  have tRegs : translated.regs = a.regs := by
    rw [registers, htr']; unfold fetchGuardRegs; simp only [query, notFetch, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨info, walk, leaf, middle, _, traffic, endEv, cond, _, slots⟩ := eventsT
  obtain ⟨walkFlags, leafFlag, tMem⟩ := cond (by rw [htm']; exact raw) (by rw [htr']; exact none acc hA0)
  change Mem_set (addr a Rn imm12) 1 acc dv t' = .ok () final at hms
  simp only [hms]
  try simp only [PreSail.assert, ite_true, pure, EStateM.pure]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hr2' : final.regs = a.regs := hr2.trans tRegs
  have hspe : final.regs.bank_Bool .SPESampleInFlight = false := by rw [hr2']; exact pr.post.spe
  try simp only [rdB, CryptoMem.MemCore.setGpr, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, Bool.cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  have kind : AccessDescriptor_to_Access_kind acc = MemM1.MemWriteD4.akPlain := by
    exact MemM1.MemWriteD7.akT acc hAW
  refine ⟨hr2', ?_, ?_⟩
  · rw [hm2, tMem, htm', hdat]
  · refine ⟨info, walk, leaf, middle, address, by rw [← hte']; exact traffic, walkFlags, leafFlag, slots, ?_, ?_⟩
    · exact vaddr
    · rw [hev, endEv, hdat]
      simp only [query] at vaddr ⊢
      rw [vaddr, kind]

#print axioms run

/-- The stored byte is the low byte of X[Rt]. -/
theorem stByte (a : NativeState) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8 * 1) (stData a Rt)).extractLsb' (8 * 0) 8 =
      (a.regs.gpr[(GPRSummary.key Rt.toNat).val]).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Sail.BitVec.castWidth, stData, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi]

/-- Value-layer effect (ArmCert-only statement): registers unchanged, MemVHolds [.storeb Rt r j]. -/
theorem value (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List ArmCertValue.Region)
    (a u : NativeState) (Rt : BitVec 5) (pa : Nat) (hr : u.regs = a.regs)
    (hm : u.mem = MemM1.MemWriteD1.wfold a.mem pa 1 (fun j => (Sail.BitVec.castWidth (m := 8 * 1) (stData a Rt)).extractLsb' (8 * j) 8))
    (r : ArmCertValue.Region) (j : Nat)
    (lin : mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + (j : Int))) = some pa)
    (miss : ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words → ArmCertR14.Value.ByteFree [.storeb (.x (GPRSummary.key Rt.toNat)) r j] r' j' → ∀ q,
      mapping (BitVec.ofInt 64 ((pinv r'.pin : Int) + r'.off + j')) = some q → ¬ (pa ≤ q ∧ q < pa + 1)) :
    HeapV2StepCerts.RegBind.Holds [] a u ∧
      HeapV2StepCerts.Flags.nzcv u.regs = HeapV2StepCerts.Flags.nzcv a.regs ∧
      ArmCertValue.MemVHolds mapping pinv regions [.storeb (.x (GPRSummary.key Rt.toNat)) r j] a u := by
  have hk : ∀ r, HeapV2StepCerts.RegBind.updOf [] r = .keep ∨ HeapV2StepCerts.RegBind.updOf [] r = .drop :=
    fun _ => Or.inl rfl
  refine ⟨HeapV2StepCerts.RegBind.holds_of_regs_eq hk (by rw [hr]) (by rw [hr]), by rw [hr],
    ArmCertR14.Value.memV_of_writes mapping pinv regions a u _ pa 1 (fun q hq => by
      rw [hm, MemM1.MemWriteD1.wfold_get, if_neg hq]) miss (fun e he => ?_)⟩
  rw [List.mem_singleton] at he; subst he
  refine ⟨fun e he => ?_, fun r h => by simp at h, fun r h => by simp at h⟩
  rw [List.mem_singleton] at he; subst he
  show ArmCertValue.regionByte mapping pinv u r j = _
  rw [ArmCertValue.regionByte, lin, Option.bind_some, hm, MemM1.MemWriteD1.wfold_get,
    if_pos (by omega), Nat.sub_self, stByte]
  rfl

#print axioms value

end MemClass.StrbU
