-- Memory (runtime14 memory classes, / a9b7): MemClass.LdrU32.run, the ACTUAL LdrU32 (immediate,
-- unsigned offset, Rn < 31, no writeback) decode at an arbitrary state a, from the canonical invariant
-- (CurrentS1At + per-descriptor CurrentS1AccessAt), with the no-update route. Mirrors MemClass.Ldrb.run with
-- the aligned 4-byte read MemM1.MemSingle4V5.memRead2_4; register result as CruxMem.Ldr64uEval.post (restated here).
import ArmCertWalk.DataAccessEvents
import MemM1.MemSingle4V5
import MemM1.AccGPR
import CryptoMem.MemCore
import CryptoMem.Tac
import CryptoMem.Tac2
import ArmCertR14.Value
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false
namespace MemClass.LdrU32
open ArmCertWalk ArmBridge.Draft

/-- X[Rt] value: the 4-byte datum zero-extended (W-register write). -/
def val (d : BitVec (4 * 8)) : BitVec 64 :=
  Sail.BitVec.zeroExtend (BitVec.castWidth (Sail.BitVec.zeroExtend (BitVec.castWidth d : BitVec 32) 32) : BitVec 32) 64

/-- The register file after the leaf: X[Rt] := val data (no writeback). -/
def post (t : NativeState) (Rt : BitVec 5) (d : BitVec (4 * 8)) : NativeState :=
  CryptoMem.MemCore.setGpr t (GPRSummary.key Rt.toNat) (val d)

/-- The access address X[Rn] + (imm12 << 3). -/
def addr (a : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) : BitVec 64 :=
  a.regs.gpr[(GPRSummary.key Rn.toNat).val] + (BitVec.zeroExtend 64 imm12 <<< 2)

/-- The 4-byte data query for descriptor acc. -/
def query (a : NativeState) (Rn : BitVec 5) (imm12 : BitVec 12) (acc : AccessDescriptor) : AccessQuery :=
  ⟨addr a Rn imm12, ⟨acc, true⟩, ((4 : Nat) : Int)⟩

/-- Actual translation traffic then the n-byte read, from before (decision-171 no-update form). -/
def LoadEvents {domain : QueryDomain} (spec : TopologyImageSpec domain) (va : BitVec 64) (pa : BitVec 56) (n : Nat)
    (before : Array Event) (kind : Access_kind arm_acc_type) (after : Array Event) : Prop :=
  ∃ (info : TranslationStartInfo) (walk : List (Nat × Bool × Array Event))
    (leaf : Nat × Bool × Array Event) (middle : Array Event) (address : AddressDescriptor),
    TranslateTrafficFrom (before.push (.translationStart info)) walk leaf middle ∧
    (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧
    ((spec.logicalRows.map (·.logical)).Nodup → walk.map (·.1) = declaredSlots spec.logicalRows spec.layout va) ∧
    address.vaddress = va ∧
    after = (middle.push (.translationEnd address)).push (.memRead pa.toNat n (some va.toNat) kind false)

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm12 : BitVec 12) (Rn Rt : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemReadD2.AccDR2 acc →
      domain (query a Rn imm12 acc) ∧ ∃ data : S1AccessData spec config rows (query a Rn imm12 acc),
        CurrentS1AccessAt spec config rows mapping (query a Rn imm12 acc) data a)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (pr : MemM1.MemReadD2.PostRegs2 a.regs)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (dcache : currentDCache a.regs = true)
    (halign : (addr a Rn imm12).toNat % 4 = 0)
    (pa : BitVec 56) (mapped : mapping (addr a Rn imm12) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (data : BitVec (4 * 8)) (bytes : ∀ i < 4, a.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8))
    (raw : RawImageAt spec.imageRows a.mem)
    (none : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u, (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 2#2 : SailM Unit) a = .ok () u ∧
      u.regs = (post a Rt data).regs ∧ u.mem = a.mem ∧
      LoadEvents spec (addr a Rn imm12) pa 4 a.events (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) u.events := by
  unfold decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned
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
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr⟩ := MemM1.AccGPR.create X1 ArmFull.MemOp.MemOp_LOAD false true
    (by subst hX1; exact pr.post.noRME) (by subst hX1; exact pr.post.nrw) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact pr.post.ns) (by subst hX1; exact hTME)
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_LOAD false (0#2 != EL0)
      (ArmFull.MemOp.MemOp_LOAD != ArmFull.MemOp.MemOp_PREFETCH && (false || true)) X1 = .ok acc t' := by
    rw [show (0#2 != EL0) = false from rfl,
      show (ArmFull.MemOp.MemOp_LOAD != ArmFull.MemOp.MemOp_PREFETCH && (false || true)) = true from rfl]
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
  name_call_arg Mem_read 3 as ad0
  have haddrA : ad0 = addr a Rn imm12 := by
    rw [← had0, htr']
    first | rfl | (simp [Sail.BitVec.zeroExtend, addr]) | (congr 1)
  rw [haddrA]
  obtain ⟨member, dataQ, access⟩ := perAcc acc hA0 hAD
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hAD.gpr]; rfl
  obtain ⟨ad, t1, t2, hQ, hmr, hev, hr2, hm2⟩ := MemM1.MemSingle4V5.memRead2_4
    (addr a Rn imm12) halign acc t' pa data hAD (by rw [htr']; exact pr.noMTE2)
    (fun ad t1 => t1.regs = a.regs ∧ t1.mem = a.mem ∧ LoadEvents spec (addr a Rn imm12) pa 4 a.events
        (AccessDescriptor_to_Access_kind acc) ((t1.events).push (.memRead pa.toNat 4 (some ad.vaddress.toNat)
          (AccessDescriptor_to_Access_kind acc) false)))
    (by
      intro u fu
      have uRegs : u.regs = a.regs := fu.1.trans htr'
      have uMem : u.mem = a.mem := fu.2.1.trans htm'
      have uEvents : u.events = a.events := fu.2.2.trans hte'
      obtain ⟨address, fault, other, call, fields, _, _, _, _, _, _, _, writes, _,
          info, walk, leaf, middle, _, traffic, endEv, cond, wb, slots⟩ :=
        current_translate_address_events spec config rows mapping (query a Rn imm12 acc) member dataQ u
          (current_s1_frame current uRegs uMem) (access.of_regs uRegs)
          (by rw [uRegs]; exact mode) (by rw [uRegs]; exact pr.post.aa64el0)
          (by rw [uRegs]; exact debug) (by rw [uRegs]; exact pr.post.spe)
      obtain ⟨_, out, _, _, _, _, _, mapResult, vaddr, normal, addressFault, _, _, registers, _⟩ := fields
      have addressPA : address.paddress.address = pa :=
        BitVec.eq_of_toNat_eq (Option.some.inj (mapResult.symm.trans mapped))
      have otherRegs : other.regs = a.regs := by
        rw [registers, uRegs]; unfold fetchGuardRegs; simp only [query, notFetch, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨walkFlags, leafFlag, otherMem⟩ := cond (by rw [uMem]; exact raw)
        (by rw [uRegs]; exact none acc hA0)
      have otherMem' : other.mem = a.mem := otherMem.trans uMem
      have cachedU : outputCached (query a Rn imm12 acc).request.raw u.regs = true := by
        show outputCached acc u.regs = true
        unfold outputCached; rw [notFetch, uRegs]; exact dcache
      obtain ⟨inner, outer⟩ := wb cachedU
      refine ⟨address, other, call, addressFault, addressPA, normal, inner, outer,
        by rw [otherRegs]; exact pr, ?_, otherRegs, otherMem', ?_⟩
      · intro i hi
        rw [otherMem']; exact bytes i hi
      · refine ⟨info, walk, leaf, middle, address, by rw [← uEvents]; exact traffic, walkFlags, leafFlag, slots,
          vaddr, ?_⟩
        rw [endEv, vaddr]
        rfl)
    mmio
  obtain ⟨t1Regs, t1Mem, loadEvents⟩ := hQ
  simp only [hmr]
  simp only [PreSail.assert, ite_true, pure, EStateM.pure]
  simp only [CryptoMem.MemCore.xset t2 Rt hRt 32 (Or.inl rfl)]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hr2' : t2.regs = a.regs := hr2.trans t1Regs
  have hm2' : t2.mem = a.mem := hm2.trans t1Mem
  have hspe : t2.regs.bank_Bool .SPESampleInFlight = false := by rw [hr2']; exact pr.post.spe
  try simp only [rdB, CryptoMem.MemCore.setGpr, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, Bool.cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  have kind : AccessDescriptor_to_Access_kind acc = .AK_explicit { variety := .AV_plain, strength := .AS_normal } :=
    MemM1.MemReadD2.kind_eq2 acc hAD
  refine ⟨?_, hm2', ?_⟩
  · simp only [post, val, CryptoMem.MemCore.setGpr]
    rw [hr2']
    try rfl
  · rw [hev, kind]; rw [kind] at loadEvents; exact loadEvents

#print axioms run

/-- LDR Wt's value is the zero-extended 4-byte datum. -/
theorem val_eq (d : BitVec (4 * 8)) : val d = d.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [val, Sail.BitVec.zeroExtend, Sail.BitVec.castWidth, BitVec.getLsbD_setWidth]
  all_goals omega

theorem byte_eq (d : BitVec (4 * 8)) (t : Nat) (ht : t < 4) :
    ((d.setWidth 64 >>> (8 * t)).setWidth 8) = d.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi]
  omega

/-- Value-layer effect (ArmCert-only statement): X[Rt] clobbered, NZCV unchanged, MemVHolds [.load32 Rt r j]. -/
theorem value (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List ArmCertValue.Region)
    (a u : NativeState) (Rt : BitVec 5) (data : BitVec (4 * 8))
    (hr : u.regs = (post a Rt data).regs) (hm : u.mem = a.mem) (r : ArmCertValue.Region) (j : Nat)
    (hb : ∀ t, t < 4 → ArmCertValue.regionByte mapping pinv a r (j + t) = some (data.extractLsb' (8 * t) 8)) :
    HeapV2StepCerts.RegBind.Holds [(.x (GPRSummary.key Rt.toNat), .drop)] a u ∧
      HeapV2StepCerts.Flags.nzcv u.regs = HeapV2StepCerts.Flags.nzcv a.regs ∧
      ArmCertValue.MemVHolds mapping pinv regions [.load32 (.x (GPRSummary.key Rt.toNat)) r j] a u := by
  have hg : u.regs.gpr = a.regs.gpr.set (GPRSummary.key Rt.toNat).val (val data) (GPRSummary.key Rt.toNat).isLt := by
    rw [hr]; rfl
  refine ⟨ArmCertR14.Value.holds_drop1 a u _ (val data) hg (by rw [hr]; rfl), by rw [hr]; rfl,
    ArmCertR14.Value.memV_of_mem mapping pinv regions a u _ hm (fun e he => ?_)⟩
  rw [List.mem_singleton] at he; subst he
  refine ⟨fun e he => ?_, fun r h => by simp at h, fun r h => by simp at h⟩
  rw [List.mem_singleton] at he; subst he
  refine ⟨data.setWidth 64, ?_, fun t ht => ?_, ?_⟩
  · simp only [BitVec.toNat_setWidth]; omega
  · rw [hb t ht, byte_eq data t ht]
  · show u.regs.gpr[(GPRSummary.key Rt.toNat).val] = _
    rw [hg, Vector.getElem_set_self, val_eq]

#print axioms value

end MemClass.LdrU32
