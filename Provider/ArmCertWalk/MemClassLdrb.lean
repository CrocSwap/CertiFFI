-- /: MemClass.Ldrb.run — the ACTUAL LDRB (immediate, post-index,
-- size=00 opc=01) decode at an arbitrary state `a`, from the canonical invariant (CurrentS1At +
-- per-descriptor CurrentS1AccessAt), with the no-update route.
-- Mirrors the SDK CruxMem.LdrbEval.decode_ldrb_eval, replacing its TranslationAgreesV3 premise by
-- current_translate_address_events (no premise). Register result = the SDK `ldrbPost`.
import ArmCertWalk.DataAccessEvents
import CruxMem.LdrbEval
import CruxMem.CruxLdrb
import MemM1.MemReadD2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false
namespace MemClass.Ldrb
open ArmCertWalk ArmBridge.Draft ArmCertMem.LdrbEval

/-- The base address X[Rn] (pre-writeback) read by the access. -/
def base (a : NativeState) (Rn : BitVec 5) : BitVec 64 := a.regs.gpr[(GPRSummary.key Rn.toNat).val]

/-- The 1-byte data query for descriptor `acc`. -/
def query (a : NativeState) (Rn : BitVec 5) (acc : AccessDescriptor) : AccessQuery :=
  ⟨base a Rn, ⟨acc, true⟩, ((1 : Nat) : Int)⟩

/-- Actual translation traffic then the 1-byte read, from `before` (decision-171 no-update form). -/
def LoadEvents {domain : QueryDomain} (spec : TopologyImageSpec domain) (va : BitVec 64) (pa : BitVec 56)
    (before : Array Event) (kind : Access_kind arm_acc_type) (after : Array Event) : Prop :=
  ∃ (info : TranslationStartInfo) (walk : List (Nat × Bool × Array Event))
    (leaf : Nat × Bool × Array Event) (middle : Array Event) (address : AddressDescriptor),
    TranslateTrafficFrom (before.push (.translationStart info)) walk leaf middle ∧
    (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧
    ((spec.logicalRows.map (·.logical)).Nodup → walk.map (·.1) = declaredSlots spec.logicalRows spec.layout va) ∧
    address.vaddress = va ∧
    after = (middle.push (.translationEnd address)).push (.memRead pa.toNat 1 (some va.toNat) kind false)

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm9 : BitVec 9) (Rn Rt : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemReadD2.AccDR2 acc →
      domain (query a Rn acc) ∧ ∃ data : S1AccessData spec config rows (query a Rn acc),
        CurrentS1AccessAt spec config rows mapping (query a Rn acc) data a)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (post : MemM1.MemReadD2.PostRegs2 a.regs)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (dcache : currentDCache a.regs = true)
    (pa : BitVec 56) (mapped : mapping (base a Rn) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (v : BitVec 8) (byte : a.mem[pa.toNat]? = some v)
    (outside : ¬ (rowsFootprint spec.imageRows).byte pa.toNat)
    (raw : RawImageAt spec.imageRows a.mem)
    (none : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u, (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2 : SailM Unit) a = .ok () u ∧
      u.regs = (ldrbPost a Rn Rt imm9 v).regs ∧ u.mem = a.mem ∧
      LoadEvents spec (base a Rn) pa a.events (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) u.events := by
  unfold decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  unfold execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have hRnt' : ¬ ((Rn.toNat : Int) = (Rt.toNat : Int)) := by
    intro h; apply hRnt; apply BitVec.eq_of_toNat_eq; omega
  have hRn' : ¬ ((Rn.toNat : Int) = 31) := by omega
  have hb1 : (((Rn.toNat : Int)) == ((Rt.toNat : Int))) = false := by simpa using hRnt'
  have hb2 : (((Rn.toNat : Int)) != 31) = true := by simpa using hRn'
  have htn : Sail.Int.toNatChecked ((Rn.toNat : Nat) : Int) = Rn.toNat := rfl
  have htt : Sail.Int.toNatChecked ((Rt.toNat : Nat) : Int) = Rt.toNat := rfl
  have hR31 : ¬ Rn.toNat = 31 := by omega
  simp (config := {decide := true}) only [undefined_MemOp, undefined_Constraint, PreSail.internal_pick_at,
    PreSail.chooseAt, PreSail.occLabel, PreSail.undefined_bool_at, PreSail.undefined_bitvector_at,
    undefined_bool, undefined_bitvector, modifyGet, hb1, hb2, htn, htt, hR31, Functor.map, EStateM.map, MonadStateOf.modifyGet, EStateM.modifyGet, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind, ite_true, ite_false, dite_true, dite_false,
    hRnt', hRn', Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and, beq_iff_eq, bne_iff_ne, ne_eq,
    reduceIte, reduceDIte, Bool.not_true, Bool.not_false, decide_true, decide_false]
  have rdP : ∀ st : NativeState, (readReg PSTATE : SailM ProcState) st = .ok st.regs.PSTATE st :=
    fun _ => rfl
  have hEL := post.post.el0
  simp (config := {decide := true}) only [rdP, hEL]
  name_call_state CreateAccDescGPR as X1
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr⟩ := MemM1.AccGPR.create X1 ArmFull.MemOp.MemOp_LOAD false true
    (by subst hX1; exact post.post.noRME) (by subst hX1; exact post.post.nrw) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact post.post.ns) (by subst hX1; exact hTME)
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_LOAD false (0#2 != EL0)
      (ArmFull.MemOp.MemOp_LOAD != ArmFull.MemOp.MemOp_PREFETCH && (true || true)) X1 = .ok acc t' := by
    rw [show (0#2 != EL0) = false from rfl,
      show (ArmFull.MemOp.MemOp_LOAD != ArmFull.MemOp.MemOp_PREFETCH && (true || true)) = true from rfl]
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
  have haddr : t'.regs.gpr[(GPRSummary.key Rn.toNat).val] = base a Rn := by
    rw [htr']; rfl
  obtain ⟨member, data, access⟩ := perAcc acc hA0 hAD
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hAD.gpr]; rfl
  -- the actual 1-byte read through the canonical-invariant translation
  obtain ⟨ad, t1, t2, hQ, hmr, hev, hr2, hm2⟩ := MemM1.MemReadD2.memRead2_1
    (t'.regs.gpr[(GPRSummary.key Rn.toNat).val]) acc t' pa v hAD (by rw [htr']; exact post.noMTE2)
    (fun ad t1 => t1.regs = a.regs ∧ t1.mem = a.mem ∧ LoadEvents spec (base a Rn) pa a.events
        (AccessDescriptor_to_Access_kind acc) ((t1.events).push (.memRead pa.toNat 1 (some ad.vaddress.toNat)
          (AccessDescriptor_to_Access_kind acc) false)))
    (by
      intro u fu
      have uRegs : u.regs = a.regs := fu.1.trans htr'
      have uMem : u.mem = a.mem := fu.2.1.trans htm'
      have uEvents : u.events = a.events := fu.2.2.trans hte'
      obtain ⟨address, fault, other, call, fields, _, _, _, _, _, _, _, writes, _,
          info, walk, leaf, middle, _, traffic, endEv, cond, wb, slots⟩ :=
        current_translate_address_events spec config rows mapping (query a Rn acc) member data u
          (current_s1_frame current uRegs uMem) (access.of_regs uRegs)
          (by rw [uRegs]; exact mode) (by rw [uRegs]; exact post.post.aa64el0)
          (by rw [uRegs]; exact debug) (by rw [uRegs]; exact post.post.spe)
      obtain ⟨_, out, _, _, _, _, _, mapResult, vaddr, normal, addressFault, _, _, registers, _⟩ := fields
      have addressPA : address.paddress.address = pa :=
        BitVec.eq_of_toNat_eq (Option.some.inj (mapResult.symm.trans mapped))
      have otherRegs : other.regs = a.regs := by
        rw [registers, uRegs]; unfold fetchGuardRegs; simp only [query, notFetch, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨walkFlags, leafFlag, otherMem⟩ := cond (by rw [uMem]; exact raw)
        (by rw [uRegs]; exact none acc hA0)
      have otherMem' : other.mem = a.mem := otherMem.trans uMem
      have cachedU : outputCached (query a Rn acc).request.raw u.regs = true := by
        show outputCached acc u.regs = true
        unfold outputCached; rw [notFetch, uRegs]; exact dcache
      obtain ⟨inner, outer⟩ := wb cachedU
      refine ⟨address, other, ?_, addressFault, addressPA, normal, inner, outer,
        by rw [otherRegs]; exact post, ?_, otherRegs, otherMem', ?_⟩
      · rw [haddr]; exact call
      · intro i hi
        obtain rfl : i = 0 := by omega
        rw [otherMem', Nat.add_zero, byte]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.extractLsb'_toNat]
      · refine ⟨info, walk, leaf, middle, address, by rw [← uEvents]; exact traffic, walkFlags, leafFlag, slots,
          vaddr, ?_⟩
        rw [endEv, vaddr]
        rfl)
    mmio
  obtain ⟨t1Regs, t1Mem, loadEvents⟩ := hQ
  simp only [hmr]
  simp only [PreSail.assert, ite_true, pure, EStateM.pure]
  simp only [CryptoMem.MemCore.xset t2 Rt hRt 32 (Or.inl rfl), CryptoMem.MemCore.xset _ Rn hRn 64 (Or.inr rfl)]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hr2' : t2.regs = a.regs := hr2.trans t1Regs
  have hm2' : t2.mem = a.mem := hm2.trans t1Mem
  have hspe : t2.regs.bank_Bool .SPESampleInFlight = false := by rw [hr2']; exact post.post.spe
  try simp only [rdB, CryptoMem.MemCore.setGpr, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  have kind : AccessDescriptor_to_Access_kind acc = .AK_explicit { variety := .AV_plain, strength := .AS_normal } :=
    MemM1.MemReadD2.kind_eq2 acc hAD
  refine ⟨?_, hm2', ?_⟩
  · simp only [ldrbPost, CryptoMem.MemCore.setGpr, haddr]
    rw [hr2']
    rfl
  · rw [hev, kind]; rw [kind] at loadEvents; exact loadEvents

#print axioms run

/-- (1)-(5): canonical frames of any state whose registers are `ldrbPost a …`. -/
theorem frames (a u : NativeState) (imm9 : BitVec 9) (Rn Rt : BitVec 5) (v : BitVec 8)
    (hr : u.regs = (ldrbPost a Rn Rt imm9 v).regs) :
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
  · rw [hr]; rfl
  · rw [hr]; rfl

#print axioms frames
end MemClass.Ldrb
