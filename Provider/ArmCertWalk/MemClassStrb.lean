-- /: MemClass.Strb.run — ACTUAL STRB (immediate, post-index, size=00
-- opc=00) decode at arbitrary `a`, from the canonical invariant + decision-171 no-update route.
-- Mirrors SDK CruxMem.StrbEval.decode_strb_eval with the AgreesV3 premise store (strbV5) replaced by
-- native_data_write_events (DataAccessEvents). Registers = SDK `strbPost`; memory = one byte at pa.
import ArmCertWalk.DataAccessEvents
import CruxMem.StrbEval
import CruxMem.CruxStrb
import MemM1.MemWriteD7
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false
namespace MemClass.Strb
open ArmCertWalk ArmBridge.Draft ArmCertMem.StrbEval

def base (a : NativeState) (Rn : BitVec 5) : BitVec 64 := a.regs.gpr[(GPRSummary.key Rn.toNat).val]

def query (a : NativeState) (Rn : BitVec 5) (acc : AccessDescriptor) : AccessQuery :=
  ⟨base a Rn, ⟨acc, true⟩, ((1 : Nat) : Int)⟩

/-- The stored byte: X[Rt][7:0]. -/
def byteOf (a : NativeState) (Rt : BitVec 5) : BitVec (1 * 8) :=
  BitVec.setWidth (1 * 8) (a.regs.gpr[(GPRSummary.key Rt.toNat).val])

/-- Actual translation traffic then the 1-byte write, from `before` (no-update form). -/
def StoreEvents {domain : QueryDomain} (spec : TopologyImageSpec domain) (va : BitVec 64) (pa : BitVec 56)
    (before : Array Event) (kind : Access_kind arm_acc_type) (value : BitVec (8 * 1)) (after : Array Event) : Prop :=
  ∃ (info : TranslationStartInfo) (walk : List (Nat × Bool × Array Event))
    (leaf : Nat × Bool × Array Event) (middle : Array Event) (address : AddressDescriptor),
    TranslateTrafficFrom (before.push (.translationStart info)) walk leaf middle ∧
    (∀ step ∈ walk, step.2.1 = false) ∧ leaf.2.1 = false ∧
    ((spec.logicalRows.map (·.logical)).Nodup → walk.map (·.1) = declaredSlots spec.logicalRows spec.layout va) ∧
    address.vaddress = va ∧
    after = (middle.push (.translationEnd address)).push (.memWrite pa.toNat 1 (some va.toNat) kind (some value) none)

theorem run {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm9 : BitVec 9) (Rn Rt : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, MemM1.Witness.Acc0 acc → MemM1.MemWriteD5.AccDWT acc →
      domain (query a Rn acc) ∧ (∃ data : S1AccessData spec config rows (query a Rn acc),
        CurrentS1AccessAt spec config rows mapping (query a Rn acc) data a) ∧
      MemM1.MemWriteD6.PreW acc a.regs)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (post : MemM1.MemReadD2.PostRegs2 a.regs)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false)
    (pa : BitVec 56) (mapped : mapping (base a Rn) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (raw : RawImageAt spec.imageRows a.mem)
    (none : ∀ acc, MemM1.Witness.Acc0 acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u, (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 0#2 0#2 : SailM Unit) a = .ok () u ∧
      u.regs = (strbPost a Rn imm9).regs ∧
      u.mem = MemM1.MemWriteD1.wfold a.mem pa.toNat 1
        (fun j => (Sail.BitVec.castWidth (m := 8 * 1) (byteOf a Rt)).extractLsb' (8 * j) 8) ∧
      StoreEvents spec (base a Rn) pa a.events MemM1.MemWriteD4.akPlain
        (Sail.BitVec.castWidth (m := 8 * 1) (byteOf a Rt)) u.events := by
  unfold decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
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
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr⟩ := MemM1.AccGPR.create X1 ArmFull.MemOp.MemOp_STORE false true
    (by subst hX1; exact post.post.noRME) (by subst hX1; exact post.post.nrw) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact post.post.ns) (by subst hX1; exact hTME)
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_STORE false (0#2 != EL0)
      (ArmFull.MemOp.MemOp_STORE != ArmFull.MemOp.MemOp_PREFETCH && (true || true)) X1 = .ok acc t' := by
    rw [show (0#2 != EL0) = false from rfl,
      show (ArmFull.MemOp.MemOp_STORE != ArmFull.MemOp.MemOp_PREFETCH && (true || true)) = true from rfl]
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
  simp only [CryptoMem.Strb.xread8 t' Rt hRt]
  name_call_arg Mem_set 1 as dv
  have haddr : t'.regs.gpr[(GPRSummary.key Rn.toNat).val] = base a Rn := by
    rw [htr']; rfl
  have hdat : dv = byteOf a Rt := by
    rw [← hdv, htr']
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb, BitVec.castWidth, byteOf]
  obtain ⟨member, ⟨data, access⟩, preW⟩ := perAcc acc hA0 hAW
  have notFetch : (acc.acctype == .AccessType_IFETCH) = false := by rw [hAW.base.gpr]; rfl
  obtain ⟨address, translated, final, faultOut, clean, _, _, eventsT, hms, hev, hr2, hm2⟩ :=
    native_data_write_events spec config rows mapping (query a Rn acc) member data t'
      (current_s1_frame current htr' htm') (access.of_regs htr')
      (by rw [htr']; exact mode) (by rw [htr']; exact post.post.aa64el0)
      (by rw [htr']; exact debug) (by rw [htr']; exact post.post.spe)
      1 (Or.inl rfl) hAW (by rw [htr']; exact preW) rfl rfl (Nat.mod_one _) pa mapped mmio dv
  obtain ⟨_, out, _, _, _, _, _, _, vaddr, _, _, _, _, registers, _⟩ := clean
  have tRegs : translated.regs = a.regs := by
    rw [registers, htr']; unfold fetchGuardRegs; simp only [query, notFetch, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨info, walk, leaf, middle, _, traffic, endEv, cond, _, slots⟩ := eventsT
  obtain ⟨walkFlags, leafFlag, tMem⟩ := cond (by rw [htm']; exact raw) (by rw [htr']; exact none acc hA0)
  change Mem_set (base a Rn) 1 acc dv t' = .ok () final at hms
  rw [← haddr] at hms
  simp only [hms]
  try simp only [PreSail.assert, ite_true, pure, EStateM.pure]
  simp only [CryptoMem.MemCore.xset _ Rn hRn 64 (Or.inr rfl)]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hr2' : final.regs = a.regs := hr2.trans tRegs
  have hspe : final.regs.bank_Bool .SPESampleInFlight = false := by rw [hr2']; exact post.post.spe
  try simp only [rdB, CryptoMem.MemCore.setGpr, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, Bool.cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  have kind : AccessDescriptor_to_Access_kind acc = MemM1.MemWriteD4.akPlain := by
    exact MemM1.MemWriteD7.akT acc hAW
  refine ⟨?_, ?_, ?_⟩
  · simp only [strbPost, CryptoMem.MemCore.setGpr, haddr]
    rw [hr2']
    try rfl
  · rw [hm2, tMem, htm', hdat]
  · refine ⟨info, walk, leaf, middle, address, by rw [← hte']; exact traffic, walkFlags, leafFlag, slots, ?_, ?_⟩
    · exact vaddr
    · rw [hev, endEv, hdat]
      simp only [query] at vaddr ⊢
      rw [vaddr, kind]

#print axioms run

/-- (1)-(5) from `u.regs = strbPost a …`. -/
theorem frames (a u : NativeState) (imm9 : BitVec 9) (Rn : BitVec 5) (hr : u.regs = (strbPost a Rn imm9).regs) :
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

/-- certiffi (i)+(ii): the store writes exactly byte `pa`, which is not a table byte. -/
theorem footprint {domain : QueryDomain} (spec : TopologyImageSpec domain) (mem : Mem) (pa : BitVec 56)
    (g : Nat → BitVec 8) (outside : ¬ (rowsFootprint spec.imageRows).byte pa.toNat) :
    WritesOnly (fun x => x = pa.toNat) (fun x => mem[x]?) (fun x => (MemM1.MemWriteD1.wfold mem pa.toNat 1 g)[x]?) ∧
    Separated (rowsFootprint spec.imageRows).byte (fun x => x = pa.toNat) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [MemM1.MemWriteD1.wfold_get]
    have : ¬ (pa.toNat ≤ x ∧ x < pa.toNat + 1) := by omega
    simp [this]
  · intro x table same
    subst same
    exact outside table

#print axioms frames
#print axioms footprint
end MemClass.Strb
