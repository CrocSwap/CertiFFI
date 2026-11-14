-- Heap-v2 byte actions using the actual TCO preparation before translation.
import ArmCertWalk.MemClassLdrb
import ArmCertWalk.MemClassStrb
import HeapV2StepCerts.AccShape
import HeapDefaultTagCheck.Access
import DefaultStoreNoUpdate

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model NativeMteTagCheck NativeMteTagCheck.StatusTrace ReleaseProfile

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false

namespace MemClass.Ldrb
open ArmCertWalk ArmBridge.Draft ArmCertMem.LdrbEval

theorem runDefaultTagCheck {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm9 : BitVec 9) (Rn Rt : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      domain (query a Rn acc) ∧ ∃ data : S1AccessData spec config rows (query a Rn acc),
        CurrentS1AccessAt spec config rows mapping (query a Rn acc) data a)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (post : MemM1.MemReadD.PostRegs a.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue a)
    (statusRows : TagStatusRows a (a.choiceOcc.getD 1354 0) 1)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (dcache : currentDCache a.regs = true)
    (pa : BitVec 56) (mapped : mapping (base a Rn) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (v : BitVec 8) (byte : a.mem[pa.toNat]? = some v)
    (outside : ¬ (rowsFootprint spec.imageRows).byte pa.toNat)
    (raw : RawImageAt spec.imageRows a.mem)
    (none : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u draws, (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2 : SailM Unit) a = .ok () u ∧
      u.regs = (ldrbPost a Rn Rt imm9 v).regs ∧ u.mem = a.mem ∧
      LoadEvents spec (base a Rn) pa a.events (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) u.events ∧ ChoiceDelta a u draws ∧ draws ≤ 1 := by
  rw [exists_comm]
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
  have hEL := post.el0
  simp (config := {decide := true}) only [rdP, hEL]
  name_call_state CreateAccDescGPR as X1
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr, hshape⟩ := HeapV2StepCerts.AccShape.create' X1 ArmFull.MemOp.MemOp_LOAD false true (Or.inl rfl)
    (by subst hX1; exact post.noRME) (by subst hX1; exact post.nrw) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact post.ns) (by subst hX1; exact hTME)
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
  have dX1 : ChoiceDelta a X1 0 := by
    subst hX1
    refine ⟨rfl, ?_⟩
    simp [Std.ExtHashMap.getD_insert]
  have dCtor := DefaultDescriptorChoice.create_gpr_preserves .MemOp_LOAD false false true X1 acc t' hcr
  have dPrefix : ChoiceDelta a t' 0 := choice_delta_trans dX1 dCtor
  have fPrefix : TraceFrame a t' := ⟨htr', htm', hte', dPrefix⟩
  have allowed : TagStatusOK a := HeapDefaultTagCheck.Access.status_at statusRows (choice_delta_refl a) (by decide)
  simp only [CryptoMem.MemCore.xread64 t' Rn hRn]
  reduce_closed_nat
  have haddr : t'.regs.gpr[(GPRSummary.key Rn.toNat).val] = base a Rn := by
    rw [htr']; rfl
  obtain ⟨ad, mid, t2, draws, hmr, traffic, vaddr, hev, hr2', hm2', d2, bound⟩ :=
    HeapDefaultTagCheck.Access.load1 spec config rows mapping a t' fPrefix (base a Rn) acc hAD hshape
      (fun prepared hp => perAcc prepared hp) current mode debug post catalogue controls allowed hshape.el
      dcache pa mapped mmio raw none v (by
        intro i hi
        have iz : i = 0 := by omega
        subst i
        simpa [BitVec.extractLsb'_toNat] using byte)
  rw [← haddr] at hmr
  simp only [hmr]
  simp only [PreSail.assert, ite_true, pure, EStateM.pure]
  simp only [CryptoMem.MemCore.xset t2 Rt hRt 32 (Or.inl rfl), CryptoMem.MemCore.xset _ Rn hRn 64 (Or.inr rfl)]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hspe : t2.regs.bank_Bool .SPESampleInFlight = false := by rw [hr2']; exact post.spe
  try simp only [rdB, CryptoMem.MemCore.setGpr, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  have kind : AccessDescriptor_to_Access_kind acc = .AK_explicit { variety := .AV_plain, strength := .AS_normal } :=
    MemM1.MemReadD2.kind_eq2 acc hAD
  refine ⟨draws, ?_, hm2', ?_, ?_, bound⟩
  · simp only [ldrbPost, CryptoMem.MemCore.setGpr, haddr]
    rw [hr2']
    rfl
  · obtain ⟨info,walk,leaf,middle,traffic,flags,leafFlag,slots,endEv⟩ := traffic
    exact ⟨info,walk,leaf,middle,ad,traffic,flags,leafFlag,slots,vaddr,by rw [hev,endEv,kind]⟩
  · exact d2

#print axioms runDefaultTagCheck
end MemClass.Ldrb

namespace MemClass.Strb
open ArmCertWalk ArmBridge.Draft ArmCertMem.StrbEval

theorem runDefaultTagCheck {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm9 : BitVec 9) (Rn Rt : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRnt : Rn ≠ Rt)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      domain (query a Rn acc) ∧ (∃ data : S1AccessData spec config rows (query a Rn acc),
        CurrentS1AccessAt spec config rows mapping (query a Rn acc) data a))
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (post : MemM1.MemReadD.PostRegs a.regs) (catalogue : ControlCatalogue) (controls : DefaultAt catalogue a)
    (statusRows : TagStatusRows a (a.choiceOcc.getD 1354 0) 1)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (dcache : currentDCache a.regs = true)
    (pa : BitVec 56) (mapped : mapping (base a Rn) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (raw : RawImageAt spec.imageRows a.mem)
    (none : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u draws, (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 0#2 0#2 : SailM Unit) a = .ok () u ∧
      u.regs = (strbPost a Rn imm9).regs ∧
      u.mem = MemM1.MemWriteD1.wfold a.mem pa.toNat 1
        (fun j => (Sail.BitVec.castWidth (m := 8 * 1) (byteOf a Rt)).extractLsb' (8 * j) 8) ∧
      StoreEvents spec (base a Rn) pa a.events MemM1.MemWriteD4.akPlain
        (Sail.BitVec.castWidth (m := 8 * 1) (byteOf a Rt)) u.events ∧ ChoiceDelta a u draws ∧ draws ≤ 1 := by
  rw [exists_comm]
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
  have hEL := post.el0
  simp (config := {decide := true}) only [rdP, hEL]
  name_call_state CreateAccDescGPR as X1
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr, hshape⟩ := HeapV2StepCerts.AccShape.create' X1 ArmFull.MemOp.MemOp_STORE false true (Or.inr rfl)
    (by subst hX1; exact post.noRME) (by subst hX1; exact post.nrw) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact post.ns) (by subst hX1; exact hTME)
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
  have dX1 : ChoiceDelta a X1 0 := by
    subst hX1
    refine ⟨rfl, ?_⟩
    simp [Std.ExtHashMap.getD_insert]
  have dCtor := DefaultDescriptorChoice.create_gpr_preserves .MemOp_STORE false false true X1 acc t' hcr
  have dPrefix : ChoiceDelta a t' 0 := choice_delta_trans dX1 dCtor
  have fPrefix : TraceFrame a t' := ⟨htr', htm', hte', dPrefix⟩
  have allowed : TagStatusOK a := HeapDefaultTagCheck.Access.status_at statusRows (choice_delta_refl a) (by decide)
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
  obtain ⟨address,middle,final,draws,hms,traffic,vaddr,hev,hr2',hm2,d2,bound⟩ :=
    DefaultStoreNoUpdate.natural spec config rows mapping a t' fPrefix
      (base a Rn) 1 (Or.inl rfl) (Nat.mod_one _) acc hAW hshape hshape.el
      catalogue controls allowed dv (fun prepared hp => perAcc prepared hp)
      current mode post debug dcache pa mapped raw none mmio
  rw [← haddr] at hms
  simp only [hms]
  try simp only [PreSail.assert, ite_true, pure, EStateM.pure]
  simp only [CryptoMem.MemCore.xset _ Rn hRn 64 (Or.inr rfl)]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hspe : final.regs.bank_Bool .SPESampleInFlight = false := by rw [hr2']; exact post.spe
  try simp only [rdB, CryptoMem.MemCore.setGpr, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, Bool.cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  have kind : AccessDescriptor_to_Access_kind acc = MemM1.MemWriteD4.akPlain := by
    exact MemM1.MemWriteD7.akT acc hAW
  refine ⟨draws, ?_, ?_, ?_, ?_, bound⟩
  · simp only [strbPost, CryptoMem.MemCore.setGpr, haddr]
    rw [hr2']
    try rfl
  · rw [hm2, hdat]
  · obtain ⟨info, walk, leaf, mid, traffic, walkFlags, leafFlag, slots, endEv⟩ := traffic
    exact ⟨info, walk, leaf, mid, address, traffic, walkFlags, leafFlag, slots, vaddr,
      by rw [hev, endEv, hdat, kind]⟩
  · exact d2

#print axioms runDefaultTagCheck
end MemClass.Strb
