-- Actual unsigned runtime data loads. Each access query uses the descriptor
-- Sail returns from the real MTE2-on preparation path.
import ArmCertR14.MemClassLdrU64
import ArmCertR14.MemClassLdrU64Sp
import ArmCertR14.MemClassLdrbU
import DefaultSPChoice
import DefaultNaturalReadTrace
import DefaultNaturalReadTrace

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option linter.unusedSimpArgs false

namespace ReleaseProfile.DefaultLdrU64Sp
open ArmCertWalk ArmBridge.Draft MemClass.LdrU64Sp NativeMte2

#check "CURRENT_DECL LdrU64Sp.runD"
theorem runD {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm12 : BitVec 12) (Rt : BitVec 5)
    (hRt : Rt.toNat < 31)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      domain (query a imm12 acc) ∧ ∃ data : S1AccessData spec config rows (query a imm12 acc),
        CurrentS1AccessAt spec config rows mapping (query a imm12 acc) data a)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (pr : MemM1.MemReadD.PostRegs a.regs) (catalogue : NativeMteTagCheck.ControlCatalogue) (controls : NativeMteTagCheck.DefaultAt catalogue a)
    (allowed : NativeMteTagCheck.TagStatusOK a)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (dcache : currentDCache a.regs = true)
    (hsp : a.regs.SP_EL0.toNat % 16 = 0) (halign : (addr a imm12).toNat % 8 = 0)
    (pa : BitVec 56) (mapped : mapping (addr a imm12) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (data : BitVec (8 * 8)) (bytes : ∀ i < 8, a.mem[pa.toNat + i]? = some (data.extractLsb' (8 * i) 8))
    (raw : RawImageAt spec.imageRows a.mem)
    (none : ∀ acc, ArmCert.Translate.Model.DataShape false acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u, (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 1#2 3#2 : SailM Unit) a = .ok () u ∧
      u.regs = (post a Rt data).regs ∧ u.mem = a.mem ∧
      LoadEvents spec (addr a imm12) pa 8 a.events (.AK_explicit { variety := .AV_plain, strength := .AS_normal }) u.events ∧
      ∃ draws, NativeMteTagCheck.ChoiceDelta a u draws ∧ draws ≤ 1 := by
  unfold decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned
  unfold execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have htt : Sail.Int.toNatChecked ((Rt.toNat : Nat) : Int) = Rt.toNat := rfl
  simp (config := {decide := true}) only [undefined_MemOp, undefined_Constraint, PreSail.internal_pick_at,
    PreSail.chooseAt, PreSail.choose, PreSail.occLabel, PreSail.undefined_bool_at, PreSail.undefined_bitvector_at,
    undefined_bool, undefined_bitvector, modifyGet, htt, Functor.map, EStateM.map, MonadStateOf.modifyGet, EStateM.modifyGet, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind, ite_true, ite_false, dite_true, dite_false,
    Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and, beq_iff_eq, bne_iff_ne, ne_eq,
    reduceIte, reduceDIte, Bool.not_true, Bool.not_false, decide_true, decide_false]
  have rdP : ∀ st : NativeState, (readReg PSTATE : SailM ProcState) st = .ok st.regs.PSTATE st :=
    fun _ => rfl
  have hEL := pr.el0
  simp (config := {decide := true}) only [rdP, hEL]
  name_call_state CreateAccDescGPR as X1
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr, hshape⟩ := HeapV2StepCerts.AccShape.create' X1 ArmFull.MemOp.MemOp_LOAD false false (Or.inl rfl)
    (by subst hX1; exact pr.noRME) (by subst hX1; exact pr.nrw) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact pr.ns) (by subst hX1; exact hTME)
  have hcr2 : CreateAccDescGPR ArmFull.MemOp.MemOp_LOAD false (0#2 != EL0)
      (ArmFull.MemOp.MemOp_LOAD != ArmFull.MemOp.MemOp_PREFETCH && (false || ((((31#5 : BitVec 5).toNat : Nat) : Int) != 31))) X1 = .ok acc t' := by
    rw [show (0#2 != EL0) = false from rfl,
      show (ArmFull.MemOp.MemOp_LOAD != ArmFull.MemOp.MemOp_PREFETCH && (false || ((((31#5 : BitVec 5).toNat : Nat) : Int) != 31))) = false from rfl]
    exact hcr
  simp only [hcr2]
  have hfr' := hfr
  simp only [S1Normality.Frame] at hfr'
  obtain ⟨htr, htm, hte⟩ := hfr'
  have hX1r : X1.regs = a.regs := by subst hX1; rfl
  have hX1m : X1.mem = a.mem := by subst hX1; rfl
  have hX1e : X1.events = a.events := by subst hX1; rfl
  have initialDelta : NativeMteTagCheck.ChoiceDelta a X1 0 := by
    subst hX1
    exact ⟨rfl, by simp [Std.ExtHashMap.getD_insert]⟩
  have ctorDelta : NativeMteTagCheck.ChoiceDelta a t' 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans initialDelta
      (DefaultDescriptorChoice.create_gpr_preserves .MemOp_LOAD false false false X1 acc t' hcr)
  have htr' : t'.regs = a.regs := htr.trans hX1r
  have htm' : t'.mem = a.mem := htm.trans hX1m
  have hte' : t'.events = a.events := hte.trans hX1e
  have hspt : t'.regs.SP_EL0.toNat % 16 = 0 := by rw [htr']; exact hsp
  obtain ⟨t3, hcs, hf3⟩ := CryptoMem.PairNative.cspa_ok t' (by rw [htr']; exact pr.el0) (by rw [htr']; exact pr.nrw) (by rw [htr']; exact pr.noRME) (by rw [htr']; exact pr.vhe) (by rw [htr']; exact pr.aa64el0) (by rw [htr']; exact pr.ns)
    (by rw [htr']; exact pr.e2h) (by rw [htr']; exact pr.tge) hspt
  simp only [hcs]
  obtain ⟨h3r, h3m, h3e⟩ := hf3
  have hEL3 : t3.regs.PSTATE.EL = 0#2 := by rw [h3r, htr']; exact pr.el0
  simp only [CryptoMem.PairNative.spread t3 hEL3]
  have htr3 : t3.regs = a.regs := h3r.trans htr'
  have htm3 : t3.mem = a.mem := h3m.trans htm'
  have hte3 : t3.events = a.events := h3e.trans hte'
  have prefixDelta : NativeMteTagCheck.ChoiceDelta a t3 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans ctorDelta
      (DefaultDescriptorChoice.sp_alignment_preserves t' () t3 hcs)
  reduce_closed_nat
  name_call_arg Mem_read 3 as ad0
  have haddrA : ad0 = addr a imm12 := by
    rw [← had0, htr3]
    first | rfl | (simp [Sail.BitVec.zeroExtend, addr]) | (congr 1)
  rw [haddrA]
  obtain ⟨ad, t1, t2, draws, hQ, hmr, hev, hr2, hm2, callDelta, drawBound⟩ :=
    ReleaseProfile.DefaultNaturalReads.memRead8_trace
    (addr a imm12) halign acc t3 pa data hAD catalogue (controls.transport ⟨htr3, htm3, hte3⟩) hshape.el
    (fun ad t1 => t1.regs = a.regs ∧ t1.mem = a.mem ∧ LoadEvents spec (addr a imm12) pa 8 a.events
        (AccessDescriptor_to_Access_kind acc) ((t1.events).push (.memRead pa.toNat 8 (some ad.vaddress.toNat)
          (AccessDescriptor_to_Access_kind acc) false)))
    (by
      intro prepared u preparedEq fu
      have hclear : DataShape false prepared := by
        rw [preparedEq]
        exact ⟨hshape.acctype,hshape.el,hshape.ss,hshape.read,hshape.write,hshape.tagaccess,
          hshape.transactional,hshape.nonfault,hshape.contiguous,hshape.firstfault,hshape.first,hshape.ls64⟩
      obtain ⟨member, dataQ, access⟩ := perAcc prepared hclear
      have notFetch : (prepared.acctype == .AccessType_IFETCH) = false := by
        rw [preparedEq]
        change (acc.acctype == .AccessType_IFETCH) = false
        rw [hAD.gpr]; rfl
      have uRegs : u.regs = a.regs := fu.1.trans htr3
      have uMem : u.mem = a.mem := fu.2.1.trans htm3
      have uEvents : u.events = a.events := fu.2.2.1.trans hte3
      obtain ⟨address, fault, other, call, fields, _, _, _, _, _, _, _, writes, _,
          info, walk, leaf, middle, _, traffic, endEv, cond, wb, slots⟩ :=
        current_translate_address_events spec config rows mapping (query a imm12 prepared) member dataQ u
          (current_s1_frame current uRegs uMem) (access.of_regs uRegs)
          (by rw [uRegs]; exact mode) (by rw [uRegs]; exact pr.aa64el0)
          (by rw [uRegs]; exact debug) (by rw [uRegs]; exact pr.spe)
      obtain ⟨_, out, _, _, _, _, _, mapResult, vaddr, normal, addressFault, _, _, registers, _⟩ := fields
      have addressPA : address.paddress.address = pa :=
        BitVec.eq_of_toNat_eq (Option.some.inj (mapResult.symm.trans mapped))
      have otherRegs : other.regs = a.regs := by
        rw [registers, uRegs]; unfold fetchGuardRegs; simp only [query, notFetch, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨walkFlags, leafFlag, otherMem⟩ := cond (by rw [uMem]; exact raw)
        (by rw [uRegs]; exact none prepared hclear)
      have otherMem' : other.mem = a.mem := otherMem.trans uMem
      have cachedU : outputCached (query a imm12 prepared).request.raw u.regs = true := by
        show outputCached prepared u.regs = true
        unfold outputCached; rw [notFetch, uRegs]; exact dcache
      obtain ⟨inner, outer⟩ := wb cachedU
      have walkDelta := TagCheckFrames.translation_preserves _ prepared true _ u address other call
      have otherDelta : NativeMteTagCheck.ChoiceDelta a other 0 := by
        simpa only [Nat.zero_add, Nat.add_zero] using NativeMteTagCheck.choice_delta_trans
          prefixDelta (NativeMteTagCheck.choice_delta_trans fu.2.2.2 walkDelta)
      have defaultNext : NativeMteTagCheck.DefaultAt catalogue other := by
        rcases controls with ⟨⟨el,nrw,aa64,rme,vhe,ns,e2h,tge⟩,mte2,tco,tcf0,preparation⟩
        refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
        all_goals (try unfold NativeMteTagCheck.PreparationAt) <;> rw [otherRegs] <;> assumption
      have statusNext := NativeMteTagCheck.tag_status_transport otherDelta allowed
      refine ⟨address, other, call, addressFault, addressPA, normal, inner, outer,
        by rw [otherRegs]; exact pr, defaultNext, ?_, ?_, otherRegs, otherMem', ?_⟩
      · intro value after run
        cases run
        exact statusNext
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
  simp only [CryptoMem.MemCore.xset t2 Rt hRt 64 (Or.inr rfl)]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hr2' : t2.regs = a.regs := hr2.trans t1Regs
  have hm2' : t2.mem = a.mem := hm2.trans t1Mem
  have hspe : t2.regs.bank_Bool .SPESampleInFlight = false := by rw [hr2']; exact pr.spe
  try simp only [rdB, CryptoMem.MemCore.setGpr, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, Bool.cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  have kind : AccessDescriptor_to_Access_kind acc = .AK_explicit { variety := .AV_plain, strength := .AS_normal } :=
    MemM1.MemReadD2.kind_eq2 acc hAD
  have totalDelta : NativeMteTagCheck.ChoiceDelta a t2 draws := by
    simpa only [Nat.zero_add] using NativeMteTagCheck.choice_delta_trans prefixDelta callDelta
  refine ⟨?_, hm2', ?_, draws, totalDelta, drawBound⟩
  · simp only [post, val, CryptoMem.MemCore.setGpr]
    rw [hr2']
    try rfl
  · rw [hev, kind]; rw [kind] at loadEvents; exact loadEvents

#print axioms runD
end ReleaseProfile.DefaultLdrU64Sp
