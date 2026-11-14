-- Actual runtime unsigned stores using the MTE2-on preparation path.
import ArmCertR14.MemClassStrU64
import ArmCertR14.MemClassStrU64Sp
import ArmCertR14.MemClassStrU32
import ArmCertR14.MemClassStrbU
import DefaultSPChoice
import DefaultStoreNoUpdate

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option linter.unusedSimpArgs false

namespace ReleaseProfile.DefaultStrU32
open ArmCertWalk ArmBridge.Draft MemClass.StrU32 NativeMte2

#check "CURRENT_DECL StrU32.runD"
theorem runD {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (a : NativeState) (imm12 : BitVec 12) (Rn Rt : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (current : CurrentS1At spec config rows a)
    (perAcc : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      domain (query a Rn imm12 acc) ∧ ∃ data : S1AccessData spec config rows (query a Rn imm12 acc),
        CurrentS1AccessAt spec config rows mapping (query a Rn imm12 acc) data a)
    (mode : HostEL0ModeAt a.regs) (debug : ExistingE11DebugAt a.regs)
    (pr : MemM1.MemReadD.PostRegs a.regs) (catalogue : NativeMteTagCheck.ControlCatalogue) (controls : NativeMteTagCheck.DefaultAt catalogue a)
    (allowed : NativeMteTagCheck.TagStatusOK a)
    (hEL3A64 : a.regs.FeatureImpl[7] = true) (hNoEL3A32 : a.regs.FeatureImpl[3] = false)
    (hTME : a.regs.FeatureImpl[227] = false) (dcache : currentDCache a.regs = true)
    (halign : (addr a Rn imm12).toNat % 4 = 0)
    (pa : BitVec 56) (mapped : mapping (addr a Rn imm12) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (raw : RawImageAt spec.imageRows a.mem)
    (none : ∀ acc, ArmCert.Translate.Model.DataShape true acc →
      NoUpdateRows {spec.params with haft := hostHAFT a.regs} acc spec.imageRows = true) :
    ∃ u, (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 2#2 : SailM Unit) a = .ok () u ∧
      u.regs = a.regs ∧
      u.mem = MemM1.MemWriteD1.wfold a.mem pa.toNat 4
        (fun j => (Sail.BitVec.castWidth (m := 8 * 4) (stData a Rt)).extractLsb' (8 * j) 8) ∧
      StoreEvents spec (addr a Rn imm12) pa 4 a.events MemM1.MemWriteD4.akPlain
        (Sail.BitVec.castWidth (m := 8 * 4) (stData a Rt)) u.events ∧ ∃ draws, NativeMteTagCheck.ChoiceDelta a u draws ∧ draws ≤ 1 := by
  unfold decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned
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
  have hEL := pr.el0
  simp (config := {decide := true}) only [rdP, hEL]
  name_call_state CreateAccDescGPR as X1
  obtain ⟨acc, t', hcr, hA0, hAD, hAW, hrd, hwr, htc, hfr, hshape⟩ := HeapV2StepCerts.AccShape.create' X1 ArmFull.MemOp.MemOp_STORE false true (Or.inr rfl)
    (by subst hX1; exact pr.noRME) (by subst hX1; exact pr.nrw) (by subst hX1; exact hEL3A64)
    (by subst hX1; exact hNoEL3A32) (by subst hX1; exact hEL) (by subst hX1; exact pr.ns) (by subst hX1; exact hTME)
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
  have initialDelta : NativeMteTagCheck.ChoiceDelta a X1 0 := by
    subst hX1
    exact ⟨rfl, by simp [Std.ExtHashMap.getD_insert]⟩
  have prefixDelta : NativeMteTagCheck.ChoiceDelta a t' 0 := by
    simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans initialDelta
      (DefaultDescriptorChoice.create_gpr_preserves .MemOp_STORE false false true X1 acc t' hcr)
  have htr' : t'.regs = a.regs := htr.trans hX1r
  have htm' : t'.mem = a.mem := htm.trans hX1m
  have hte' : t'.events = a.events := hte.trans hX1e
  simp only [CryptoMem.MemCore.xread64 t' Rn hRn]
  reduce_closed_nat
  simp only [ArmCertR14.XRead.xread32 t' Rt hRt]
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
  obtain ⟨address, eventMid, final, draws, hms, traffic, vaddr, hev, hr2', hm2, delta, drawBound⟩ :=
    ReleaseProfile.DefaultStoreNoUpdate.natural spec config rows mapping a t' ⟨htr', htm', hte', prefixDelta⟩
      (addr a Rn imm12) 4 (by simp [MemM1.MemWriteD1.SizeOK]) halign acc hAW hshape hshape.el catalogue controls allowed dv
      perAcc current mode pr debug dcache pa mapped raw none mmio
  simp only [hms]
  try simp only [PreSail.assert, ite_true, pure, EStateM.pure]
  have rdB : ∀ st : NativeState, (readReg SPESampleInFlight : SailM Bool) st =
      .ok (st.regs.bank_Bool .SPESampleInFlight) st := fun _ => rfl
  have hspe : final.regs.bank_Bool .SPESampleInFlight = false := by rw [hr2']; exact pr.spe
  try simp only [rdB, CryptoMem.MemCore.setGpr, hspe, Bool.false_eq_true, ite_false,
    EStateM.pure, Bool.not_false, Bool.cond_true, ite_true, EStateM.bind, EStateM.Result.ok.injEq, true_and,
    exists_eq_left']
  have kind : AccessDescriptor_to_Access_kind acc = MemM1.MemWriteD4.akPlain := by
    exact MemM1.MemWriteD7.akT acc hAW
  refine ⟨hr2', by rw [hm2, hdat], ?_, draws, delta, drawBound⟩
  obtain ⟨info, walk, leaf, middle, walks, walkFlags, leafFlag, slots, endEv⟩ := traffic
  refine ⟨info, walk, leaf, middle, address, walks, walkFlags, leafFlag, slots, vaddr, ?_⟩
  rw [hev, endEv, hdat, kind]

#print axioms runD
end ReleaseProfile.DefaultStrU32
