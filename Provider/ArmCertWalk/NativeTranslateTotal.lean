import ArmCertWalk.TranslateNormalizedEntry
import ArmCertWalk.NativeTranslateTail

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

def CleanTranslateResult {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (leafLevel : Nat) (view : S1DescriptorPIE.View 64)
    (initial : State) (result : FaultRecord × AddressDescriptor) (other : State) : Prop :=
  ∃ (params : S1TTWParams) (out : TranslateVars) (operations : List TableUpdate),
    ImageParamsEq spec.params params ∧ result.1 = translateFault out ∧
    result.1.statuscode = .Fault_None ∧ mapping query.va = some result.2.paddress.address.toNat ∧
    result.2.vaddress = query.va ∧ result.2.memattrs.memtype = .MemType_Normal ∧
    result.2.paddress = S1LogicalReference.outputAddress query.va leafLevel
      (translateCurrent out).baseaddress ((translateCurrent out).contiguous == 1#1) ∧
    other.regs = fetchGuardRegs query.request.raw (translateCurrent out) initial.regs ∧
    StoreHistory params (rowsFootprint spec.imageRows) initial.mem operations other.mem ∧
    CurrentImagesAt {spec with params := params} config rows other ∧
    HeldTranslateLeaf config spec.controls params (outputOverlayEnabled initial.regs) leafLevel view out

/-- Complete actual S1Translate, from current host/image/query data through the
actual wrapper, exact TxSZ clamp and source guards to the actual walk/update/
output tail. No future success equation or whole-parameter equality is an input. -/
theorem native_translate_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query) (aligned : Bool)
    (leafLevel logical : Nat) (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (path : S1LogicalReference.Path (logicalObserve spec.logicalRows)
      (effectiveBits spec.physicalConfig).toNat query.va spec.layout.start
      (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root
      (.leaf leafLevel logical physical view))
    (binding : PathPermissionUse spec config rows query path ⟨0#2, false, false⟩)
    (fault : FaultRecord) (initial : State)
    (lower : AArch64_GetVARange query.va = .VARange_LOWER)
    (current : HostWalkAt config spec.controls spec.physicalConfig initial)
    (bound : HostImageParamsAt initial.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (initial.regs.bank_BitVec_64 .TCR_EL2)})
    (geometry : spec.params.txsz = normalizeTxsz initial.regs
      (_get_TCR_EL2_Type_T0SZ (initial.regs.bank_BitVec_64 .TCR_EL2)))
    (layout : CurrentLayoutAt spec.layout spec.params query.va initial.regs)
    (images : CurrentImagesAt spec config rows initial)
    (guard : HostTranslateGuardAt initial.regs spec.params)
    (checked : TranslateQueryChecks initial.regs spec.params query.va query.request.raw)
    (rawFault : sourceTxszFault initial.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (initial.regs.bank_BitVec_64 .TCR_EL2)} = false)
    (enabled : currentTranslationEnabled initial.regs = true)
    (accessEL : query.request.raw.el = EL0) (ss : query.request.raw.ss = .SS_NonSecure)
    (noFault : fault.statuscode = .Fault_None)
    (cache : initial.regs.bank_Bool .__tlb_enabled = false)
    (epd : currentWalkEPD initial.regs query.va = 0#1)
    (map : LeafMapAt mapping spec.physicalConfig initial.regs query leafLevel view)
    (outputPolicy : OutputCacheAdmissible query.request.raw initial.regs) :
    ∃ result other,
      AArch64_S1Translate fault .Regime_EL20 query.va aligned query.request.raw initial = .ok result other ∧
      CleanTranslateResult spec config rows mapping query leafLevel view initial result other := by
  rw [S1WalkSource.translate.equation, TranslateTailSource.equation]
  unfold TranslateTailSource.withTail
  apply S1EntryWP.run_wp
  apply S1EntryWP.bind_normal_me _ _ initial _ _ (prefix_access_draw 1608)
  intro oldAccess t1 hf1
  apply S1EntryWP.bind_normal_me _ _ t1 _ _ (S1EntryDraws.bool_draw 1609)
  intro a64 t2 hf2
  apply S1EntryWP.bind_normal_me _ _ t2 _ _ (S1EntryDraws.bool_draw 1610)
  intro s2 t3 hf3
  apply S1EntryWP.bind_normal_me _ _ t3 _ _ (prefix_tlbline_draw 1611)
  intro tlb t4 hf4
  have hf14 := S1EntryWP.frame_trans (S1EntryWP.frame_trans (S1EntryWP.frame_trans hf1 hf2) hf3) hf4
  have enabledCall : AArch64_S1Enabled .Regime_EL20 query.request.raw.acctype t4 = .ok true t4 := by
    rw [s1_enabled_el20_eq, hf14.1, enabled]
  apply S1EntryWP.bind_lift_eq _ _ t4 t4 true _ _ enabledCall
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨raw, t5, getterCall, getterFrame, active, actualImages, format, callees, actualLayout, disch,
    rawNoFault, checks⟩ := translate_normalized_entry_total spec config rows query t4 lower
      (host_walk_frame config spec.controls spec.physicalConfig initial t4 current hf14.1)
      (by simpa only [hf14.1] using bound) (by simpa only [hf14.1] using geometry)
      (layout.of_regs hf14.1) (images.frame hf14.1 hf14.2.1)
      (by simpa only [hf14.1] using guard) (by simpa only [hf14.1] using checked)
      (by simpa only [hf14.1] using rawFault)
  rw [ss]
  apply S1EntryWP.bind_lift_eq _ _ t4 t5 raw _ _ getterCall
  have hf15 := S1EntryWP.frame_trans hf14 getterFrame
  have rawD128 : raw.d128 = 0#1 := by
    simpa only [normalize_walk_params_record] using format.d128
  have rawDS : raw.ds = 0#1 := by
    simpa only [normalize_walk_params_record] using format.ds
  have rawTG : raw.tgx = .TGx_4KB := by
    simpa only [normalize_walk_params_record] using format.tg
  apply S1EntryWP.bind_lift_eq _ _ t5 t5 16 _ _ (min_txsz_eq raw t5 rawD128 rawDS rawTG)
  have maxCall : AArch64_MaxTxSZ raw.tgx t5 = .ok (currentMaxTxsz t5.regs) t5 := by
    rw [rawTG]; exact max_txsz_eq t5
  apply S1EntryWP.bind_lift_eq _ _ t5 t5 (currentMaxTxsz t5.regs) _ _ maxCall
  have faultCall : AArch64_S1TxSZFaults .Regime_EL20 raw t5 = .ok false t5 := by
    rw [txsz_fault_eq raw t5 rawD128 rawDS rawTG, rawNoFault]
  apply S1EntryWP.bind_lift_eq _ _ t5 t5 false _ _ faultCall
  simp only [Bool.false_eq_true, ↓reduceIte]
  have effectiveRegs : normalizeWalkParams t4.regs raw = normalizeWalkParams t5.regs raw := by
    rw [getterFrame.1]
  rw [effectiveRegs] at active actualImages format callees actualLayout disch checks
  have clampEq : (if (((raw.txsz.toNat : Int) <b 16) : Bool) then
      {raw with txsz := integer_subrange 16 5 0}
    else if (((raw.txsz.toNat : Int) >b currentMaxTxsz t5.regs) : Bool) then
      {raw with txsz := integer_subrange (currentMaxTxsz t5.regs) 5 0}
    else raw) = normalizeWalkParams t5.regs raw := by
      simp only [normalizeWalkParams, decide_eq_true_eq]
  rw [clampEq]
  simp only [checks.va, Bool.false_eq_true, ↓reduceIte]
  have e0pdCheck := checks.e0pd
  unfold sourceE0PDFault at e0pdCheck
  simp only [e0pdCheck, Bool.false_eq_true, ↓reduceIte]
  apply S1EntryWP.bind_wp
  refine ⟨.ok false, t5, ?_, ?_⟩
  · exact (source_tme_guard_eq _ _ t5).trans (by rw [checks.tme])
  simp only [S1EntryWP.Post, Bool.false_eq_true, ↓reduceIte]
  apply S1EntryWP.bind_wp
  refine ⟨.ok false, t5, ?_, ?_⟩
  · exact (source_vector_guard_eq _ _ t5).trans (by rw [checks.vector])
  simp only [S1EntryWP.Post, Bool.false_eq_true, ↓reduceIte]
  apply S1EntryWP.bind_normal_me _ _ t5 _ _ (S1EntryDraws.address_draw 1612)
  intro oldSlot t6 hf6
  apply S1EntryWP.bind_normal_me _ _ t6 _ _ (prefix_walk_draw 1613)
  intro oldNext t7 hf7
  apply S1EntryWP.bind_normal_me _ _ t7 _ _ (prefix_bits128_draw 1614)
  intro oldDescriptor t8 hf8
  apply S1EntryWP.bind_normal_me _ _ t8 _ _ (prefix_bits128_draw 1615)
  intro oldNew t9 hf9
  apply S1EntryWP.bind_normal_me _ _ t9 _ _ (prefix_bits128_draw 1616)
  intro oldMemory t10 hf10
  have hf510 := S1EntryWP.frame_trans (S1EntryWP.frame_trans (S1EntryWP.frame_trans
    (S1EntryWP.frame_trans hf6 hf7) hf8) hf9) hf10
  have hf110 := S1EntryWP.frame_trans hf15 hf510
  let params := normalizeWalkParams t5.regs raw
  obtain ⟨address, out, other, operations, tailCall, stop, faultNone, level, slotPA, slotVA,
    normal, mapResult, registers, history, imagesAfter, held, addressPA, addressVA, addressNormal,
    context, assured, mecid⟩ := native_translate_tail_total {spec with params := params} config rows mapping
      query member aligned leafLevel logical physical view path
      (binding.reparam_active params active.ha active.hd active.pie active.mtx)
      oldAccess oldSlot oldDescriptor {fault with secondstage := false, s2fs1walk := false}
      oldMemory oldNew a64 s2 oldNext t10 format (callees.of_regs hf510.1)
      (actualImages.frame hf510.1 hf510.2.1) (actualLayout.of_regs hf510.1) disch accessEL ss noFault
      (by rw [hf110.1]; exact cache) (by rw [hf110.1]; exact epd)
      (by rw [hf110.1]; exact map) (by rw [hf110.1]; exact outputPolicy)
  apply S1EntryWP.of_run _ t10 other _ _ tailCall
  refine ⟨params, out, operations, active, rfl, faultNone, ?_, addressVA, addressNormal, addressPA,
    registers.trans (congrArg (fetchGuardRegs query.request.raw (translateCurrent out)) hf110.1), ?_, imagesAfter, ?_⟩
  · rw [addressPA]; exact mapResult
  · simpa only [hf110.2.1] using history
  · simpa only [hf110.1] using held

#print axioms native_translate_total
end ArmCertWalk
