import ArmCertTranslateModel.HostTranslateGuards
import ArmCertTranslateModel.TranslateLoopBinding

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Selected current register equalities come from the actual phase frame.
    No relation between inactive words of two getter invocations is needed. -/
theorem current_host_guard_view_register_fields (before after : Regs)
    (features : after.FeatureImpl = before.FeatureImpl)
    (tcr : after.bank_BitVec_64 .TCR_EL2 = before.bank_BitVec_64 .TCR_EL2) :
    currentHostGuardView after = currentHostGuardView before := by
  simp only [currentHostGuardView, features, tcr]

theorem HostTranslateGuardAt.registers {before after : Regs} {params : S1TTWParams}
    (current : HostTranslateGuardAt before params)
    (features : after.FeatureImpl = before.FeatureImpl)
    (tcr : after.bank_BitVec_64 .TCR_EL2 = before.bank_BitVec_64 .TCR_EL2) :
    HostTranslateGuardAt after params :=
  current.trans (current_host_guard_view_register_fields before after features tcr).symm

theorem normalized_txsz_register_fields (before after : Regs)
    (features : after.FeatureImpl = before.FeatureImpl)
    (tcr : after.bank_BitVec_64 .TCR_EL2 = before.bank_BitVec_64 .TCR_EL2) :
    normalizeTxsz after (_get_TCR_EL2_Type_T0SZ (after.bank_BitVec_64 .TCR_EL2)) =
      normalizeTxsz before (_get_TCR_EL2_Type_T0SZ (before.bank_BitVec_64 .TCR_EL2)) := by
  simp only [normalizeTxsz, currentMaxTxsz, features, tcr]
  rfl

theorem translate_query_checks_register_fields {before after : Regs} {params : S1TTWParams}
    {va : BitVec 64} {acc : AccessDescriptor} (current : TranslateQueryChecks before params va acc)
    (features : after.FeatureImpl = before.FeatureImpl) : TranslateQueryChecks after params va acc := by
  refine ⟨current.va, current.e0pd, ?_, ?_⟩
  · simpa only [sourceTmeFault, features] using current.tme
  · simpa only [sourceVectorFault, features] using current.vector

theorem source_txsz_fault_register_fields (before after : Regs) (params : S1TTWParams)
    (lva : after.FeatureImpl[71] = before.FeatureImpl[71]) :
    sourceTxszFault after params = sourceTxszFault before params := by
  simp only [sourceTxszFault, lva]

/-- The current five image controls use a temporary RAW scalar while the
    static geometry retains the independently checked NORMALIZED scalar. -/
theorem host_image_core_register_fields {before after : Regs} {params : S1TTWParams}
    (current : HostImageParamsAt before
      {params with txsz := _get_TCR_EL2_Type_T0SZ (before.bank_BitVec_64 .TCR_EL2)})
    (features : after.FeatureImpl = before.FeatureImpl)
    (tcr : after.bank_BitVec_64 .TCR_EL2 = before.bank_BitVec_64 .TCR_EL2)
    (tcr2 : after.bank_BitVec_64 .TCR2_EL2 = before.bank_BitVec_64 .TCR2_EL2)
    (scr : after.bank_BitVec_64 .SCR_EL3 = before.bank_BitVec_64 .SCR_EL3)
    (sctlr : after.bank_BitVec_64 .SCTLR_EL2 = before.bank_BitVec_64 .SCTLR_EL2) :
    HostImageParamsAt after
      {params with txsz := _get_TCR_EL2_Type_T0SZ (after.bank_BitVec_64 .TCR_EL2)} := by
  simpa only [tcr] using current.registers features tcr tcr2 scr sctlr

/-- Consume the PAST actual translation's register result. Its hardware
    updates and IFETCH guarded-page bookkeeping preserve the normalized query
    admission needed at the next access, without forcing raw=effective TxSZ. -/
theorem normalized_translate_register_bindings {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (mapping : BitVec 64 → Option Nat) (query : AccessQuery)
    (level : Nat) (view : S1DescriptorPIE.View 64) (before after : State) (next : TTWState)
    (registers : after.regs = fetchGuardRegs query.request.raw next before.regs)
    (current : HostWalkAt config spec.controls spec.physicalConfig before)
    (bound : HostImageParamsAt before.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (before.regs.bank_BitVec_64 .TCR_EL2)})
    (geometry : spec.params.txsz = normalizeTxsz before.regs
      (_get_TCR_EL2_Type_T0SZ (before.regs.bank_BitVec_64 .TCR_EL2)))
    (layout : CurrentLayoutAt spec.layout spec.params query.va before.regs)
    (map : LeafMapAt mapping spec.physicalConfig before.regs query level view)
    (guard : HostTranslateGuardAt before.regs spec.params)
    (checked : TranslateQueryChecks before.regs spec.params query.va query.request.raw)
    (rawFault : sourceTxszFault before.regs
      {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (before.regs.bank_BitVec_64 .TCR_EL2)} = false) :
    HostWalkAt config spec.controls spec.physicalConfig after ∧
      HostImageParamsAt after.regs
        {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (after.regs.bank_BitVec_64 .TCR_EL2)} ∧
      spec.params.txsz = normalizeTxsz after.regs
        (_get_TCR_EL2_Type_T0SZ (after.regs.bank_BitVec_64 .TCR_EL2)) ∧
      CurrentLayoutAt spec.layout spec.params query.va after.regs ∧
      LeafMapAt mapping spec.physicalConfig after.regs query level view ∧
      HostTranslateGuardAt after.regs spec.params ∧
      TranslateQueryChecks after.regs spec.params query.va query.request.raw ∧
      sourceTxszFault after.regs
        {spec.params with txsz := _get_TCR_EL2_Type_T0SZ (after.regs.bank_BitVec_64 .TCR_EL2)} = false := by
  have sameFeatures : after.regs.FeatureImpl = before.regs.FeatureImpl := by
    rw [registers]; unfold fetchGuardRegs; split <;> rfl
  have sameTCR : after.regs.bank_BitVec_64 .TCR_EL2 = before.regs.bank_BitVec_64 .TCR_EL2 := by
    rw [registers]; unfold fetchGuardRegs; split <;> rfl
  have host : HostWalkAt config spec.controls spec.physicalConfig after := by
    have fetch : HostWalkAt config spec.controls spec.physicalConfig (fetchGuardState query.request.raw next before) := by
      unfold fetchGuardState fetchGuardRegs
      split
      · exact host_walk_at_guarded_page current _
      · exact current
    exact host_walk_at_regs_frame fetch registers
  have afterLayout : CurrentLayoutAt spec.layout spec.params query.va after.regs := by
    rw [registers]; unfold fetchGuardRegs
    split
    · exact current_layout_guarded_page layout _
    · exact layout
  have afterMap : LeafMapAt mapping spec.physicalConfig after.regs query level view := by
    rw [registers]; unfold fetchGuardRegs
    split
    · exact map.guarded_page _
    · exact map
  refine ⟨host, host_image_core_register_fields bound sameFeatures sameTCR ?_ ?_ ?_,
    geometry.trans (normalized_txsz_register_fields before.regs after.regs sameFeatures sameTCR).symm,
    afterLayout, afterMap, guard.registers sameFeatures sameTCR, translate_query_checks_register_fields checked sameFeatures, ?_⟩
  all_goals try (rw [registers]; unfold fetchGuardRegs; split <;> rfl)
  simpa only [sourceTxszFault, sameFeatures, sameTCR] using rawFault

#print axioms current_host_guard_view_register_fields
#print axioms HostTranslateGuardAt.registers
#print axioms normalized_txsz_register_fields
#print axioms translate_query_checks_register_fields
#print axioms source_txsz_fault_register_fields
#print axioms host_image_core_register_fields
#print axioms normalized_translate_register_bindings
end ArmCert.Translate.Model
