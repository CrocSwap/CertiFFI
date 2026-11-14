import ArmCertTranslateModel.TranslationInvariant

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Consume selected fields of a PAST actual phase frame and its actual
    separated physical writes. The closed native producer derives these facts;
    this is not a public forall-future frame or preservation assumption. -/
theorem current_s1_program_write {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {before after : State}
    (current : CurrentS1At spec config rows before)
    (writes : Nat → Prop)
    (memory : WritesOnly writes (fun a => before.mem[a]?) (fun a => after.mem[a]?))
    (separated : Separated (rowsFootprint spec.imageRows).byte writes)
    (features : after.regs.FeatureImpl = before.regs.FeatureImpl)
    (el : after.regs.PSTATE.EL = before.regs.PSTATE.EL)
    (nrw : after.regs.PSTATE.nRW = before.regs.PSTATE.nRW)
    (tcr : after.regs.bank_BitVec_64 .TCR_EL2 = before.regs.bank_BitVec_64 .TCR_EL2)
    (tcr2 : after.regs.bank_BitVec_64 .TCR2_EL2 = before.regs.bank_BitVec_64 .TCR2_EL2)
    (hcr : after.regs.bank_BitVec_64 .HCR_EL2 = before.regs.bank_BitVec_64 .HCR_EL2)
    (scr : after.regs.bank_BitVec_64 .SCR_EL3 = before.regs.bank_BitVec_64 .SCR_EL3)
    (sctlr : after.regs.bank_BitVec_64 .SCTLR_EL2 = before.regs.bank_BitVec_64 .SCTLR_EL2)
    (mair : after.regs.bank_BitVec_64 .MAIR_EL2 = before.regs.bank_BitVec_64 .MAIR_EL2)
    (pa : after.regs.bank_Int .__supported_pa_size = before.regs.bank_Int .__supported_pa_size)
    (pir : spec.controls.pie = true → after.regs.bank_BitVec_64 .PIR_EL2 = before.regs.bank_BitVec_64 .PIR_EL2)
    (pire0 : spec.controls.pie = true → after.regs.bank_BitVec_64 .PIRE0_EL2 = before.regs.bank_BitVec_64 .PIRE0_EL2)
    (por : e0OverlayEnabled before.regs = true →
      after.regs.bank_BitVec_64 .POR_EL0 = before.regs.bank_BitVec_64 .POR_EL0)
    (cache : after.regs.bank_Bool .__tlb_enabled = before.regs.bank_Bool .__tlb_enabled) :
    CurrentS1At spec config rows after := by
  have overlay := overlay_enables_register_fields before.regs after.regs features tcr2 scr current.host.regime.el3a64
  refine ⟨current.images.program_write writes memory separated overlay.1.symm (fun active => (por active).symm),
    current.host.registers features el nrw tcr tcr2 hcr scr sctlr mair pa pir pire0,
    host_image_core_register_fields current.core features tcr tcr2 scr sctlr,
    current.geometry.trans (normalized_txsz_register_fields before.regs after.regs features tcr).symm,
    current.guards.registers features tcr, ?_, ?_, cache.trans current.cache⟩
  · simpa only [sourceTxszFault, features, tcr] using current.rawFault
  · simpa only [currentTranslationEnabled, sctlr] using current.enabled

/-- A past phase's current control projections transport ANY declared access
    check. BBM implementation fields are needed only for an active block leaf;
    PIR/PIRE0 and POR requirements in the image transport stay conditional. -/
theorem current_s1_access_registers {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {data : S1AccessData spec config rows query} {before after : State}
    (access : CurrentS1AccessAt spec config rows mapping query data before)
    (features : after.regs.FeatureImpl = before.regs.FeatureImpl)
    (tcr : after.regs.bank_BitVec_64 .TCR_EL2 = before.regs.bank_BitVec_64 .TCR_EL2)
    (sctlr : after.regs.bank_BitVec_64 .SCTLR_EL2 = before.regs.bank_BitVec_64 .SCTLR_EL2)
    (ttbr0 : after.regs.bank_BitVec_128 ._TTBR0_EL2 = before.regs.bank_BitVec_128 ._TTBR0_EL2)
    (httbr : after.regs.bank_BitVec_64 .HTTBR = before.regs.bank_BitVec_64 .HTTBR)
    (ttbr1 : after.regs.bank_BitVec_128 .TTBR1_EL2 = before.regs.bank_BitVec_128 .TTBR1_EL2)
    (bbm : data.leafLevel < 3 → before.regs.FeatureImpl[101] = true →
      after.regs.bank_Int .__block_bbm_implemented = before.regs.bank_Int .__block_bbm_implemented) :
    CurrentS1AccessAt spec config rows mapping query data after := by
  refine ⟨current_layout_register_fields access.layout ttbr0 httbr ttbr1,
    translate_query_checks_register_fields access.checks features, ?_,
    access.map.registers (fun _ => by rw [features]) bbm, ?_⟩
  · simpa only [currentWalkEPD, tcr] using access.epd
  · simpa only [OutputCacheAdmissible, currentICache, currentDCache, sctlr] using access.outputPolicy

#print axioms current_s1_program_write
#print axioms current_s1_access_registers
end ArmCert.Translate.Model
