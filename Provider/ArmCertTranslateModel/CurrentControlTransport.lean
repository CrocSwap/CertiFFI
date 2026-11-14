import ArmCertTranslateModel.HostWalkInputs

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Actual phase frames supply these selected CURRENT field equalities.
    This module introduces no global frame predicate or future-frame premise. -/
theorem overlay_enables_register_fields (before after : Regs)
    (features : after.FeatureImpl = before.FeatureImpl)
    (tcr2 : after.bank_BitVec_64 .TCR2_EL2 = before.bank_BitVec_64 .TCR2_EL2)
    (scr : after.bank_BitVec_64 .SCR_EL3 = before.bank_BitVec_64 .SCR_EL3)
    (el3 : before.FeatureImpl[7] = true) :
    e0OverlayEnabled after = e0OverlayEnabled before ∧
    outputOverlayEnabled after = outputOverlayEnabled before := by
  simp [e0OverlayEnabled, outputOverlayEnabled, privilegedOverlayEnabled,
    permissionTCR2Enabled, permissionSCR, features, tcr2, scr, el3]

theorem host_pie_register_fields (before after : Regs)
    (features : after.FeatureImpl = before.FeatureImpl)
    (tcr2 : after.bank_BitVec_64 .TCR2_EL2 = before.bank_BitVec_64 .TCR2_EL2)
    (scr : after.bank_BitVec_64 .SCR_EL3 = before.bank_BitVec_64 .SCR_EL3) :
    hostPIE after = hostPIE before := by
  have gate : hostTCR2Enabled after = hostTCR2Enabled before := by
    simp only [hostTCR2Enabled, features, scr]
  unfold hostPIE
  rw [features, gate, tcr2]

theorem host_haft_register_fields (before after : Regs)
    (features : after.FeatureImpl = before.FeatureImpl)
    (tcr : after.bank_BitVec_64 .TCR_EL2 = before.bank_BitVec_64 .TCR_EL2)
    (tcr2 : after.bank_BitVec_64 .TCR2_EL2 = before.bank_BitVec_64 .TCR2_EL2)
    (scr : after.bank_BitVec_64 .SCR_EL3 = before.bank_BitVec_64 .SCR_EL3) :
    hostHAFT after = hostHAFT before := by
  have gate : hostTCR2Enabled after = hostTCR2Enabled before := by
    simp only [hostTCR2Enabled, features, scr]
  have ha : hostHA after = hostHA before := by simp only [hostHA, features, tcr]
  unfold hostHAFT
  rw [features, ha, gate, tcr2]

/-- Getter-derived flag facts remain available for the existing ordered-history
    active-control reparametrization. No inactive parameter equality is used. -/
theorem HostFlagShape.registers {before after : Regs} {params : S1TTWParams}
    (current : HostFlagShape before params)
    (features : after.FeatureImpl = before.FeatureImpl)
    (tcr : after.bank_BitVec_64 .TCR_EL2 = before.bank_BitVec_64 .TCR_EL2)
    (tcr2 : after.bank_BitVec_64 .TCR2_EL2 = before.bank_BitVec_64 .TCR2_EL2)
    (scr : after.bank_BitVec_64 .SCR_EL3 = before.bank_BitVec_64 .SCR_EL3)
    (sctlr : after.bank_BitVec_64 .SCTLR_EL2 = before.bank_BitVec_64 .SCTLR_EL2) :
    HostFlagShape after params := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hostHA, features, tcr] using current.1
  · simpa only [hostHD, features, tcr] using current.2.1
  · exact current.2.2.1.trans (host_pie_register_fields before after features tcr2 scr).symm
  · exact current.2.2.2.1.trans (host_haft_register_fields before after features tcr tcr2 scr).symm
  · simpa only [sctlr] using current.2.2.2.2

theorem HostImageParamsAt.registers {before after : Regs} {params : S1TTWParams}
    (current : HostImageParamsAt before params)
    (features : after.FeatureImpl = before.FeatureImpl)
    (tcr : after.bank_BitVec_64 .TCR_EL2 = before.bank_BitVec_64 .TCR_EL2)
    (tcr2 : after.bank_BitVec_64 .TCR2_EL2 = before.bank_BitVec_64 .TCR2_EL2)
    (scr : after.bank_BitVec_64 .SCR_EL3 = before.bank_BitVec_64 .SCR_EL3)
    (sctlr : after.bank_BitVec_64 .SCTLR_EL2 = before.bank_BitVec_64 .SCTLR_EL2) :
    HostImageParamsAt after params := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hostHA, features, tcr] using current.ha
  · simpa only [hostHD, features, tcr] using current.hd
  · exact current.pie.trans (host_pie_register_fields before after features tcr2 scr).symm
  · simpa only [sctlr] using current.wxn
  · simpa only [features, tcr] using current.mtx
  · simpa only [tcr] using current.txsz

theorem HostPermissionControlsAt.registers {before after : Regs} {controls : S1LogicalReference.Controls}
    (current : HostPermissionControlsAt before controls)
    (features : after.FeatureImpl = before.FeatureImpl)
    (tcr : after.bank_BitVec_64 .TCR_EL2 = before.bank_BitVec_64 .TCR_EL2)
    (tcr2 : after.bank_BitVec_64 .TCR2_EL2 = before.bank_BitVec_64 .TCR2_EL2)
    (scr : after.bank_BitVec_64 .SCR_EL3 = before.bank_BitVec_64 .SCR_EL3)
    (el3 : before.FeatureImpl[7] = true)
    (pir : controls.pie = true → after.bank_BitVec_64 .PIR_EL2 = before.bank_BitVec_64 .PIR_EL2)
    (pire0 : controls.pie = true → after.bank_BitVec_64 .PIRE0_EL2 = before.bank_BitVec_64 .PIRE0_EL2) :
    HostPermissionControlsAt after controls := by
  refine ⟨current.regime, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hostHA, features, tcr] using current.ha
  · simpa only [hostHD, features, tcr] using current.hd
  · rw [host_pie_register_fields before after features tcr2 scr]; exact current.pie
  · simpa only [features, tcr] using current.hpd
  · intro active; rw [pir active]; exact current.pir active
  · intro active; rw [pire0 active]; exact current.pire0 active
  · exact current.overlay.trans (overlay_enables_register_fields before after features tcr2 scr el3).2.symm

theorem HostRegimeAt.registers {before after : State} (current : HostRegimeAt before)
    (features : after.regs.FeatureImpl = before.regs.FeatureImpl)
    (nrw : after.regs.PSTATE.nRW = before.regs.PSTATE.nRW)
    (tcr : after.regs.bank_BitVec_64 .TCR_EL2 = before.regs.bank_BitVec_64 .TCR_EL2)
    (tcr2 : after.regs.bank_BitVec_64 .TCR2_EL2 = before.regs.bank_BitVec_64 .TCR2_EL2)
    (hcr : after.regs.bank_BitVec_64 .HCR_EL2 = before.regs.bank_BitVec_64 .HCR_EL2) :
    HostRegimeAt after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [features] using current.el3a64
  · simpa only [features] using current.noEl3a32
  · simpa only [features] using current.noRME
  · exact nrw.trans current.a64
  · simpa only [tcr] using current.tg
  · simpa only [hcr] using current.e2h
  · simpa only [features, tcr2] using current.d128
  · simpa only [features, tcr2] using current.aie
  · simpa only [features, tcr2] using current.pnch
  · simpa only [tcr] using current.ds

theorem physical_at_register_fields {config : PhysicalConfig} {before after : State}
    (current : PhysicalAt config before) (features : after.regs.FeatureImpl = before.regs.FeatureImpl)
    (pa : after.regs.bank_Int .__supported_pa_size = before.regs.bank_Int .__supported_pa_size) :
    PhysicalAt config after :=
  ⟨current.legal, pa.trans current.pa, by simpa only [features] using current.lpa,
    by simpa only [features] using current.lpa2⟩

theorem current_layout_register_fields {layout : S1LogicalReference.Layout} {params : S1TTWParams}
    {va : BitVec 64} {before after : Regs} (current : CurrentLayoutAt layout params va before)
    (ttbr0 : after.bank_BitVec_128 ._TTBR0_EL2 = before.bank_BitVec_128 ._TTBR0_EL2)
    (httbr : after.bank_BitVec_64 .HTTBR = before.bank_BitVec_64 .HTTBR)
    (ttbr1 : after.bank_BitVec_128 .TTBR1_EL2 = before.bank_BitVec_128 .TTBR1_EL2) :
    CurrentLayoutAt layout params va after := by
  refine ⟨current.start, current.inputBits, ?_⟩
  simpa only [selectedRootTTBR, currentTTBR0, ttbr0, httbr, ttbr1] using current.root

theorem current_walk_epd_register_fields (before after : Regs) (va : BitVec 64)
    (tcr : after.bank_BitVec_64 .TCR_EL2 = before.bank_BitVec_64 .TCR_EL2) :
    currentWalkEPD after va = currentWalkEPD before va := by simp only [currentWalkEPD, tcr]

/-- Transport the existing current getter/walk primitive bundle from selected
    outputs of the actual phase frame. This adds no new admission predicate. -/
theorem HostWalkAt.registers {config : AttributeConfig} {controls : S1LogicalReference.Controls}
    {physicalConfig : PhysicalConfig} {before after : State}
    (current : HostWalkAt config controls physicalConfig before)
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
    (pir : controls.pie = true → after.regs.bank_BitVec_64 .PIR_EL2 = before.regs.bank_BitVec_64 .PIR_EL2)
    (pire0 : controls.pie = true → after.regs.bank_BitVec_64 .PIRE0_EL2 = before.regs.bank_BitVec_64 .PIRE0_EL2) :
    HostWalkAt config controls physicalConfig after := by
  refine ⟨current.regime.registers features nrw tcr tcr2 hcr,
    current.controls.registers features tcr tcr2 scr current.regime.el3a64 pir pire0,
    physical_at_register_fields current.physical features pa, ?_, ?_, current.mair.trans mair.symm, ?_, ?_, ?_⟩
  · simpa only [tcr] using current.ips
  · simpa only [sctlr] using current.endian
  · simpa only [features] using current.xs
  · simpa only [features] using current.mte2
  · simpa only [el] using current.el

#print axioms host_haft_register_fields
#print axioms HostFlagShape.registers
#print axioms HostWalkAt.registers
#print axioms overlay_enables_register_fields
#print axioms host_pie_register_fields
#print axioms HostImageParamsAt.registers
#print axioms HostPermissionControlsAt.registers
#print axioms HostRegimeAt.registers
#print axioms physical_at_register_fields
#print axioms current_layout_register_fields
#print axioms current_walk_epd_register_fields
end ArmCert.Translate.Model
