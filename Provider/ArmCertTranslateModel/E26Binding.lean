import ArmCertTranslateModel.CurrentS1Checks
import ArmCertTranslateModel.CurrentProgramTransport

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- E26 clause (a), typed on the ACTUAL declared descriptor footprint and roots,
    for one interval that the model does not step (OS/environment): the covered
    descriptor bytes and the translation roots are unchanged. The certified run's
    own modeled walks (the only permitted AF/dirty SETTING) are model steps and
    are handled by the translation lemmas, not by this interval predicate.
 Explicit environment hypothesis; not proved here. -/
def E26CoveredUnchanged {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (before after : State) : Prop :=
  AgreeOn (rowsFootprint spec.imageRows).byte (fun a => before.mem[a]?) (fun a => after.mem[a]?) ∧
  after.regs.bank_BitVec_128 ._TTBR0_EL2 = before.regs.bank_BitVec_128 ._TTBR0_EL2 ∧
  after.regs.bank_BitVec_64 .HTTBR = before.regs.bank_BitVec_64 .HTTBR ∧
  after.regs.bank_BitVec_128 .TTBR1_EL2 = before.regs.bank_BitVec_128 .TTBR1_EL2

/-- The selected translation-control fields the program's resumed context must
    find unchanged after such an interval (existing interrupt/fault restoration
    trust, separate from E26). Only fields the current invariant reads. -/
structure ControlsRestored {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (before after : State) : Prop where
  features : after.regs.FeatureImpl = before.regs.FeatureImpl
  el : after.regs.PSTATE.EL = before.regs.PSTATE.EL
  nrw : after.regs.PSTATE.nRW = before.regs.PSTATE.nRW
  tcr : after.regs.bank_BitVec_64 .TCR_EL2 = before.regs.bank_BitVec_64 .TCR_EL2
  tcr2 : after.regs.bank_BitVec_64 .TCR2_EL2 = before.regs.bank_BitVec_64 .TCR2_EL2
  hcr : after.regs.bank_BitVec_64 .HCR_EL2 = before.regs.bank_BitVec_64 .HCR_EL2
  scr : after.regs.bank_BitVec_64 .SCR_EL3 = before.regs.bank_BitVec_64 .SCR_EL3
  sctlr : after.regs.bank_BitVec_64 .SCTLR_EL2 = before.regs.bank_BitVec_64 .SCTLR_EL2
  mair : after.regs.bank_BitVec_64 .MAIR_EL2 = before.regs.bank_BitVec_64 .MAIR_EL2
  pa : after.regs.bank_Int .__supported_pa_size = before.regs.bank_Int .__supported_pa_size
  pir : spec.controls.pie = true →
    after.regs.bank_BitVec_64 .PIR_EL2 = before.regs.bank_BitVec_64 .PIR_EL2
  pire0 : spec.controls.pie = true →
    after.regs.bank_BitVec_64 .PIRE0_EL2 = before.regs.bank_BitVec_64 .PIRE0_EL2
  por : e0OverlayEnabled before.regs = true →
    after.regs.bank_BitVec_64 .POR_EL0 = before.regs.bank_BitVec_64 .POR_EL0
  cache : after.regs.bank_Bool .__tlb_enabled = before.regs.bank_Bool .__tlb_enabled
  bbm : before.regs.FeatureImpl[101] = true →
    after.regs.bank_Int .__block_bbm_implemented = before.regs.bank_Int .__block_bbm_implemented

/-- An unchanged descriptor footprint is a write frame separated from it. -/
theorem e26_write_frame {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {before after : State} (unchanged : E26CoveredUnchanged spec before after) :
    WritesOnly (fun a => ¬ (rowsFootprint spec.imageRows).byte a) (fun a => before.mem[a]?)
        (fun a => after.mem[a]?) ∧
      Separated (rowsFootprint spec.imageRows).byte (fun a => ¬ (rowsFootprint spec.imageRows).byte a) :=
  ⟨fun a outside => unchanged.1 a (Classical.not_not.1 outside), fun _ inside outside => outside inside⟩

/-- The current invariant survives an E26 interval with restored controls. -/
theorem current_s1_across_interval {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {before after : State}
    (current : CurrentS1At spec config rows before) (unchanged : E26CoveredUnchanged spec before after)
    (restored : ControlsRestored spec before after) : CurrentS1At spec config rows after :=
  current_s1_program_write current _ (e26_write_frame unchanged).1 (e26_write_frame unchanged).2
    restored.features restored.el restored.nrw restored.tcr restored.tcr2 restored.hcr restored.scr
    restored.sctlr restored.mair restored.pa restored.pir restored.pire0 restored.por restored.cache

/-- Every declared query's current access data survives the same interval. -/
theorem current_s1_access_across_interval {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {data : S1AccessData spec config rows query} {before after : State}
    (access : CurrentS1AccessAt spec config rows mapping query data before)
    (unchanged : E26CoveredUnchanged spec before after) (restored : ControlsRestored spec before after) :
    CurrentS1AccessAt spec config rows mapping query data after :=
  current_s1_access_registers access restored.features restored.tcr restored.sctlr unchanged.2.1
    unchanged.2.2.1 unchanged.2.2.2 (fun _ active => restored.bbm active)

/-- Closed membership survives the interval (same declared queries and data). -/
theorem closed_membership_across_interval {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {before after : State}
    (closed : ClosedMembershipAt spec config rows mapping m before)
    (unchanged : E26CoveredUnchanged spec before after) (restored : ControlsRestored spec before after) :
    ClosedMembershipAt spec config rows mapping m after := by
  intro va acc aligned size permitted
  obtain ⟨query, hva, hraw, haligned, hsize, member, data, access⟩ := closed va acc aligned size permitted
  exact ⟨query, hva, hraw, haligned, hsize, member, data,
    current_s1_access_across_interval access unchanged restored⟩

#print axioms e26_write_frame
#print axioms current_s1_across_interval
#print axioms current_s1_access_across_interval
#print axioms closed_membership_across_interval
end ArmCert.Translate.Model
