import ArmCertTranslateModel.ClosedMembershipTransport
import ArmCertTranslateModel.NormalizedControlTransport
import ArmCertTranslateModel.CurrentControlTransport
import ArmCertTranslateModel.LeafOutputBinding

set_option autoImplicit false

/-!
# Projection-level closed membership transport

`ClosedChain.closed_of_fields` / `NativeLoaderSynth.closed_transfer` require the WHOLE feature vector and whole
TCR/SCTLR/TTBR words to agree, which no source completion satisfies against a fixed register file.
`CurrentS1AccessAt` only reads: features 227 (TME), 81 (vector), 101 (BBM) and, under BBM,
`__block_bbm_implemented`; TCR_EL2.EPD0/EPD1 (through `currentWalkEPD`); SCTLR_EL2.I/C (output cache
policy); and the TTBR words (walk root; payload data). These lemmas transport it, and closed membership,
on exactly those projections.
-/

namespace ReleaseProfile.GB10.ClosedProjection

open ArmFull ArmCert.Translate.Model ArmCertWalk

/-- The register projections a current S1 access depends on, as hypotheses `after` vs `before`. -/
structure WalkAgree (before after : Regs) : Prop where
  tme : after.FeatureImpl[227] = before.FeatureImpl[227]
  vector : after.FeatureImpl[81] = before.FeatureImpl[81]
  bbmFeature : after.FeatureImpl[101] = before.FeatureImpl[101]
  bbm : before.FeatureImpl[101] = true →
    after.bank_Int .__block_bbm_implemented = before.bank_Int .__block_bbm_implemented
  epd : ∀ va, currentWalkEPD before va = 0#1 → currentWalkEPD after va = 0#1
  icache : currentICache after = currentICache before
  dcache : currentDCache after = currentDCache before
  ttbr0 : after.bank_BitVec_128 ._TTBR0_EL2 = before.bank_BitVec_128 ._TTBR0_EL2
  httbr : after.bank_BitVec_64 .HTTBR = before.bank_BitVec_64 .HTTBR
  ttbr1 : after.bank_BitVec_128 .TTBR1_EL2 = before.bank_BitVec_128 .TTBR1_EL2

theorem current_s1_access_projected {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {data : S1AccessData spec config rows query} {before after : ArmCertWalk.State}
    (access : CurrentS1AccessAt spec config rows mapping query data before)
    (agree : WalkAgree before.regs after.regs) :
    CurrentS1AccessAt spec config rows mapping query data after := by
  refine ⟨current_layout_register_fields access.layout agree.ttbr0 agree.httbr agree.ttbr1,
    ⟨access.checks.va, access.checks.e0pd, ?_, ?_⟩, agree.epd _ access.epd,
    access.map.registers (fun _ => agree.bbmFeature) (fun _ h => agree.bbm h), ?_⟩
  · simpa only [sourceTmeFault, agree.tme] using access.checks.tme
  · simpa only [sourceVectorFault, agree.vector] using access.checks.vector
  · simpa only [OutputCacheAdmissible, agree.icache, agree.dcache] using access.outputPolicy

/-- Closed membership on the walk projections. -/
theorem closed_of_projection {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {before after : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping m before)
    (agree : WalkAgree before.regs after.regs) :
    ClosedMembershipAt spec config rows mapping m after := by
  intro va acc aligned size permitted
  obtain ⟨q, hva, hraw, hal, hsz, member, data, access⟩ := closed va acc aligned size permitted
  exact ⟨q, hva, hraw, hal, hsz, member, data, current_s1_access_projected access agree⟩

/-- `closed_transfer` on projections: from closed membership at every state over a reference register
file `r` (e.g. a regs-generic witness instantiated at one file) to any state agreeing with `r` on the walk
projections. -/
theorem closed_transfer_projected {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} (r : Regs)
    (hc : ∀ s : ArmCertWalk.State, s.regs = r → ClosedMembershipAt spec config rows mapping m s)
    (x : ArmCertWalk.State) (agree : WalkAgree r x.regs) : ClosedMembershipAt spec config rows mapping m x :=
  closed_of_projection (hc { x with regs := r } rfl) agree

end ReleaseProfile.GB10.ClosedProjection

#print axioms ReleaseProfile.GB10.ClosedProjection.current_s1_access_projected
#print axioms ReleaseProfile.GB10.ClosedProjection.closed_of_projection
#print axioms ReleaseProfile.GB10.ClosedProjection.closed_transfer_projected
