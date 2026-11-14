import ArmCertTranslateModel.HeapV2FetchEl0
import ArmCertTranslateModel.CurrentS1Checks
import ArmCertWalk.PageTransfer
import ArmCertTranslateModel.ClosedTable
import ReleaseProfile.GB10.ClosedProjection

set_option autoImplicit false

/-!
# Closed membership with page leaves, transported on walk projections

Re-homes the program-independent representative checks of `TranslateSynth.Checks` (a synthetic-named module)
and records that every chosen walk leaf is a level-3 page. With page leaves the BBM support integer
(`__block_bbm_implemented`, undeclared in the source) never enters `LeafMapAt`, so closed membership
transports on features 227/81, EPD, SCTLR_EL2.I/C and the TTBR words alone.
-/

namespace ReleaseProfile.GB10.ClosedPages

open Sail ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate ArmCert.Translate.Model

def isLower (va : BitVec 64) : Bool :=
  match AArch64_GetVARange va with | .VARange_LOWER => true | _ => false

theorem isLower_sound {va : BitVec 64} (h : isLower va = true) : AArch64_GetVARange va = .VARange_LOWER := by
  unfold isLower at h
  split at h
  · assumption
  · contradiction

section
variable {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)

noncomputable def checkAt (q : AccessQuery) (level : Nat) (view : S1DescriptorPIE.View 64) (R : Regs) : Bool :=
  checkCurrentLayout spec.layout spec.params q.va R &&
  (checkTranslateQuery R spec.params q.va q.request.raw &&
  (decide (currentWalkEPD R q.va = 0#1) &&
  (checkLeafMap mapping spec.physicalConfig R q level view && checkOutputCache q.request.raw R)))

structure Representative (queries : List AccessQuery) (shape : AccessDescriptor → Prop) where
  query : AccessQuery
  member : query ∈ queries
  level : Nat
  view : S1DescriptorPIE.View 64
  data : S1AccessData spec config rows query
  leafLevel : data.leafLevel = level
  leafView : data.view = view
  shaped : shape query.request.raw

noncomputable def repOK {queries : List AccessQuery} {shape : AccessDescriptor → Prop}
    (rep : Representative spec config rows queries shape) (R : Regs) (va : BitVec 64) (size : Int) : Bool :=
  decide (rep.query.va.toNat / 4096 = va.toNat / 4096) &&
  checkAt spec mapping ⟨va, rep.query.request, size⟩ rep.level rep.view R

noncomputable def accessOK {queries : List AccessQuery} {shape : AccessDescriptor → Prop}
    (reps : List (Representative spec config rows queries shape)) (R : Regs) (va : BitVec 64) (size : Int) : Bool :=
  (isLower va && ((mapping va).isSome && decide ((mapping va).getD 0 < 2 ^ 56))) &&
  reps.any (fun rep => repOK spec config rows mapping rep R va size)

/-- `TranslateSynth.access_case`, additionally recording a level-3 (page) leaf. -/
theorem access_case_pages {queries : List AccessQuery} {shape : AccessDescriptor → Prop}
    (reps : List (Representative spec config rows queries shape)) (levels : ∀ rep ∈ reps, rep.level = 3)
    (R : Regs) (va : BitVec 64) (size : Int) (h : accessOK spec config rows mapping reps R va size = true)
    (state : ArmCertWalk.State) (regs : state.regs = R) :
    (∃ q0 ∈ queries, SamePage q0.va va) ∧
    ∃ (r : S1LogicalReference.Request) (data : S1AccessData spec config rows ⟨va, r, size⟩),
      shape r.raw ∧ data.leafLevel = 3 ∧ CurrentS1AccessAt spec config rows mapping ⟨va, r, size⟩ data state := by
  simp only [accessOK, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at h
  obtain ⟨⟨lower, ⟨pa, hpa⟩, bound⟩, anyRep⟩ := h
  obtain ⟨rep, repMem, checked⟩ := List.any_eq_true.1 anyRep
  simp only [repOK, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨same, checked⟩ := checked
  have agree : AccAgree rep.query.request.raw rep.query.request.raw :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  let data := S1AccessData.transferPage (r' := rep.query.request) (size' := size) rep.data same agree (isLower_sound lower)
  refine ⟨⟨rep.query, rep.member, same⟩, rep.query.request, data, rep.shaped, ?_, ?_⟩
  · show (S1AccessData.transferPage (r' := rep.query.request) (size' := size) rep.data same agree
      (isLower_sound lower)).leafLevel = 3
    rw [show (S1AccessData.transferPage (r' := rep.query.request) (size' := size) rep.data same agree
      (isLower_sound lower)).leafLevel = rep.data.leafLevel from rfl, rep.leafLevel]
    exact levels rep repMem
  · apply current_s1_access_of_check
    change checkAt spec mapping ⟨va, rep.query.request, size⟩ rep.data.leafLevel rep.data.view state.regs = true
    rw [rep.leafLevel, rep.leafView, regs]
    exact checked
end

/-! ## Closed membership with page leaves, and its projection transport -/

def ClosedPagesAt {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (s : ArmCertWalk.State) : Prop :=
  ∀ va acc aligned size, m.permitted va acc aligned size →
    ∃ query : AccessQuery, query.va = va ∧ query.request.raw = acc ∧
      query.request.aligned = aligned ∧ query.size = size ∧ domain query ∧
      ∃ data : S1AccessData spec config rows query, data.leafLevel = 3 ∧
        CurrentS1AccessAt spec config rows mapping query data s

theorem ClosedPagesAt.closed {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {s : ArmCertWalk.State}
    (h : ClosedPagesAt spec config rows mapping m s) : ClosedMembershipAt spec config rows mapping m s := by
  intro va acc aligned size permitted
  obtain ⟨q, hva, hraw, hal, hsz, member, data, _, access⟩ := h va acc aligned size permitted
  exact ⟨q, hva, hraw, hal, hsz, member, data, access⟩

/-- The walk projections for page leaves: no BBM fields. -/
structure WalkAgreePages (before after : Regs) : Prop where
  tme : after.FeatureImpl[227] = before.FeatureImpl[227]
  vector : after.FeatureImpl[81] = before.FeatureImpl[81]
  epd : ∀ va, currentWalkEPD before va = 0#1 → currentWalkEPD after va = 0#1
  icache : currentICache after = currentICache before
  dcache : currentDCache after = currentDCache before
  ttbr0 : after.bank_BitVec_128 ._TTBR0_EL2 = before.bank_BitVec_128 ._TTBR0_EL2
  httbr : after.bank_BitVec_64 .HTTBR = before.bank_BitVec_64 .HTTBR
  ttbr1 : after.bank_BitVec_128 .TTBR1_EL2 = before.bank_BitVec_128 .TTBR1_EL2

theorem current_s1_access_pages {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {data : S1AccessData spec config rows query} {before after : ArmCertWalk.State}
    (access : CurrentS1AccessAt spec config rows mapping query data before) (page : data.leafLevel = 3)
    (agree : WalkAgreePages before.regs after.regs) :
    CurrentS1AccessAt spec config rows mapping query data after := by
  refine ⟨current_layout_register_fields access.layout agree.ttbr0 agree.httbr agree.ttbr1,
    ⟨access.checks.va, access.checks.e0pd, ?_, ?_⟩, agree.epd _ access.epd,
    access.map.registers (fun h => absurd page (by omega)) (fun h _ => absurd page (by omega)), ?_⟩
  · simpa only [sourceTmeFault, agree.tme] using access.checks.tme
  · simpa only [sourceVectorFault, agree.vector] using access.checks.vector
  · simpa only [OutputCacheAdmissible, agree.icache, agree.dcache] using access.outputPolicy

theorem closed_pages_of_projection {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {before after : ArmCertWalk.State}
    (closed : ClosedPagesAt spec config rows mapping m before) (agree : WalkAgreePages before.regs after.regs) :
    ClosedPagesAt spec config rows mapping m after := by
  intro va acc aligned size permitted
  obtain ⟨q, hva, hraw, hal, hsz, member, data, page, access⟩ := closed va acc aligned size permitted
  exact ⟨q, hva, hraw, hal, hsz, member, data, page, current_s1_access_pages access page agree⟩

/-- Transfer from closed-with-pages at a reference register file `r` to any state on the walk projections. -/
theorem closed_transfer_pages {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} (r : Regs)
    (hc : ∀ s : ArmCertWalk.State, s.regs = r → ClosedPagesAt spec config rows mapping m s)
    (x : ArmCertWalk.State) (agree : WalkAgreePages r x.regs) :
    ClosedMembershipAt spec config rows mapping m x :=
  (closed_pages_of_projection (hc { x with regs := r } rfl) agree).closed

end ReleaseProfile.GB10.ClosedPages

#print axioms ReleaseProfile.GB10.ClosedPages.access_case_pages
#print axioms ReleaseProfile.GB10.ClosedPages.closed_transfer_pages
