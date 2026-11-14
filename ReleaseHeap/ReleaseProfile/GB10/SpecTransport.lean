import ReleaseProfile.GB10.ClosedPages
import ArmCertTranslateModel.PathPermissionBinding
import ArmCertTranslateModel.LeafBinding
import ArmCertWalk.RootMeaning

set_option autoImplicit false
set_option maxHeartbeats 400000

/-!
# Spec-side transport of closed membership

`CurrentS1AccessAt`/`S1AccessData` read the spec only through: params txsz/tbi/tbid/mtx/e0pd/nfd (layout,
translate checks), params ha/hd/pie/mtx (row view, row attributes), controls hpd/pie/nv1Mode (table
permissions in the path annotation), and the tables/layout/physicalConfig. A spec with the same tables
equals the base spec with params/controls replaced; on that update the path data is unchanged.
-/

namespace ReleaseProfile.GB10.SpecTransport

open Sail ArmFull ArmFull.Functions ArmCertWalk ArmCert.Translate ArmCert.Translate.Model
open ReleaseProfile.GB10.ClosedPages

/-- Spec walk fields `P`/`C` agree with `spec`'s on everything the walk reads. -/
structure SpecAgree {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (P : S1TTWParams) (C : S1LogicalReference.Controls) : Prop where
  txsz : P.txsz = spec.params.txsz
  tbi : P.tbi = spec.params.tbi
  tbid : P.tbid = spec.params.tbid
  mtx : P.mtx = spec.params.mtx
  e0pd : P.e0pd = spec.params.e0pd
  nfd : P.nfd = spec.params.nfd
  ha : P.ha = spec.params.ha
  hd : P.hd = spec.params.hd
  pie : P.pie = spec.params.pie
  tp : S1LogicalReference.tablePermissions C = S1LogicalReference.tablePermissions spec.controls

theorem annotation_recontrol {observe : S1LogicalReference.Observation} {paBits : Nat} {va : BitVec 64}
    {c c' : S1LogicalReference.Controls}
    (htp : S1LogicalReference.tablePermissions c' = S1LogicalReference.tablePermissions c)
    {level bits : Nat} {base : BitVec 48} {endpoint : S1LogicalReference.PathEnd}
    {path : S1LogicalReference.Path observe paBits va level bits base endpoint}
    {prior : S1LogicalReference.TablePermissions} {words : List (BitVec 64)} {final : S1LogicalReference.TablePermissions}
    (h : PathPermissionAnnotation observe paBits va c path prior words final) :
    PathPermissionAnnotation observe paBits va c' path prior words final := by
  induction h with
  | invalid level bits base physical view hl aligned present kind prior =>
    exact .invalid level bits base physical view hl aligned present kind prior
  | leaf level bits base physical view hl aligned present kind prior =>
    exact .leaf level bits base physical view hl aligned present kind prior
  | range level bits base physical view hl aligned present kind outOfRange prior =>
    exact .range level bits base physical view hl aligned present kind outOfRange prior
  | table level bits base physical view endpoint hl aligned present kind inRange tail prior final words annotation ih =>
    exact .table level bits base physical view endpoint hl aligned present kind inRange tail prior final words
      (htp ▸ ih)

section
variable {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
  {rows : List PermissionRow} {P : S1TTWParams} {C : S1LogicalReference.Controls}

/-- Access data transported to the spec with replaced params/controls. -/
def dataUpdate {query : AccessQuery} {config' : AttributeConfig} (agree : SpecAgree spec P C)
    (hattr : ∀ row ∈ rows, checkPermissionRowAttributes config spec.params row = true →
      checkPermissionRowAttributes config' P row = true)
    (data : S1AccessData spec config rows query) :
    S1AccessData { spec with params := P, controls := C } config' rows query where
  leafLevel := data.leafLevel
  logical := data.logical
  physical := data.physical
  view := data.view
  path := data.path
  permissions :=
    { row := data.permissions.row
      member := data.permissions.member
      slot := data.permissions.slot
      words := data.permissions.words
      annotation := annotation_recontrol agree.tp data.permissions.annotation
      used := data.permissions.used
      rowView := by
        have h := data.permissions.rowView
        simp only [agree.ha, agree.hd, agree.pie]
        exact h
      attributes := hattr _ data.permissions.member data.permissions.attributes
      kind := data.permissions.kind
      read := data.permissions.read
      write := data.permissions.write
      tagaccess := data.permissions.tagaccess }
  lower := data.lower
  accessEL := data.accessEL
  nonsecure := data.nonsecure

theorem current_update {mapping : BitVec 64 → Option Nat} {query : AccessQuery} {config' : AttributeConfig}
    {data : S1AccessData spec config rows query} {s : ArmCertWalk.State} (agree : SpecAgree spec P C)
    (hattr : ∀ row ∈ rows, checkPermissionRowAttributes config spec.params row = true →
      checkPermissionRowAttributes config' P row = true)
    (access : CurrentS1AccessAt spec config rows mapping query data s) :
    CurrentS1AccessAt { spec with params := P, controls := C } config' rows mapping query (dataUpdate agree hattr data) s := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, access.epd, access.map, access.outputPolicy⟩
  · simpa only [rootStartLevel, agree.txsz] using access.layout.start
  · simpa only [agree.txsz] using access.layout.inputBits
  · simpa only [rootBaseValue, rootTableSize, rootStartLevel, agree.txsz] using access.layout.root
  · simpa only [AArch64_VAIsOutOfRange, agree.txsz, agree.tbi, agree.tbid, agree.mtx] using access.checks.va
  · simpa only [sourceE0PDFault, agree.e0pd] using access.checks.e0pd
  · simpa only [sourceTmeFault, agree.nfd] using access.checks.tme
  · simpa only [sourceVectorFault, agree.nfd] using access.checks.vector

theorem closed_pages_update {mapping : BitVec 64 → Option Nat} {config' : AttributeConfig}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {s : ArmCertWalk.State} (agree : SpecAgree spec P C)
    (hattr : ∀ row ∈ rows, checkPermissionRowAttributes config spec.params row = true →
      checkPermissionRowAttributes config' P row = true)
    (closed : ClosedPagesAt spec config rows mapping m s) :
    ClosedPagesAt { spec with params := P, controls := C } config' rows mapping m s := by
  intro va acc aligned size permitted
  obtain ⟨q, hva, hraw, hal, hsz, member, data, page, access⟩ := closed va acc aligned size permitted
  exact ⟨q, hva, hraw, hal, hsz, member, dataUpdate agree hattr data, page, current_update agree hattr access⟩
end

/-- A spec with the base spec's tables/layout/physicalConfig is the base spec with params/controls replaced. -/
theorem spec_eq_update {domain : QueryDomain} {spec spec' : TopologyImageSpec domain}
    (hph : spec'.physicalConfig = spec.physicalConfig) (hlay : spec'.layout = spec.layout)
    (hlr : spec'.logicalRows = spec.logicalRows) (hir : spec'.imageRows = spec.imageRows) :
    spec' = { spec with params := spec'.params, controls := spec'.controls } := by
  cases spec; cases spec'
  simp only at hph hlay hlr hir ⊢
  subst hph hlay hlr hir
  rfl

/-- Closed-with-pages over the base spec transfers to any spec with the same tables agreeing on the walk fields. -/
theorem closed_pages_spec {domain : QueryDomain} {spec spec' : TopologyImageSpec domain}
    {config config' : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {s : ArmCertWalk.State}
    (hph : spec'.physicalConfig = spec.physicalConfig) (hlay : spec'.layout = spec.layout)
    (hlr : spec'.logicalRows = spec.logicalRows) (hir : spec'.imageRows = spec.imageRows)
    (agree : SpecAgree spec spec'.params spec'.controls)
    (hattr : ∀ row ∈ rows, checkPermissionRowAttributes config spec.params row = true →
      checkPermissionRowAttributes config' spec'.params row = true)
    (closed : ClosedPagesAt spec config rows mapping m s) : ClosedPagesAt spec' config' rows mapping m s := by
  rw [spec_eq_update hph hlay hlr hir]
  exact closed_pages_update agree hattr closed

/-- End to end: closed membership at the world entry over the source-pinned spec and config, from closed
pages over the base spec/config at a reference register file `r`. -/
theorem closed_world {domain : QueryDomain} {spec spec' : TopologyImageSpec domain}
    {config config' : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} (r : Regs)
    (hc : ∀ s : ArmCertWalk.State, s.regs = r → ClosedPagesAt spec config rows mapping m s)
    (hph : spec'.physicalConfig = spec.physicalConfig) (hlay : spec'.layout = spec.layout)
    (hlr : spec'.logicalRows = spec.logicalRows) (hir : spec'.imageRows = spec.imageRows)
    (agree : SpecAgree spec spec'.params spec'.controls)
    (hattr : ∀ row ∈ rows, checkPermissionRowAttributes config spec.params row = true →
      checkPermissionRowAttributes config' spec'.params row = true)
    (x : ArmCertWalk.State) (walk : WalkAgreePages r x.regs) :
    ClosedMembershipAt spec' config' rows mapping m x :=
  (closed_pages_spec hph hlay hlr hir agree hattr
    (closed_pages_of_projection (hc { x with regs := r } rfl) walk)).closed

end ReleaseProfile.GB10.SpecTransport

#print axioms ReleaseProfile.GB10.SpecTransport.closed_pages_spec
#print axioms ReleaseProfile.GB10.SpecTransport.closed_world
