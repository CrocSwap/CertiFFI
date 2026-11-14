-- (E17 instance table cost): the walk certificate of a query transfers to every VA in the
-- SAME 4KiB page (all table indices read VA bits ≥ 12), so one evaluated Path per page suffices.
-- The remaining per-access checks (layout / translate-query / EPD / leaf map / VA range) are cheap
-- per-VA register decisions and stay evaluated by the caller (checkCurrentS1Access).
import ArmCertWalk.AccessTransfer
open Sail ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk
open S1LogicalReference

/-- Two VAs in the same 4KiB page. -/
def SamePage (va va' : BitVec 64) : Prop := va.toNat / 4096 = va'.toNat / 4096

theorem entryIndex_page {va va' : BitVec 64} (h : SamePage va va') (level bits : Nat) :
    entryIndex va level bits = entryIndex va' level bits := by
  unfold entryIndex
  have split : 2 ^ (12 + 9 * (3 - level)) = 4096 * 2 ^ (9 * (3 - level)) := by
    rw [Nat.pow_add]
  rw [split, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

theorem entryAddress_page {va va' : BitVec 64} (h : SamePage va va') (base : BitVec 48) (level bits : Nat) :
    entryAddress base va level bits = entryAddress base va' level bits := by
  unfold entryAddress; rw [entryIndex_page h]

theorem path_page {observe : Observation} {paBits : Nat} {va va' : BitVec 64} (h : SamePage va va')
    {level bits : Nat} {base : BitVec 48} {endpoint : PathEnd}
    (p : Path observe paBits va level bits base endpoint) : Path observe paBits va' level bits base endpoint := by
  induction p with
  | invalid level bits base physical view hl aligned present kind =>
    exact .invalid level bits base physical view hl (by rw [← entryAddress_page h]; exact aligned)
      (by rw [← entryAddress_page h]; exact present) kind
  | leaf level bits base physical view hl aligned present kind =>
    rw [entryAddress_page h]
    exact .leaf level bits base physical view hl (by rw [← entryAddress_page h]; exact aligned)
      (by rw [← entryAddress_page h]; exact present) kind
  | range level bits base physical view hl aligned present kind outOfRange =>
    exact .range level bits base physical view hl (by rw [← entryAddress_page h]; exact aligned)
      (by rw [← entryAddress_page h]; exact present) kind (by rw [← entryAddress_page h]; exact outOfRange)
  | table level bits base physical view endpoint hl aligned present kind inRange tail ih =>
    exact .table level bits base physical view endpoint hl (by rw [← entryAddress_page h]; exact aligned)
      (by rw [← entryAddress_page h]; exact present) kind (by rw [← entryAddress_page h]; exact inRange) ih

theorem annotation_page {observe : Observation} {paBits : Nat} {va va' : BitVec 64} (h : SamePage va va')
    {controls : S1LogicalReference.Controls} {level bits : Nat} {base : BitVec 48} {endpoint : PathEnd}
    {p : Path observe paBits va level bits base endpoint} {prior final : TablePermissions}
    {words : List (BitVec 64)}
    (a : PathPermissionAnnotation observe paBits va controls p prior words final) :
    PathPermissionAnnotation observe paBits va' controls (path_page h p) prior words final := by
  induction a with
  | invalid level bits base physical view hl aligned present kind prior =>
    exact .invalid level bits base physical view hl (by rw [← entryAddress_page h]; exact aligned)
      (by rw [← entryAddress_page h]; exact present) kind prior
  | leaf level bits base physical view hl aligned present kind prior =>
    have e := entryAddress_page h base level bits
    have aligned' : entryAddress base va' level bits % 8 = 0 := by rw [← e]; exact aligned
    have present' : observe (entryAddress base va' level bits) physical view := by rw [← e]; exact present
    have gen : ∀ (s : Nat) (hs : entryAddress base va' level bits = s)
        (q : Path observe paBits va' level bits base (.leaf level s physical view)),
        PathPermissionAnnotation observe paBits va' controls q prior [] prior := by
      intro s hs q
      subst hs
      exact .leaf level bits base physical view hl aligned' present' kind prior
    exact gen _ e.symm _
  | range level bits base physical view hl aligned present kind outOfRange prior =>
    exact .range level bits base physical view hl (by rw [← entryAddress_page h]; exact aligned)
      (by rw [← entryAddress_page h]; exact present) kind (by rw [← entryAddress_page h]; exact outOfRange) prior
  | table level bits base physical view endpoint hl aligned present kind inRange tail prior final words annotation ih =>
    exact .table level bits base physical view endpoint hl (by rw [← entryAddress_page h]; exact aligned)
      (by rw [← entryAddress_page h]; exact present) kind (by rw [← entryAddress_page h]; exact inRange)
      (path_page h tail) prior final words ih

/-- Transfer an access certificate to a same-page VA with an agreeing descriptor. The VA-range
fact for the new VA is a cheap per-VA decision supplied by the caller. -/
def S1AccessData.transferPage {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {va va' : BitVec 64}
    {r r' : S1LogicalReference.Request} {size size' : Int}
    (data : S1AccessData spec config rows ⟨va, r, size⟩) (same : SamePage va va')
    (agree : AccAgree r.raw r'.raw) (lower' : AArch64_GetVARange va' = .VARange_LOWER) :
    S1AccessData spec config rows ⟨va', r', size'⟩ where
  leafLevel := data.leafLevel
  logical := data.logical
  physical := data.physical
  view := data.view
  path := path_page same data.path
  permissions :=
    { row := data.permissions.row, member := data.permissions.member, slot := data.permissions.slot,
      words := data.permissions.words, annotation := annotation_page same data.permissions.annotation,
      used := data.permissions.used, rowView := data.permissions.rowView,
      attributes := data.permissions.attributes,
      kind := data.permissions.kind.trans agree.acctype,
      read := data.permissions.read.trans agree.read,
      write := data.permissions.write.trans agree.write,
      tagaccess := data.permissions.tagaccess.trans agree.tagaccess }
  lower := lower'
  accessEL := agree.el ▸ data.accessEL
  nonsecure := agree.ss ▸ data.nonsecure

/-- **TopologyImageSpec keyed by PAGE**: every query whose VA lies in a declared query's page. -/
noncomputable def specOfChecksPage (params : S1TTWParams) (physicalConfig : PhysicalConfig)
    (controls : S1LogicalReference.Controls) (layout : S1LogicalReference.Layout)
    (logicalRows : List LogicalRow) (imageRows : List ImageRow) (queries : List AccessQuery) (fuel : Nat)
    (rowsOK : checkSpecRows logicalRows imageRows = true)
    (queriesOK : queries.all (checkSpecQuery physicalConfig layout logicalRows imageRows fuel) = true) :
    TopologyImageSpec (fun q => ∃ q0 ∈ queries, SamePage q0.va q.va) :=
  let base := specOfChecks params physicalConfig controls layout logicalRows imageRows queries fuel rowsOK queriesOK
  { base with
    rootBound := by
      rintro q ⟨q0, member, same⟩
      rw [← entryAddress_page same]; exact base.rootBound q0 member
    paths := by
      rintro q ⟨q0, member, same⟩
      obtain ⟨level, logical, physical, view, path, used⟩ := base.paths q0 member
      exact ⟨level, logical, physical, view, path_page same path, used⟩ }

#print axioms path_page
#print axioms annotation_page
#print axioms S1AccessData.transferPage
end ArmCertWalk
