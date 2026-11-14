-- (1b): per-access certificates transfer between access descriptors that agree on every
-- field the certificate checks read. The actual IFETCH descriptor's oracle-varying fields
-- (NewAccDesc occ 769: modop, cacheop, opscope, cachetype, toplevel, varange) are not among them,
-- so one evaluated representative per code PC covers every ActualIFetchAcc variant.
import ArmCertWalk.SpecBuilder
import ArmCertWalk.NativeFetchTotal
open Sail ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

/-- Agreement on every descriptor field read by S1AccessData / CurrentS1AccessAt. -/
structure AccAgree (a b : AccessDescriptor) : Prop where
  acctype : a.acctype = b.acctype
  el : a.el = b.el
  ss : a.ss = b.ss
  read : a.read = b.read
  write : a.write = b.write
  tagaccess : a.tagaccess = b.tagaccess
  transactional : a.transactional = b.transactional
  nonfault : a.nonfault = b.nonfault
  contiguous : a.contiguous = b.contiguous
  firstfault : a.firstfault = b.firstfault
  first : a.first = b.first
  ls64 : a.ls64 = b.ls64

/-- Transfer an access certificate to a query with the same VA and an agreeing descriptor. -/
def S1AccessData.transfer {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {va : BitVec 64}
    {r r' : S1LogicalReference.Request} {size size' : Int}
    (data : S1AccessData spec config rows ⟨va, r, size⟩) (agree : AccAgree r.raw r'.raw) :
    S1AccessData spec config rows ⟨va, r', size'⟩ where
  leafLevel := data.leafLevel
  logical := data.logical
  physical := data.physical
  view := data.view
  path := data.path
  permissions :=
    { row := data.permissions.row, member := data.permissions.member, slot := data.permissions.slot,
      words := data.permissions.words, annotation := data.permissions.annotation,
      used := data.permissions.used, rowView := data.permissions.rowView,
      attributes := data.permissions.attributes,
      kind := data.permissions.kind.trans agree.acctype,
      read := data.permissions.read.trans agree.read,
      write := data.permissions.write.trans agree.write,
      tagaccess := data.permissions.tagaccess.trans agree.tagaccess }
  lower := data.lower
  accessEL := agree.el ▸ data.accessEL
  nonsecure := agree.ss ▸ data.nonsecure

theorem translate_query_checks_transfer {regs : Regs} {params : S1TTWParams} {va : BitVec 64}
    {a b : AccessDescriptor} (agree : AccAgree a b) (checks : TranslateQueryChecks regs params va a) :
    TranslateQueryChecks regs params va b := by
  obtain ⟨vaOK, e0pd, tme, vector⟩ := checks
  refine ⟨agree.acctype ▸ vaOK, ?_, ?_, ?_⟩
  · simpa only [sourceE0PDFault, agree.el] using e0pd
  · simpa only [sourceTmeFault, agree.el, agree.transactional] using tme
  · simpa only [sourceVectorFault, agree.el, agree.nonfault, agree.contiguous, agree.firstfault, agree.first]
      using vector

theorem output_cache_transfer {regs : Regs} {a b : AccessDescriptor} (agree : AccAgree a b)
    (policy : OutputCacheAdmissible a regs) : OutputCacheAdmissible b regs := by
  unfold OutputCacheAdmissible at policy ⊢
  rw [← agree.ls64, ← agree.acctype]
  exact policy

theorem CurrentS1AccessAt.transfer {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {va : BitVec 64} {r r' : S1LogicalReference.Request} {size size' : Int}
    {data : S1AccessData spec config rows ⟨va, r, size⟩} {state : State}
    (current : CurrentS1AccessAt spec config rows mapping ⟨va, r, size⟩ data state)
    (agree : AccAgree r.raw r'.raw) :
    CurrentS1AccessAt spec config rows mapping ⟨va, r', size'⟩ (ArmCertWalk.S1AccessData.transfer (size' := size') data agree) state := by
  obtain ⟨layout, checks, epd, map, output⟩ := current
  exact ⟨layout, translate_query_checks_transfer agree checks, epd,
    ⟨map.mapped, map.admissible⟩, output_cache_transfer agree output⟩

/-- **TopologyImageSpec keyed by VA**: every query whose VA is a declared query's VA is in the
domain (paths and rootBound depend only on the VA), e.g. all ActualIFetchAcc variants at a PC. -/
noncomputable def specOfChecksVA (params : S1TTWParams) (physicalConfig : PhysicalConfig)
    (controls : S1LogicalReference.Controls) (layout : S1LogicalReference.Layout)
    (logicalRows : List LogicalRow) (imageRows : List ImageRow) (queries : List AccessQuery) (fuel : Nat)
    (rowsOK : checkSpecRows logicalRows imageRows = true)
    (queriesOK : queries.all (checkSpecQuery physicalConfig layout logicalRows imageRows fuel) = true) :
    TopologyImageSpec (fun q => ∃ q0 ∈ queries, q.va = q0.va) :=
  let base := specOfChecks params physicalConfig controls layout logicalRows imageRows queries fuel rowsOK queriesOK
  { base with
    rootBound := by
      rintro q ⟨q0, member, va⟩
      rw [va]; exact base.rootBound q0 member
    paths := by
      rintro q ⟨q0, member, va⟩
      rw [va]; exact base.paths q0 member }

#print axioms S1AccessData.transfer
#print axioms CurrentS1AccessAt.transfer
/-- Register-independent fields of an actual IFETCH descriptor (NewAccDesc constants). -/
theorem actual_ifetch_flags {s : State} {acc : AccessDescriptor} (h : ActualIFetchAcc s acc) :
    acc.acctype = .AccessType_IFETCH ∧ acc.read = false ∧ acc.write = false ∧ acc.tagaccess = false ∧
      acc.transactional = false ∧ acc.nonfault = false ∧ acc.contiguous = false ∧ acc.firstfault = false ∧
      acc.first = false ∧ acc.ls64 = false := by
  obtain ⟨t0, u0, _, call⟩ := h
  unfold CreateAccDescIFetch NewAccDesc at call
  simp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure] at call
  repeat (split at call <;> try (simp at call; done))
  simp only [EStateM.Result.ok.injEq] at call
  obtain ⟨rfl, _⟩ := call
  simp

/-- Two actual IFETCH descriptors (any oracle draw) agree on every certificate-read field once
their EL and security state agree (both are register-determined; callers have el = EL0, ss = NS). -/
theorem actual_ifetch_agree {s s' : State} {a b : AccessDescriptor}
    (ha : ActualIFetchAcc s a) (hb : ActualIFetchAcc s' b) (el : a.el = b.el) (ss : a.ss = b.ss) :
    AccAgree a b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := actual_ifetch_flags ha
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := actual_ifetch_flags hb
  exact ⟨a1.trans b1.symm, el, ss, a2.trans b2.symm, a3.trans b3.symm, a4.trans b4.symm, a5.trans b5.symm,
    a6.trans b6.symm, a7.trans b7.symm, a8.trans b8.symm, a9.trans b9.symm, a10.trans b10.symm⟩

#print axioms actual_ifetch_agree
end ArmCertWalk
