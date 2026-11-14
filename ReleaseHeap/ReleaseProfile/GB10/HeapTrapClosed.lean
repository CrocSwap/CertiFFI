import ReleaseProfile.GB10.HeapVariantStatics
import ReleaseProfile.GB10.HeapTrapWorld

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Heap trap worlds: closed membership, gate-safe route B

`HeapClosedB` at the trap tables (normal + page 0) and the trap worlds `HeapTrapWorld.world t`: ten
representatives (the eight normal ones and VA page 0 read/write) at the source-pinned spec, walk checks at
the world entry's source registers by rewrite + decide (TCR_EL2.EPD1 quantified), for every t : Fin 6.
-/

namespace ReleaseProfile.GB10.HeapTrapClosed

open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10 ReleaseProfile.GB10.Heap
open ReleaseProfile.GB10.HeapClosedB (classicTP tp_classic WorldRegs worldRegs_before)

structure TrapSpec {domain : QueryDomain} (spec : TopologyImageSpec domain) : Prop where
  lr : spec.logicalRows = HeapTrapTables.logicalRows
  ir : spec.imageRows = HeapTrapTables.imageRows
  lay : spec.layout = HeapWorldTables.layout
  phys : spec.physicalConfig = gb10Physical
  ha : spec.params.ha = 1#1
  hd : spec.params.hd = 1#1
  pie : spec.params.pie = 0#1
  tbi : spec.params.tbi = 1#1
  tbid : spec.params.tbid = 0#1
  nfd : spec.params.nfd = 0#1
  e0pd : spec.params.e0pd = 0#1
  mtx : spec.params.mtx = 0#1
  txsz : spec.params.txsz = 16#6
  tp : S1LogicalReference.tablePermissions spec.controls = classicTP

theorem trapSpec_of_source {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    {domain : QueryDomain} {spec : TopologyImageSpec domain} (sspec : SourceSpec rho caller spec) (d : DataPart)
    (lr : spec.logicalRows = HeapTrapTables.logicalRows) (ir : spec.imageRows = HeapTrapTables.imageRows)
    (lay : spec.layout = HeapWorldTables.layout) : TrapSpec spec := by
  obtain ⟨ha, hd, pie, tbi, tbid, nfd, e0pd, mtx, txsz, cpie, chpd⟩ := sourceSpec_walkLiterals rho caller sspec d
  exact ⟨lr, ir, lay, sspec.physical.trans (sourcePhysical_eq rho caller), ha, hd, pie, tbi, tbid, nfd, e0pd, mtx, txsz,
    tp_classic _ chpd cpie (nv1Mode_el20 _ sspec.regime)⟩

/-! ## Representatives at the source-pinned world spec -/

section reps

variable {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
  {domain : QueryDomain} {spec : TopologyImageSpec domain}

set_option hygiene false in
macro "trow_ok" : tactic => `(tactic| (
  simp only [permissionRowB, checkPermissionRowAttributes, selectedAttribute, w.lr, w.ir, w.lay, w.phys, w.tp,
    w.pie, w.ha, w.hd, w.mtx, sourceAttributes_mair]
  decide))

set_option hygiene false in
macro "twalk_ok" : tactic => `(tactic| (rw [w.lr, w.phys, w.lay]; rfl))

noncomputable def trep_fetch (w : TrapSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
      HeapTrapTables.queries FetchShape where
  query := HeapWorldTables.fetchQuery
  member := by simp [HeapTrapTables.queries, HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x200000801107c3#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
    HeapWorldTables.fetchQuery 4 3 2147500160 { paspace := .PAS_NonSecure, address := 0x80004080#56 }
    (HeapWorldTables.viewOf 0x200000801107c3#64) (by twalk_ok) HeapWorldTables.fetchRow
    (by simp [HeapTrapTables.permissionRows, HeapWorldTables.permissionRows]) (by trow_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def trep_dataRead (w : TrapSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
      HeapTrapTables.queries (DataShape false) where
  query := HeapWorldTables.dataReadQuery
  member := by simp [HeapTrapTables.queries, HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080120743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
    HeapWorldTables.dataReadQuery 4 3 2147500288 { paspace := .PAS_NonSecure, address := 0x80004100#56 }
    (HeapWorldTables.viewOf 0x68000080120743#64) (by twalk_ok) HeapWorldTables.dataReadRow
    (by simp [HeapTrapTables.permissionRows, HeapWorldTables.permissionRows]) (by trow_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def trep_inputRead (w : TrapSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
      HeapTrapTables.queries (DataShape false) where
  query := HeapWorldTables.inputReadQuery
  member := by simp [HeapTrapTables.queries, HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080130743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
    HeapWorldTables.inputReadQuery 4 3 2147496320 { paspace := .PAS_NonSecure, address := 0x80003180#56 }
    (HeapWorldTables.viewOf 0x68000080130743#64) (by twalk_ok) HeapWorldTables.inputReadRow
    (by simp [HeapTrapTables.permissionRows, HeapWorldTables.permissionRows]) (by trow_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def trep_outputWrite (w : TrapSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
      HeapTrapTables.queries (DataShape true) where
  query := HeapWorldTables.outputWriteQuery
  member := by simp [HeapTrapTables.queries, HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080131743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
    HeapWorldTables.outputWriteQuery 4 3 2147496328 { paspace := .PAS_NonSecure, address := 0x80003188#56 }
    (HeapWorldTables.viewOf 0x68000080131743#64) (by twalk_ok) HeapWorldTables.outputWriteRow
    (by simp [HeapTrapTables.permissionRows, HeapWorldTables.permissionRows]) (by trow_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def trep_stackWrite (w : TrapSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
      HeapTrapTables.queries (DataShape true) where
  query := HeapWorldTables.stackWriteQuery
  member := by simp [HeapTrapTables.queries, HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x680000801ff743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
    HeapWorldTables.stackWriteQuery 4 3 2147500024 { paspace := .PAS_NonSecure, address := 0x80003ff8#56 }
    (HeapWorldTables.viewOf 0x680000801ff743#64) (by twalk_ok) HeapWorldTables.stackWriteRow
    (by simp [HeapTrapTables.permissionRows, HeapWorldTables.permissionRows]) (by trow_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def trep_stackRead (w : TrapSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
      HeapTrapTables.queries (DataShape false) where
  query := HeapWorldTables.stackReadQuery
  member := by simp [HeapTrapTables.queries, HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x680000801ff743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
    HeapWorldTables.stackReadQuery 4 3 2147500024 { paspace := .PAS_NonSecure, address := 0x80003ff8#56 }
    (HeapWorldTables.viewOf 0x680000801ff743#64) (by twalk_ok) HeapWorldTables.stackReadRow
    (by simp [HeapTrapTables.permissionRows, HeapWorldTables.permissionRows]) (by trow_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def trep_shimFrameWrite (w : TrapSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
      HeapTrapTables.queries (DataShape true) where
  query := HeapWorldTables.shimFrameWriteQuery
  member := by simp [HeapTrapTables.queries, HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080200743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
    HeapWorldTables.shimFrameWriteQuery 4 3 2147504128 { paspace := .PAS_NonSecure, address := 0x80005000#56 }
    (HeapWorldTables.viewOf 0x68000080200743#64) (by twalk_ok) HeapWorldTables.shimFrameWriteRow
    (by simp [HeapTrapTables.permissionRows, HeapWorldTables.permissionRows]) (by trow_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def trep_shimFrameRead (w : TrapSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
      HeapTrapTables.queries (DataShape false) where
  query := HeapWorldTables.shimFrameReadQuery
  member := by simp [HeapTrapTables.queries, HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080200743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
    HeapWorldTables.shimFrameReadQuery 4 3 2147504128 { paspace := .PAS_NonSecure, address := 0x80005000#56 }
    (HeapWorldTables.viewOf 0x68000080200743#64) (by twalk_ok) HeapWorldTables.shimFrameReadRow
    (by simp [HeapTrapTables.permissionRows, HeapWorldTables.permissionRows]) (by trow_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def trep_zeroRead (w : TrapSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
      HeapTrapTables.queries (DataShape false) where
  query := HeapTrapTables.zeroReadQuery
  member := by simp [HeapTrapTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080300743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
    HeapTrapTables.zeroReadQuery 4 3 2147495936 { paspace := .PAS_NonSecure, address := 0x80003000#56 }
    (HeapWorldTables.viewOf 0x68000080300743#64) (by twalk_ok) HeapTrapTables.zeroReadRow
    (by simp [HeapTrapTables.permissionRows]) (by trow_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def trep_zeroWrite (w : TrapSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
      HeapTrapTables.queries (DataShape true) where
  query := HeapTrapTables.zeroWriteQuery
  member := by simp [HeapTrapTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080300743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapTrapTables.permissionRows
    HeapTrapTables.zeroWriteQuery 4 3 2147495936 { paspace := .PAS_NonSecure, address := 0x80003000#56 }
    (HeapWorldTables.viewOf 0x68000080300743#64) (by twalk_ok) HeapTrapTables.zeroWriteRow
    (by simp [HeapTrapTables.permissionRows]) (by trow_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

end reps

section repEq
variable {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho} {domain : QueryDomain}
  {spec : TopologyImageSpec domain} (w : TrapSpec spec)
theorem trq_fetch : (trep_fetch (rho := rho) (caller := caller) w).query = HeapWorldTables.fetchQuery := rfl
theorem trl_fetch : (trep_fetch (rho := rho) (caller := caller) w).level = 3 := rfl
theorem trq_dataRead : (trep_dataRead (rho := rho) (caller := caller) w).query = HeapWorldTables.dataReadQuery := rfl
theorem trl_dataRead : (trep_dataRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem trq_inputRead : (trep_inputRead (rho := rho) (caller := caller) w).query = HeapWorldTables.inputReadQuery := rfl
theorem trl_inputRead : (trep_inputRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem trq_outputWrite : (trep_outputWrite (rho := rho) (caller := caller) w).query = HeapWorldTables.outputWriteQuery := rfl
theorem trl_outputWrite : (trep_outputWrite (rho := rho) (caller := caller) w).level = 3 := rfl
theorem trq_stackWrite : (trep_stackWrite (rho := rho) (caller := caller) w).query = HeapWorldTables.stackWriteQuery := rfl
theorem trl_stackWrite : (trep_stackWrite (rho := rho) (caller := caller) w).level = 3 := rfl
theorem trq_stackRead : (trep_stackRead (rho := rho) (caller := caller) w).query = HeapWorldTables.stackReadQuery := rfl
theorem trl_stackRead : (trep_stackRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem trq_shimFrameWrite : (trep_shimFrameWrite (rho := rho) (caller := caller) w).query = HeapWorldTables.shimFrameWriteQuery := rfl
theorem trl_shimFrameWrite : (trep_shimFrameWrite (rho := rho) (caller := caller) w).level = 3 := rfl
theorem trq_shimFrameRead : (trep_shimFrameRead (rho := rho) (caller := caller) w).query = HeapWorldTables.shimFrameReadQuery := rfl
theorem trl_shimFrameRead : (trep_shimFrameRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem trq_zeroRead : (trep_zeroRead (rho := rho) (caller := caller) w).query = HeapTrapTables.zeroReadQuery := rfl
theorem trl_zeroRead : (trep_zeroRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem trq_zeroWrite : (trep_zeroWrite (rho := rho) (caller := caller) w).query = HeapTrapTables.zeroWriteQuery := rfl
theorem trl_zeroWrite : (trep_zeroWrite (rho := rho) (caller := caller) w).level = 3 := rfl
end repEq

set_option hygiene false in
macro "tacc_ok" : tactic => `(tactic| (
  simp only [ClosedPages.accessOK, ClosedPages.repOK, List.any_cons, List.any_nil]
  repeat (first | rw [trq_fetch w] | rw [trq_dataRead w] | rw [trq_inputRead w] | rw [trq_outputWrite w] | rw [trq_stackWrite w] | rw [trq_stackRead w] | rw [trq_shimFrameWrite w] | rw [trq_shimFrameRead w] | rw [trl_fetch w] | rw [trl_dataRead w] | rw [trl_inputRead w] | rw [trl_outputWrite w] | rw [trl_stackWrite w] | rw [trl_stackRead w] | rw [trl_shimFrameWrite w] | rw [trl_shimFrameRead w] | rw [trq_zeroRead w] | rw [trq_zeroWrite w] | rw [trl_zeroRead w] | rw [trl_zeroWrite w])
  dsimp only [trep_fetch, trep_dataRead, trep_inputRead, trep_outputWrite, trep_stackWrite, trep_stackRead, trep_shimFrameWrite,
    trep_shimFrameRead, trep_zeroRead, trep_zeroWrite]
  simp only [Bool.or_false, ClosedPages.checkAt, checkCurrentLayout, checkTranslateQuery, checkLeafMap, checkOutputCache,
    OutputCacheAdmissible, currentWalkEPD, selectedRootTTBR, currentTTBR0, sourceTmeFault, sourceVectorFault,
    sourceE0PDFault, blockFaultValue, currentICache, currentDCache, rootStartLevel, rootBaseValue, rootTableSize,
    ArmFull.Functions.AArch64_VAIsOutOfRange, w.lay, w.txsz, w.tbi, w.tbid, w.mtx, w.e0pd, w.nfd, w.phys,
    r.ttbr0, r.ttbr1, r.httbr, r.tcrW, r.sctlrW, r.f227, r.f81, r.f101, r.bbm, r.epd0, r.icache, r.dcache]
  generalize ArmFull.Functions._get_TCR_EL2_Type_EPD1 tcr = e1
  revert e1
  decide +kernel))


set_option hygiene false in
macro "tacc_ok_t" : tactic => `(tactic| (
  simp only [ClosedPages.accessOK, ClosedPages.repOK, List.any_cons, List.any_nil]
  repeat (first | rw [trq_fetch w] | rw [trq_dataRead w] | rw [trq_inputRead w] | rw [trq_outputWrite w] | rw [trq_stackWrite w] | rw [trq_stackRead w] | rw [trq_shimFrameWrite w] | rw [trq_shimFrameRead w] | rw [trl_fetch w] | rw [trl_dataRead w] | rw [trl_inputRead w] | rw [trl_outputWrite w] | rw [trl_stackWrite w] | rw [trl_stackRead w] | rw [trl_shimFrameWrite w] | rw [trl_shimFrameRead w] | rw [trq_zeroRead w] | rw [trq_zeroWrite w] | rw [trl_zeroRead w] | rw [trl_zeroWrite w])
  dsimp only [trep_fetch, trep_dataRead, trep_inputRead, trep_outputWrite, trep_stackWrite, trep_stackRead, trep_shimFrameWrite,
    trep_shimFrameRead, trep_zeroRead, trep_zeroWrite]
  simp only [Bool.or_false, ClosedPages.checkAt, checkCurrentLayout, checkTranslateQuery, checkLeafMap, checkOutputCache,
    OutputCacheAdmissible, currentWalkEPD, selectedRootTTBR, currentTTBR0, sourceTmeFault, sourceVectorFault,
    sourceE0PDFault, blockFaultValue, currentICache, currentDCache, rootStartLevel, rootBaseValue, rootTableSize,
    ArmFull.Functions.AArch64_VAIsOutOfRange, w.lay, w.txsz, w.tbi, w.tbid, w.mtx, w.e0pd, w.nfd, w.phys,
    r.ttbr0, r.ttbr1, r.httbr, r.tcrW, r.sctlrW, r.f227, r.f81, r.f101, r.bbm, r.epd0, r.icache, r.dcache]
  generalize ArmFull.Functions._get_TCR_EL2_Type_EPD1 tcr = e1
  revert e1
  revert t
  decide +kernel))



/-- Closed membership at any state with the world register reads, at trap world `t`. -/
theorem closed_at_regs_trap {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho} {domain : QueryDomain}
    {spec : TopologyImageSpec domain} (w : TrapSpec spec)
    (hdom : ∀ q : AccessQuery, (∃ q0 ∈ HeapTrapTables.queries, SamePage q0.va q.va) → domain q)
    (t : HeapTrapWorld.T) (state : ArmCertWalk.State) {tcr sctlr : BitVec 64} (r : WorldRegs state.regs tcr sctlr) :
    ClosedMembershipAt spec (sourceAttributes rho caller) (HeapTrapWorld.world t).rows (HeapTrapWorld.world t).mapping
      (ArmBridge.CruxGenGuarded.Release.shimMap spec (HeapTrapWorld.world t).mapping (HeapTrapWorld.world t).base
        (HeapTrapWorld.world t).pins) state := by
  refine ClosedPages.ClosedPagesAt.closed (ClosedPages.closed_pages_shim spec (sourceAttributes rho caller)
    HeapTrapTables.permissionRows HeapTrapWorld.mapping
    [trep_dataRead w, trep_inputRead w, trep_stackRead w, trep_shimFrameRead w, trep_zeroRead w]
    [trep_outputWrite w, trep_stackWrite w, trep_shimFrameWrite w, trep_zeroWrite w] [trep_fetch w]
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> rfl)
    hdom _ (HeapTrapWorld.pins t) HeapTrapWorld.base.toNat _ ?_ ?_ ?_ ?_ ?_ state rfl)
  · tacc_ok_t
  · tacc_ok
  · tacc_ok
  · tacc_ok_t
  · tacc_ok_t

/-- Atom 122 (`inv0_closed`) at trap world `t`'s entry. -/
theorem a122 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (t : HeapTrapWorld.T) (pcount : BitVec 88)
    {specCaller : AdmissibleCaller rho}
    {spec : TopologyImageSpec (fun q => ∃ q0 ∈ HeapTrapTables.queries, SamePage q0.va q.va)}
    (sspec : SourceSpec rho specCaller spec) (hlay : spec.layout = HeapTrapTables.tables.layout)
    (hlr : spec.logicalRows = HeapTrapTables.tables.logicalRows)
    (hir : spec.imageRows = HeapTrapTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/closed"
      (ClosedMembershipAt spec (sourceAttributes rho caller) (HeapTrapWorld.world t).rows (HeapTrapWorld.world t).mapping
        (ArmBridge.CruxGenGuarded.Release.shimMap spec (HeapTrapWorld.world t).mapping (HeapTrapWorld.world t).base
          (HeapTrapWorld.world t).pins)
        (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller (HeapTrapWorld.world t) pcount))) :=
  ⟨closed_at_regs_trap (trapSpec_of_source sspec HeapWorldData.data hlr hir hlay) (fun _ h => h) t _
    (worldRegs_before (Heap.VariantStatics.worldRegs_of_data worldSemantics rho caller (HeapTrapWorld.world t) pcount
      rfl rfl rfl))⟩

end ReleaseProfile.GB10.HeapTrapClosed

#print axioms ReleaseProfile.GB10.HeapTrapClosed.closed_at_regs_trap
#print axioms ReleaseProfile.GB10.HeapTrapClosed.a122
