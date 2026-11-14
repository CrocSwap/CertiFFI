import ReleaseProfile.GB10.HeapWorldData
import ReleaseProfile.GB10.HeapStaticAtoms
import ReleaseProfile.GB10.ClosedPagesShim
import ArmCertWalk.AccessDataBuilder
import ReleaseProfile.GB10.HeapImages

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Heap C2 closed membership, gate-safe route B

Everything is stated at source-pinned world spec (`sourceSpec_of_tables HeapWorldTables.tables`) and
the world entry's source registers. Configuration reads are rewritten to their declared literals
(`sourceSpec_walkLiterals`, `sourcePhysical_eq`, `sourceAttributes_mair`, `nv1Mode_el20`, feature and
TCR_EL2 bit facts, payload TTBRs); the remaining program/table data is decided. No register file, params,
controls or attribute configuration is constructed.
-/

namespace ReleaseProfile.GB10.HeapClosedB

open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10 ReleaseProfile.GB10.Heap

/-- Classic (non-HPD, non-PIE, non-NV1) table-permission accumulation: a function of descriptor data only. -/
def classicTP (prior : S1LogicalReference.TablePermissions) (d : BitVec 64) : S1LogicalReference.TablePermissions :=
  { ap := prior.ap ||| d.extractLsb' 61 2, pxn := prior.pxn || d.getLsbD 59, uxn := prior.uxn || d.getLsbD 60 }

theorem tp_classic (c : S1LogicalReference.Controls) (hpd : c.hpd = false) (pie : c.pie = false)
    (nv1 : S1LogicalReference.nv1Mode c = false) : S1LogicalReference.tablePermissions c = classicTP := by
  funext prior d
  simp only [S1LogicalReference.tablePermissions, hpd, pie, nv1, Bool.false_or, Bool.false_eq_true, ite_false]
  rfl

/-- The facts a source-pinned world spec provides, as rewrite lemmas. -/
structure WorldSpec {domain : QueryDomain} (spec : TopologyImageSpec domain) : Prop where
  lr : spec.logicalRows = HeapWorldTables.logicalRows
  ir : spec.imageRows = HeapWorldTables.imageRows
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

theorem worldSpec_of_source {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    {domain : QueryDomain} {spec : TopologyImageSpec domain} (sspec : SourceSpec rho caller spec) (d : DataPart)
    (lr : spec.logicalRows = HeapWorldTables.logicalRows) (ir : spec.imageRows = HeapWorldTables.imageRows)
    (lay : spec.layout = HeapWorldTables.layout) : WorldSpec spec := by
  obtain ⟨ha, hd, pie, tbi, tbid, nfd, e0pd, mtx, txsz, cpie, chpd⟩ := sourceSpec_walkLiterals rho caller sspec d
  exact ⟨lr, ir, lay, sspec.physical.trans (sourcePhysical_eq rho caller), ha, hd, pie, tbi, tbid, nfd, e0pd, mtx, txsz,
    tp_classic _ chpd cpie (nv1Mode_el20 _ sspec.regime)⟩

/-! ## Prototype: the fetch representative's row check at the world spec -/

theorem fetch_row {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho} {domain : QueryDomain}
    {spec : TopologyImageSpec domain} (w : WorldSpec spec) :
    permissionRowB spec (sourceAttributes rho caller) HeapWorldTables.fetchQuery
      { paspace := .PAS_NonSecure, address := 0x80004080#56 } (HeapWorldTables.viewOf HeapWorldTables.fetchRow.raw)
      (walkWords spec.logicalRows (effectiveBits spec.physicalConfig).toNat HeapWorldTables.fetchQuery.va 4
        spec.layout.start (S1LogicalReference.rootBits spec.layout.start spec.layout.inputBits) spec.layout.root)
      HeapWorldTables.fetchRow = true := by
  simp only [permissionRowB, checkPermissionRowAttributes, selectedAttribute, w.lr, w.ir, w.lay, w.phys, w.tp,
    w.pie, w.ha, w.hd, w.mtx, sourceAttributes_mair]
  decide

/-! ## Representatives at the source-pinned world spec -/

section reps

variable {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
  {domain : QueryDomain} {spec : TopologyImageSpec domain}

set_option hygiene false in
macro "row_ok" : tactic => `(tactic| (
  simp only [permissionRowB, checkPermissionRowAttributes, selectedAttribute, w.lr, w.ir, w.lay, w.phys, w.tp,
    w.pie, w.ha, w.hd, w.mtx, sourceAttributes_mair]
  decide))

set_option hygiene false in
macro "walk_ok" : tactic => `(tactic| (rw [w.lr, w.phys, w.lay]; rfl))

noncomputable def rep_fetch (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
      HeapWorldTables.queries FetchShape where
  query := HeapWorldTables.fetchQuery
  member := by simp [HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x200000801107c3#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
    HeapWorldTables.fetchQuery 4 3 2147500160 { paspace := .PAS_NonSecure, address := 0x80004080#56 }
    (HeapWorldTables.viewOf 0x200000801107c3#64) (by walk_ok) HeapWorldTables.fetchRow
    (by simp [HeapWorldTables.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_dataRead (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
      HeapWorldTables.queries (DataShape false) where
  query := HeapWorldTables.dataReadQuery
  member := by simp [HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080120743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
    HeapWorldTables.dataReadQuery 4 3 2147500288 { paspace := .PAS_NonSecure, address := 0x80004100#56 }
    (HeapWorldTables.viewOf 0x68000080120743#64) (by walk_ok) HeapWorldTables.dataReadRow
    (by simp [HeapWorldTables.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_inputRead (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
      HeapWorldTables.queries (DataShape false) where
  query := HeapWorldTables.inputReadQuery
  member := by simp [HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080130743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
    HeapWorldTables.inputReadQuery 4 3 2147496320 { paspace := .PAS_NonSecure, address := 0x80003180#56 }
    (HeapWorldTables.viewOf 0x68000080130743#64) (by walk_ok) HeapWorldTables.inputReadRow
    (by simp [HeapWorldTables.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_outputWrite (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
      HeapWorldTables.queries (DataShape true) where
  query := HeapWorldTables.outputWriteQuery
  member := by simp [HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080131743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
    HeapWorldTables.outputWriteQuery 4 3 2147496328 { paspace := .PAS_NonSecure, address := 0x80003188#56 }
    (HeapWorldTables.viewOf 0x68000080131743#64) (by walk_ok) HeapWorldTables.outputWriteRow
    (by simp [HeapWorldTables.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_stackWrite (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
      HeapWorldTables.queries (DataShape true) where
  query := HeapWorldTables.stackWriteQuery
  member := by simp [HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x680000801ff743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
    HeapWorldTables.stackWriteQuery 4 3 2147500024 { paspace := .PAS_NonSecure, address := 0x80003ff8#56 }
    (HeapWorldTables.viewOf 0x680000801ff743#64) (by walk_ok) HeapWorldTables.stackWriteRow
    (by simp [HeapWorldTables.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_stackRead (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
      HeapWorldTables.queries (DataShape false) where
  query := HeapWorldTables.stackReadQuery
  member := by simp [HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x680000801ff743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
    HeapWorldTables.stackReadQuery 4 3 2147500024 { paspace := .PAS_NonSecure, address := 0x80003ff8#56 }
    (HeapWorldTables.viewOf 0x680000801ff743#64) (by walk_ok) HeapWorldTables.stackReadRow
    (by simp [HeapWorldTables.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_shimFrameWrite (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
      HeapWorldTables.queries (DataShape true) where
  query := HeapWorldTables.shimFrameWriteQuery
  member := by simp [HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080200743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
    HeapWorldTables.shimFrameWriteQuery 4 3 2147504128 { paspace := .PAS_NonSecure, address := 0x80005000#56 }
    (HeapWorldTables.viewOf 0x68000080200743#64) (by walk_ok) HeapWorldTables.shimFrameWriteRow
    (by simp [HeapWorldTables.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_shimFrameRead (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
      HeapWorldTables.queries (DataShape false) where
  query := HeapWorldTables.shimFrameReadQuery
  member := by simp [HeapWorldTables.queries]
  level := 3
  view := HeapWorldTables.viewOf 0x68000080200743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) HeapWorldTables.permissionRows
    HeapWorldTables.shimFrameReadQuery 4 3 2147504128 { paspace := .PAS_NonSecure, address := 0x80005000#56 }
    (HeapWorldTables.viewOf 0x68000080200743#64) (by walk_ok) HeapWorldTables.shimFrameReadRow
    (by simp [HeapWorldTables.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

end reps

section repEq
variable {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho} {domain : QueryDomain}
  {spec : TopologyImageSpec domain} (w : WorldSpec spec)
theorem rq_fetch : (rep_fetch (rho := rho) (caller := caller) w).query = HeapWorldTables.fetchQuery := rfl
theorem rl_fetch : (rep_fetch (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_dataRead : (rep_dataRead (rho := rho) (caller := caller) w).query = HeapWorldTables.dataReadQuery := rfl
theorem rl_dataRead : (rep_dataRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_inputRead : (rep_inputRead (rho := rho) (caller := caller) w).query = HeapWorldTables.inputReadQuery := rfl
theorem rl_inputRead : (rep_inputRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_outputWrite : (rep_outputWrite (rho := rho) (caller := caller) w).query = HeapWorldTables.outputWriteQuery := rfl
theorem rl_outputWrite : (rep_outputWrite (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_stackWrite : (rep_stackWrite (rho := rho) (caller := caller) w).query = HeapWorldTables.stackWriteQuery := rfl
theorem rl_stackWrite : (rep_stackWrite (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_stackRead : (rep_stackRead (rho := rho) (caller := caller) w).query = HeapWorldTables.stackReadQuery := rfl
theorem rl_stackRead : (rep_stackRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_shimFrameWrite : (rep_shimFrameWrite (rho := rho) (caller := caller) w).query = HeapWorldTables.shimFrameWriteQuery := rfl
theorem rl_shimFrameWrite : (rep_shimFrameWrite (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_shimFrameRead : (rep_shimFrameRead (rho := rho) (caller := caller) w).query = HeapWorldTables.shimFrameReadQuery := rfl
theorem rl_shimFrameRead : (rep_shimFrameRead (rho := rho) (caller := caller) w).level = 3 := rfl
end repEq

/-! ## The world entry's register reads, as rewrite lemmas -/

/-- Register projections of the world entry the walk checks read. -/
structure WorldRegs (R : Regs) (tcr sctlr : BitVec 64) : Prop where
  ttbr0 : R.bank_BitVec_128 ._TTBR0_EL2 = 0x80000000#128
  ttbr1 : R.bank_BitVec_128 .TTBR1_EL2 = 0#128
  httbr : R.bank_BitVec_64 .HTTBR = 0x80000000#64
  tcrW : R.bank_BitVec_64 .TCR_EL2 = tcr
  sctlrW : R.bank_BitVec_64 .SCTLR_EL2 = sctlr
  f227 : R.FeatureImpl[227] = false
  f81 : R.FeatureImpl[81] = true
  f101 : R.FeatureImpl[101] = true
  bbm : R.bank_Int .__block_bbm_implemented = 2
  epd0 : ArmFull.Functions._get_TCR_EL2_Type_EPD0 tcr = 0#1
  icache : ArmFull.Functions._get_SCTLR_EL2_Type_I sctlr = 1#1
  dcache : ArmFull.Functions._get_SCTLR_EL2_Type_C sctlr = 1#1

set_option hygiene false in
macro "bit1 " key:term:max i:num v:term : tactic => `(tactic| (
  have hb := rho.property.construction.control64 caller.caller $key ⟨$i, by decide⟩ $v _ rfl rfl
  generalize controlWord rho.val caller.caller $key = w at hb ⊢
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [Sail.BitVec.extractLsb, ArmFull.Functions._get_TCR_EL2_Type_EPD0,
    ArmFull.Functions._get_SCTLR_EL2_Type_I, ArmFull.Functions._get_SCTLR_EL2_Type_C] at hj ⊢
  have : j = 0 := by omega
  subst this
  simpa [BitVec.getLsbD_eq_getElem] using hb))

theorem worldRegs_of_source (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (pcount : BitVec 88) :
    WorldRegs (worldEntry sem rho caller HeapWorldData.world pcount).regs
      (controlWord rho.val caller.caller .TCR_EL2) (controlWord rho.val caller.caller .SCTLR_EL2) := by
  have hd : (worldEntry sem rho caller HeapWorldData.world pcount).regs =
      sourceRegs rho caller { HeapWorldData.world.data with PhysicalCount := pcount } := rfl
  rw [hd]
  refine ⟨rfl, rfl, (show sourceBank64 rho caller { HeapWorldData.world.data with PhysicalCount := pcount } .HTTBR = _ from by
      unfold sourceBank64; simp only [↓reduceDIte]; rfl),
    sourceRegs_bank64 rho caller _ .TCR_EL2, sourceRegs_bank64 rho caller _ .SCTLR_EL2,
    sourceRegs_feature rho caller _ 227 (by decide) false _ rfl,
    sourceRegs_feature rho caller _ 81 (by decide) true _ rfl,
    sourceRegs_feature rho caller _ 101 (by decide) true _ rfl, rfl, ?_, ?_, ?_⟩
  · bit1 .TCR_EL2 7 false
  · bit1 .SCTLR_EL2 12 true
  · bit1 .SCTLR_EL2 2 true

/-! ## Prototype: the fetch representative's walk check at the world entry -/

theorem fetch_walk {domain : QueryDomain} {spec : TopologyImageSpec domain} (w : WorldSpec spec)
    {R : Regs} {tcr sctlr : BitVec 64} (r : WorldRegs R tcr sctlr) :
    ClosedPages.checkAt spec HeapWorldData.mapping HeapWorldTables.fetchQuery 3
      (HeapWorldTables.viewOf HeapWorldTables.fetchRow.raw) R = true := by
  simp only [ClosedPages.checkAt, checkCurrentLayout, checkTranslateQuery, checkLeafMap, checkOutputCache,
    OutputCacheAdmissible, currentWalkEPD, selectedRootTTBR, currentTTBR0, sourceTmeFault, sourceVectorFault,
    sourceE0PDFault, blockFaultValue, currentICache, currentDCache, rootStartLevel, rootBaseValue, rootTableSize,
    ArmFull.Functions.AArch64_VAIsOutOfRange, w.lay, w.txsz, w.tbi, w.tbid, w.mtx, w.e0pd, w.nfd, w.phys,
    r.ttbr0, r.ttbr1, r.httbr, r.tcrW, r.sctlrW, r.f227, r.f81, r.f101, r.bbm, r.epd0, r.icache, r.dcache]
  generalize ArmFull.Functions._get_TCR_EL2_Type_EPD1 tcr = e1
  revert e1
  decide

theorem worldRegs_before {R : Regs} {tcr sctlr : BitVec 64} (r : WorldRegs R tcr sctlr) :
    WorldRegs (beforeFetchRegs R) tcr sctlr :=
  ⟨r.ttbr0, r.ttbr1, r.httbr, r.tcrW, r.sctlrW, r.f227, r.f81, r.f101, r.bbm, r.epd0, r.icache, r.dcache⟩

/-! ## a122: closed membership at the world entry (route B) -/

set_option hygiene false in
macro "acc_ok" : tactic => `(tactic| (
  simp only [ClosedPages.accessOK, ClosedPages.repOK, List.any_cons, List.any_nil]
  repeat (first | rw [rq_fetch w] | rw [rq_dataRead w] | rw [rq_inputRead w] | rw [rq_outputWrite w] | rw [rq_stackWrite w] | rw [rq_stackRead w] | rw [rq_shimFrameWrite w] | rw [rq_shimFrameRead w] | rw [rl_fetch w] | rw [rl_dataRead w] | rw [rl_inputRead w] | rw [rl_outputWrite w] | rw [rl_stackWrite w] | rw [rl_stackRead w] | rw [rl_shimFrameWrite w] | rw [rl_shimFrameRead w])
  dsimp only [rep_fetch, rep_dataRead, rep_inputRead, rep_outputWrite, rep_stackWrite, rep_stackRead, rep_shimFrameWrite,
    rep_shimFrameRead]
  simp only [Bool.or_false, ClosedPages.checkAt, checkCurrentLayout, checkTranslateQuery, checkLeafMap, checkOutputCache,
    OutputCacheAdmissible, currentWalkEPD, selectedRootTTBR, currentTTBR0, sourceTmeFault, sourceVectorFault,
    sourceE0PDFault, blockFaultValue, currentICache, currentDCache, rootStartLevel, rootBaseValue, rootTableSize,
    ArmFull.Functions.AArch64_VAIsOutOfRange, w.lay, w.txsz, w.tbi, w.tbid, w.mtx, w.e0pd, w.nfd, w.phys,
    r.ttbr0, r.ttbr1, r.httbr, r.tcrW, r.sctlrW, r.f227, r.f81, r.f101, r.bbm, r.epd0, r.icache, r.dcache]
  generalize ArmFull.Functions._get_TCR_EL2_Type_EPD1 tcr = e1
  revert e1
  decide +kernel))

/-- Closed membership at any state whose register reads are the world's (source regs with the world TTBRs). -/
theorem closed_at_regs {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho} {domain : QueryDomain}
    {spec : TopologyImageSpec domain} (w : WorldSpec spec)
    (hdom : ∀ q : AccessQuery, (∃ q0 ∈ HeapWorldTables.queries, SamePage q0.va q.va) → domain q)
    (state : ArmCertWalk.State) {tcr sctlr : BitVec 64} (r : WorldRegs state.regs tcr sctlr) :
    ClosedMembershipAt spec (sourceAttributes rho caller) HeapWorldData.world.rows HeapWorldData.world.mapping
      (ArmBridge.CruxGenGuarded.Release.shimMap spec HeapWorldData.world.mapping HeapWorldData.world.base
        HeapWorldData.world.pins) state := by
  refine ClosedPages.ClosedPagesAt.closed (ClosedPages.closed_pages_shim spec (sourceAttributes rho caller)
    HeapWorldTables.permissionRows HeapWorldData.mapping
    [rep_dataRead w, rep_inputRead w, rep_stackRead w, rep_shimFrameRead w]
    [rep_outputWrite w, rep_stackWrite w, rep_shimFrameWrite w] [rep_fetch w]
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> rfl)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> rfl)
    hdom _ HeapWorldData.world.pins HeapWorldData.world.base.toNat _ ?_ ?_ ?_ ?_ ?_ state rfl)
  · acc_ok
  · acc_ok
  · acc_ok
  · acc_ok
  · acc_ok

theorem closed_world {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho} {domain : QueryDomain}
    {spec : TopologyImageSpec domain} (w : WorldSpec spec)
    (hdom : ∀ q : AccessQuery, (∃ q0 ∈ HeapWorldTables.queries, SamePage q0.va q.va) → domain q)
    (pcount : BitVec 88) :
    ClosedMembershipAt spec (sourceAttributes rho caller) HeapWorldData.world.rows HeapWorldData.world.mapping
      (ArmBridge.CruxGenGuarded.Release.shimMap spec HeapWorldData.world.mapping HeapWorldData.world.base
        HeapWorldData.world.pins)
      (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller HeapWorldData.world pcount)) := by
  exact closed_at_regs w hdom _
    (worldRegs_before (worldRegs_of_source worldSemantics rho caller pcount))

/-! ## ClosedAt fields (`Normal.ClosedAt`), at the tables' domain -/

section closedAt

variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (pcount : BitVec 88)
  {specCaller : AdmissibleCaller rho}
  {spec : TopologyImageSpec (fun q => ∃ q0 ∈ HeapWorldTables.queries, SamePage q0.va q.va)}

theorem worldSpec_tables (sspec : SourceSpec rho specCaller spec) (hlay : spec.layout = HeapWorldTables.tables.layout)
    (hlr : spec.logicalRows = HeapWorldTables.tables.logicalRows)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows) : WorldSpec spec :=
  worldSpec_of_source sspec HeapWorldData.data hlr hir hlay

theorem a122 (sspec : SourceSpec rho specCaller spec) (hlay : spec.layout = HeapWorldTables.tables.layout)
    (hlr : spec.logicalRows = HeapWorldTables.tables.logicalRows)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/closed"
      (ClosedMembershipAt spec (sourceAttributes rho caller) HeapWorldData.world.rows HeapWorldData.world.mapping
        (ArmBridge.CruxGenGuarded.Release.shimMap spec HeapWorldData.world.mapping HeapWorldData.world.base
          HeapWorldData.world.pins)
        (ArmBridge.CruxGenGuarded.beforeFetchState (worldEntry worldSemantics rho caller HeapWorldData.world pcount))) :=
  ⟨closed_world (worldSpec_tables rho sspec hlay hlr hir) (fun _ h => h) pcount⟩

theorem a272 (sspec : SourceSpec rho specCaller spec) (hlay : spec.layout = HeapWorldTables.tables.layout)
    (hlr : spec.logicalRows = HeapWorldTables.tables.logicalRows)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:default-functional-regions-injective"
      (ArmCertValue.HeapV2Mem.RegionsInjective HeapWorldData.world.pins HeapWorldData.world.mapping) :=
  ⟨Heap.Statics.atom273 HeapWorldData.world (a122 rho specCaller 0 sspec hlay hlr hir).1 (by unfold TranslateMem.RegionsDisjoint; decide) (by decide)
    (by unfold ArmCertValue.HeapV2Mem.DataBytesLinear; decide +kernel) (by decide +kernel)⟩

theorem a273 (sspec : SourceSpec rho specCaller spec) (hlay : spec.layout = HeapWorldTables.tables.layout)
    (hlr : spec.logicalRows = HeapWorldTables.tables.logicalRows)
    (hir : spec.imageRows = HeapWorldTables.tables.imageRows) :
    CertiFFI.Claim.DeploymentObligation "card:default-functional-input-slot-separation"
      (∀ (i : Nat), i < 32 → ∀ (n : Nat), HeapWorldData.world.mapping (BitVec.ofNat 64 (HeapWorldData.world.pins.x1 + i)) =
        some n → ¬RtShim2.ShimMem.slotBytes HeapWorldData.world.pins HeapWorldData.world.mapping n) :=
  ⟨Heap.Statics.atom274 HeapWorldData.world (a122 rho specCaller 0 sspec hlay hlr hir).1 (by unfold TranslateMem.RegionsDisjoint; decide) (by decide)
    (by unfold ArmCertValue.HeapV2Mem.DataBytesLinear; decide +kernel) (by decide +kernel) (by decide) (by decide)⟩

end closedAt

end ReleaseProfile.GB10.HeapClosedB

#print axioms ReleaseProfile.GB10.HeapClosedB.fetch_row
#print axioms ReleaseProfile.GB10.HeapClosedB.worldRegs_of_source
#print axioms ReleaseProfile.GB10.HeapClosedB.fetch_walk
#print axioms ReleaseProfile.GB10.HeapClosedB.closed_world
#print axioms ReleaseProfile.GB10.HeapClosedB.closed_at_regs
#print axioms ReleaseProfile.GB10.HeapClosedB.a122
#print axioms ReleaseProfile.GB10.HeapClosedB.a272
#print axioms ReleaseProfile.GB10.HeapClosedB.a273
