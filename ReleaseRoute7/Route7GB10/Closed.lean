import Route7GB10.World
import ReleaseProfile.GB10.ModelEntry
import ReleaseProfile.GB10.SpecWitness
import ReleaseProfile.GB10.ClosedPages
import ReleaseProfile.GB10.HeapImages
import ArmCertWalk.AccessDataBuilder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! # Runtime C2 closed membership, route B (generated; after Xlate HeapClosedB). Speed mode: compiles. -/

namespace Route7GB10.Closed

open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10

def classicTP (prior : S1LogicalReference.TablePermissions) (d : BitVec 64) : S1LogicalReference.TablePermissions :=
  { ap := prior.ap ||| d.extractLsb' 61 2, pxn := prior.pxn || d.getLsbD 59, uxn := prior.uxn || d.getLsbD 60 }

theorem tp_classic (c : S1LogicalReference.Controls) (hpd : c.hpd = false) (pie : c.pie = false)
    (nv1 : S1LogicalReference.nv1Mode c = false) : S1LogicalReference.tablePermissions c = classicTP := by
  funext prior d
  simp only [S1LogicalReference.tablePermissions, hpd, pie, nv1, Bool.false_or, Bool.false_eq_true, ite_false]
  rfl

structure WorldSpec {domain : QueryDomain} (spec : TopologyImageSpec domain) : Prop where
  lr : spec.logicalRows = Route7GB10.World.logicalRows
  ir : spec.imageRows = Route7GB10.World.imageRows
  lay : spec.layout = Route7GB10.World.layout
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
    (lr : spec.logicalRows = Route7GB10.World.logicalRows) (ir : spec.imageRows = Route7GB10.World.imageRows)
    (lay : spec.layout = Route7GB10.World.layout) : WorldSpec spec := by
  obtain ⟨ha, hd, pie, tbi, tbid, nfd, e0pd, mtx, txsz, cpie, chpd⟩ := sourceSpec_walkLiterals rho caller sspec d
  exact ⟨lr, ir, lay, sspec.physical.trans (sourcePhysical_eq rho caller), ha, hd, pie, tbi, tbid, nfd, e0pd, mtx, txsz,
    tp_classic _ chpd cpie (nv1Mode_el20 _ sspec.regime)⟩

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

noncomputable def rep_fetch400000 (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) Route7GB10.World.permissionRows Route7GB10.World.queries FetchShape where
  query := Route7GB10.World.fetch400000Query
  member := by simp [Route7GB10.World.queries]
  level := 3
  view := Route7GB10.World.viewOf 0x200000801007c3#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) Route7GB10.World.permissionRows
    Route7GB10.World.fetch400000Query 4 3 2147500032 { paspace := .PAS_NonSecure, address := 0x80004000#56 }
    (Route7GB10.World.viewOf 0x200000801007c3#64) (by walk_ok) Route7GB10.World.fetch400000Row
    (by simp [Route7GB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_srcRead (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) Route7GB10.World.permissionRows Route7GB10.World.queries (DataShape false) where
  query := Route7GB10.World.srcReadQuery
  member := by simp [Route7GB10.World.queries]
  level := 3
  view := Route7GB10.World.viewOf 0x68000080600743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) Route7GB10.World.permissionRows
    Route7GB10.World.srcReadQuery 4 3 2147496320 { paspace := .PAS_NonSecure, address := 0x80003180#56 }
    (Route7GB10.World.viewOf 0x68000080600743#64) (by walk_ok) Route7GB10.World.srcReadRow
    (by simp [Route7GB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_srcWrite (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) Route7GB10.World.permissionRows Route7GB10.World.queries (DataShape true) where
  query := Route7GB10.World.srcWriteQuery
  member := by simp [Route7GB10.World.queries]
  level := 3
  view := Route7GB10.World.viewOf 0x68000080600743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) Route7GB10.World.permissionRows
    Route7GB10.World.srcWriteQuery 4 3 2147496320 { paspace := .PAS_NonSecure, address := 0x80003180#56 }
    (Route7GB10.World.viewOf 0x68000080600743#64) (by walk_ok) Route7GB10.World.srcWriteRow
    (by simp [Route7GB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_dstRead (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) Route7GB10.World.permissionRows Route7GB10.World.queries (DataShape false) where
  query := Route7GB10.World.dstReadQuery
  member := by simp [Route7GB10.World.queries]
  level := 3
  view := Route7GB10.World.viewOf 0x68000080601743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) Route7GB10.World.permissionRows
    Route7GB10.World.dstReadQuery 4 3 2147496328 { paspace := .PAS_NonSecure, address := 0x80003188#56 }
    (Route7GB10.World.viewOf 0x68000080601743#64) (by walk_ok) Route7GB10.World.dstReadRow
    (by simp [Route7GB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_dstWrite (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) Route7GB10.World.permissionRows Route7GB10.World.queries (DataShape true) where
  query := Route7GB10.World.dstWriteQuery
  member := by simp [Route7GB10.World.queries]
  level := 3
  view := Route7GB10.World.viewOf 0x68000080601743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) Route7GB10.World.permissionRows
    Route7GB10.World.dstWriteQuery 4 3 2147496328 { paspace := .PAS_NonSecure, address := 0x80003188#56 }
    (Route7GB10.World.viewOf 0x68000080601743#64) (by walk_ok) Route7GB10.World.dstWriteRow
    (by simp [Route7GB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

end reps

section repEq
variable {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho} {domain : QueryDomain}
  {spec : TopologyImageSpec domain} (w : WorldSpec spec)
theorem rq_fetch400000 : (rep_fetch400000 (rho := rho) (caller := caller) w).query = Route7GB10.World.fetch400000Query := rfl
theorem rl_fetch400000 : (rep_fetch400000 (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_srcRead : (rep_srcRead (rho := rho) (caller := caller) w).query = Route7GB10.World.srcReadQuery := rfl
theorem rl_srcRead : (rep_srcRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_srcWrite : (rep_srcWrite (rho := rho) (caller := caller) w).query = Route7GB10.World.srcWriteQuery := rfl
theorem rl_srcWrite : (rep_srcWrite (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_dstRead : (rep_dstRead (rho := rho) (caller := caller) w).query = Route7GB10.World.dstReadQuery := rfl
theorem rl_dstRead : (rep_dstRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_dstWrite : (rep_dstWrite (rho := rho) (caller := caller) w).query = Route7GB10.World.dstWriteQuery := rfl
theorem rl_dstWrite : (rep_dstWrite (rho := rho) (caller := caller) w).level = 3 := rfl
end repEq

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

theorem worldRegs_before {R : Regs} {tcr sctlr : BitVec 64} (r : WorldRegs R tcr sctlr) :
    WorldRegs (beforeFetchRegs R) tcr sctlr :=
  ⟨r.ttbr0, r.ttbr1, r.httbr, r.tcrW, r.sctlrW, r.f227, r.f81, r.f101, r.bbm, r.epd0, r.icache, r.dcache⟩

set_option hygiene false in
macro "acc_ok" : tactic => `(tactic| (
  simp only [ClosedPages.accessOK, ClosedPages.repOK, List.any_cons, List.any_nil]
  repeat (first | rw [rq_fetch400000 w] | rw [rq_srcRead w] | rw [rq_srcWrite w] | rw [rq_dstRead w] | rw [rq_dstWrite w] | rw [rl_fetch400000 w] | rw [rl_srcRead w] | rw [rl_srcWrite w] | rw [rl_dstRead w] | rw [rl_dstWrite w])
  dsimp only [rep_fetch400000, rep_srcRead, rep_srcWrite, rep_dstRead, rep_dstWrite]
  simp only [Bool.or_false, ClosedPages.checkAt, checkCurrentLayout, checkTranslateQuery, checkLeafMap, checkOutputCache,
    OutputCacheAdmissible, currentWalkEPD, selectedRootTTBR, currentTTBR0, sourceTmeFault, sourceVectorFault,
    sourceE0PDFault, blockFaultValue, currentICache, currentDCache, rootStartLevel, rootBaseValue, rootTableSize,
    ArmFull.Functions.AArch64_VAIsOutOfRange, w.lay, w.txsz, w.tbi, w.tbid, w.mtx, w.e0pd, w.nfd, w.phys,
    r.ttbr0, r.ttbr1, r.httbr, r.tcrW, r.sctlrW, r.f227, r.f81, r.f101, r.bbm, r.epd0, r.icache, r.dcache]
  generalize ArmFull.Functions._get_TCR_EL2_Type_EPD1 tcr = e1
  revert e1
  decide +kernel))

end Route7GB10.Closed
