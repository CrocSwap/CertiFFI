import RuntimeGB10C2World
import ReleaseProfile.GB10.ClosedPages
import ReleaseProfile.GB10.HeapImages
import ReleaseProfile.RuntimeGB10.WorldStatics
import ArmCertWalk.AccessDataBuilder
import R14GuardWitness.Inputs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! # Runtime C2 closed membership, route B (generated; after Translate HeapClosedB). Speed mode: compiles. -/

namespace ReleaseProfile.GB10.RuntimeClosed

open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10 ReleaseProfile.GB10.Runtime

def classicTP (prior : S1LogicalReference.TablePermissions) (d : BitVec 64) : S1LogicalReference.TablePermissions :=
  { ap := prior.ap ||| d.extractLsb' 61 2, pxn := prior.pxn || d.getLsbD 59, uxn := prior.uxn || d.getLsbD 60 }

theorem tp_classic (c : S1LogicalReference.Controls) (hpd : c.hpd = false) (pie : c.pie = false)
    (nv1 : S1LogicalReference.nv1Mode c = false) : S1LogicalReference.tablePermissions c = classicTP := by
  funext prior d
  simp only [S1LogicalReference.tablePermissions, hpd, pie, nv1, Bool.false_or, Bool.false_eq_true, ite_false]
  rfl

structure WorldSpec {domain : QueryDomain} (spec : TopologyImageSpec domain) : Prop where
  lr : spec.logicalRows = ReleaseProfile.RuntimeGB10.World.logicalRows
  ir : spec.imageRows = ReleaseProfile.RuntimeGB10.World.imageRows
  lay : spec.layout = ReleaseProfile.RuntimeGB10.World.layout
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
    (lr : spec.logicalRows = ReleaseProfile.RuntimeGB10.World.logicalRows) (ir : spec.imageRows = ReleaseProfile.RuntimeGB10.World.imageRows)
    (lay : spec.layout = ReleaseProfile.RuntimeGB10.World.layout) : WorldSpec spec := by
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

noncomputable def rep_fetch2b6000 (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries FetchShape where
  query := ReleaseProfile.RuntimeGB10.World.fetch2b6000Query
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x200000803b67c3#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.fetch2b6000Query 4 3 2147501488 { paspace := .PAS_NonSecure, address := 0x800045b0#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x200000803b67c3#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.fetch2b6000Row
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_fetch2ba000 (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries FetchShape where
  query := ReleaseProfile.RuntimeGB10.World.fetch2ba000Query
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x200000803ba7c3#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.fetch2ba000Query 4 3 2147501520 { paspace := .PAS_NonSecure, address := 0x800045d0#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x200000803ba7c3#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.fetch2ba000Row
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_fetch391000 (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries FetchShape where
  query := ReleaseProfile.RuntimeGB10.World.fetch391000Query
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x200000804917c3#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.fetch391000Query 4 3 2147503240 { paspace := .PAS_NonSecure, address := 0x80004c88#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x200000804917c3#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.fetch391000Row
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_x1objRead (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape false) where
  query := ReleaseProfile.RuntimeGB10.World.x1objReadQuery
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080600743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.x1objReadQuery 4 3 2147496320 { paspace := .PAS_NonSecure, address := 0x80003180#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080600743#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.x1objReadRow
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_x1objWrite (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape true) where
  query := ReleaseProfile.RuntimeGB10.World.x1objWriteQuery
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080600743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.x1objWriteQuery 4 3 2147496320 { paspace := .PAS_NonSecure, address := 0x80003180#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080600743#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.x1objWriteRow
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_x0objRead (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape false) where
  query := ReleaseProfile.RuntimeGB10.World.x0objReadQuery
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080601743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.x0objReadQuery 4 3 2147496328 { paspace := .PAS_NonSecure, address := 0x80003188#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080601743#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.x0objReadRow
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_x0objWrite (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape true) where
  query := ReleaseProfile.RuntimeGB10.World.x0objWriteQuery
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080601743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.x0objWriteQuery 4 3 2147496328 { paspace := .PAS_NonSecure, address := 0x80003188#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080601743#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.x0objWriteRow
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_payloadRead (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape false) where
  query := ReleaseProfile.RuntimeGB10.World.payloadReadQuery
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080602743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.payloadReadQuery 4 3 2147496336 { paspace := .PAS_NonSecure, address := 0x80003190#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080602743#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.payloadReadRow
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_payloadWrite (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape true) where
  query := ReleaseProfile.RuntimeGB10.World.payloadWriteQuery
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080602743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.payloadWriteQuery 4 3 2147496336 { paspace := .PAS_NonSecure, address := 0x80003190#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080602743#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.payloadWriteRow
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_x19objRead (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape false) where
  query := ReleaseProfile.RuntimeGB10.World.x19objReadQuery
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080604743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.x19objReadQuery 4 3 2147496344 { paspace := .PAS_NonSecure, address := 0x80003198#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080604743#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.x19objReadRow
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_x19objWrite (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape true) where
  query := ReleaseProfile.RuntimeGB10.World.x19objWriteQuery
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080604743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.x19objWriteQuery 4 3 2147496344 { paspace := .PAS_NonSecure, address := 0x80003198#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080604743#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.x19objWriteRow
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_stackRead (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape false) where
  query := ReleaseProfile.RuntimeGB10.World.stackReadQuery
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080603743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.stackReadQuery 4 3 2147500024 { paspace := .PAS_NonSecure, address := 0x80003ff8#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080603743#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.stackReadRow
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

noncomputable def rep_stackWrite (w : WorldSpec spec) :
    ClosedPages.Representative spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows ReleaseProfile.RuntimeGB10.World.queries (DataShape true) where
  query := ReleaseProfile.RuntimeGB10.World.stackWriteQuery
  member := by simp [ReleaseProfile.RuntimeGB10.World.queries]
  level := 3
  view := ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080603743#64
  data := accessDataOfWalk spec (sourceAttributes rho caller) ReleaseProfile.RuntimeGB10.World.permissionRows
    ReleaseProfile.RuntimeGB10.World.stackWriteQuery 4 3 2147500024 { paspace := .PAS_NonSecure, address := 0x80003ff8#56 }
    (ReleaseProfile.RuntimeGB10.World.viewOf 0x68000080603743#64) (by walk_ok) ReleaseProfile.RuntimeGB10.World.stackWriteRow
    (by simp [ReleaseProfile.RuntimeGB10.World.permissionRows]) (by row_ok) rfl rfl rfl rfl
  leafLevel := rfl
  leafView := rfl
  shaped := by constructor <;> rfl

end reps

section repEq
variable {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho} {domain : QueryDomain}
  {spec : TopologyImageSpec domain} (w : WorldSpec spec)
theorem rq_fetch2b6000 : (rep_fetch2b6000 (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.fetch2b6000Query := rfl
theorem rl_fetch2b6000 : (rep_fetch2b6000 (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_fetch2ba000 : (rep_fetch2ba000 (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.fetch2ba000Query := rfl
theorem rl_fetch2ba000 : (rep_fetch2ba000 (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_fetch391000 : (rep_fetch391000 (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.fetch391000Query := rfl
theorem rl_fetch391000 : (rep_fetch391000 (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_x1objRead : (rep_x1objRead (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.x1objReadQuery := rfl
theorem rl_x1objRead : (rep_x1objRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_x1objWrite : (rep_x1objWrite (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.x1objWriteQuery := rfl
theorem rl_x1objWrite : (rep_x1objWrite (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_x0objRead : (rep_x0objRead (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.x0objReadQuery := rfl
theorem rl_x0objRead : (rep_x0objRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_x0objWrite : (rep_x0objWrite (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.x0objWriteQuery := rfl
theorem rl_x0objWrite : (rep_x0objWrite (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_payloadRead : (rep_payloadRead (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.payloadReadQuery := rfl
theorem rl_payloadRead : (rep_payloadRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_payloadWrite : (rep_payloadWrite (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.payloadWriteQuery := rfl
theorem rl_payloadWrite : (rep_payloadWrite (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_x19objRead : (rep_x19objRead (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.x19objReadQuery := rfl
theorem rl_x19objRead : (rep_x19objRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_x19objWrite : (rep_x19objWrite (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.x19objWriteQuery := rfl
theorem rl_x19objWrite : (rep_x19objWrite (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_stackRead : (rep_stackRead (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.stackReadQuery := rfl
theorem rl_stackRead : (rep_stackRead (rho := rho) (caller := caller) w).level = 3 := rfl
theorem rq_stackWrite : (rep_stackWrite (rho := rho) (caller := caller) w).query = ReleaseProfile.RuntimeGB10.World.stackWriteQuery := rfl
theorem rl_stackWrite : (rep_stackWrite (rho := rho) (caller := caller) w).level = 3 := rfl
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
  repeat (first | rw [rq_fetch2b6000 w] | rw [rq_fetch2ba000 w] | rw [rq_fetch391000 w] | rw [rq_x1objRead w] | rw [rq_x1objWrite w] | rw [rq_x0objRead w] | rw [rq_x0objWrite w] | rw [rq_payloadRead w] | rw [rq_payloadWrite w] | rw [rq_x19objRead w] | rw [rq_x19objWrite w] | rw [rq_stackRead w] | rw [rq_stackWrite w] | rw [rl_fetch2b6000 w] | rw [rl_fetch2ba000 w] | rw [rl_fetch391000 w] | rw [rl_x1objRead w] | rw [rl_x1objWrite w] | rw [rl_x0objRead w] | rw [rl_x0objWrite w] | rw [rl_payloadRead w] | rw [rl_payloadWrite w] | rw [rl_x19objRead w] | rw [rl_x19objWrite w] | rw [rl_stackRead w] | rw [rl_stackWrite w])
  dsimp only [rep_fetch2b6000, rep_fetch2ba000, rep_fetch391000, rep_x1objRead, rep_x1objWrite, rep_x0objRead, rep_x0objWrite, rep_payloadRead, rep_payloadWrite, rep_x19objRead, rep_x19objWrite, rep_stackRead, rep_stackWrite]
  simp only [Bool.or_false, ClosedPages.checkAt, checkCurrentLayout, checkTranslateQuery, checkLeafMap, checkOutputCache,
    OutputCacheAdmissible, currentWalkEPD, selectedRootTTBR, currentTTBR0, sourceTmeFault, sourceVectorFault,
    sourceE0PDFault, blockFaultValue, currentICache, currentDCache, rootStartLevel, rootBaseValue, rootTableSize,
    ArmFull.Functions.AArch64_VAIsOutOfRange, w.lay, w.txsz, w.tbi, w.tbid, w.mtx, w.e0pd, w.nfd, w.phys,
    r.ttbr0, r.ttbr1, r.httbr, r.tcrW, r.sctlrW, r.f227, r.f81, r.f101, r.bbm, r.epd0, r.icache, r.dcache]
  generalize ArmFull.Functions._get_TCR_EL2_Type_EPD1 tcr = e1
  revert e1
  decide +kernel))

end ReleaseProfile.GB10.RuntimeClosed
