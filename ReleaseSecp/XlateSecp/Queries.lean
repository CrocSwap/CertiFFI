import XlateSecp.Images
import XlateSecp.Topology

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Secp a124 (CheckedEntry.checkQueries) at the source-built entry, route B (Translate; speed mode)

HeapClosedB's gate-safe route at the secp World: configuration reads are rewritten to their declared literals
(`sourceSpec_walkLiterals`, `sourcePhysical`, `sourceAttributes_mair`, `nv1Mode_el20`, feature and TCR_EL2/SCTLR_EL2
bit facts, payload TTBRs/HTTBR); the rest (World tables, the card's queries) is decided. No register file, params,
controls or attribute configuration is constructed.
-/

namespace XlateSecp.Queries

open Sail ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft
open ReleaseProfile.MachineSource ReleaseProfile.GB10 TranslateSpan TranslateSpan.SecpRawDeployment XlateSecp.Topology

/-- Classic (non-HPD, non-PIE, non-NV1) table-permission accumulation: a function of descriptor data only. -/
def classicTP (prior : S1LogicalReference.TablePermissions) (d : BitVec 64) : S1LogicalReference.TablePermissions :=
  { ap := prior.ap ||| d.extractLsb' 61 2, pxn := prior.pxn || d.getLsbD 59, uxn := prior.uxn || d.getLsbD 60 }

theorem tp_classic (c : S1LogicalReference.Controls) (hpd : c.hpd = false) (pie : c.pie = false)
    (nv1 : S1LogicalReference.nv1Mode c = false) : S1LogicalReference.tablePermissions c = classicTP := by
  funext prior d
  simp only [S1LogicalReference.tablePermissions, hpd, pie, nv1, Bool.false_or, Bool.false_eq_true, ite_false]
  rfl

/-- The facts a source-pinned secp spec provides, as rewrite lemmas. -/
structure WorldSpec {domain : QueryDomain} (spec : TopologyImageSpec domain) : Prop where
  lr : spec.logicalRows = World.logicalRows
  ir : spec.imageRows = World.imageRows
  lay : spec.layout = World.layout
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

theorem worldSpec_of_raw (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) (o : OracleChoice)
    (addrs : List (BitVec 64)) (h : CheckedTopology.check (Raw.Ro sem rho caller c pcount o) addrs 4 = true) (d : DataPart) :
    WorldSpec (CheckedTopology.spec (Raw.Ro sem rho caller c pcount o) addrs 4 h) := by
  have sspec := Raw.Ro_source sem rho caller c pcount o addrs h
  obtain ⟨ha, hd, pie, tbi, tbid, nfd, e0pd, mtx, txsz, cpie, chpd⟩ := sourceSpec_walkLiterals rho caller sspec d
  exact ⟨rfl, rfl, rfl, sourcePhysical_eq rho caller, ha, hd, pie, tbi, tbid, nfd, e0pd, mtx, txsz,
    tp_classic _ chpd cpie (nv1Mode_el20 _ sspec.regime)⟩

/-- Register reads of the World entry (source regs with the payload TTBRs/HTTBR). -/
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
    (c : World.Card) (pcount : BitVec 88) :
    WorldRegs (World.entry sem rho caller c pcount).regs
      (controlWord rho.val caller.caller .TCR_EL2) (controlWord rho.val caller.caller .SCTLR_EL2) := by
  have hd : (World.entry sem rho caller c pcount).regs = sourceRegs rho caller (World.payload c pcount).data := rfl
  rw [hd]
  refine ⟨rfl, rfl, (show sourceBank64 rho caller (World.payload c pcount).data .HTTBR = _ from by
      rw [sourceBank64_entry rho caller _ .HTTBR (by decide)]; rfl),
    sourceRegs_bank64 rho caller _ .TCR_EL2, sourceRegs_bank64 rho caller _ .SCTLR_EL2,
    sourceRegs_feature rho caller _ 227 (by decide) false _ rfl,
    sourceRegs_feature rho caller _ 81 (by decide) true _ rfl,
    sourceRegs_feature rho caller _ 101 (by decide) true _ rfl, rfl, ?_, ?_, ?_⟩
  · bit1 .TCR_EL2 7 false
  · bit1 .SCTLR_EL2 12 true
  · bit1 .SCTLR_EL2 2 true

theorem worldRegs_before {R : Regs} {tcr sctlr : BitVec 64} (r : WorldRegs R tcr sctlr) :
    WorldRegs (beforeFetchRegs R) tcr sctlr :=
  ⟨r.ttbr0, r.ttbr1, r.httbr, r.tcrW, r.sctlrW, r.f227, r.f81, r.f101, r.bbm, r.epd0, r.icache, r.dcache⟩

theorem queries_eq (p : Plan) (base : BitVec 64) (e : NativeState) : queries p base e = queriesG p base e.regs.gpr := rfl

-- a124 at any spec/registers with the World facts: rewrite every configuration read, decide the rest.
set_option hygiene false in
macro "a124_tac" : tactic => `(tactic| (
  simp only [CheckedEntry.checkQueries, StaticData.checkData, CheckedEntry.checkCurrentFromWalk, checkCurrentLayout,
    checkTranslateQuery, checkLeafMap, checkOutputCache, StaticData.permissionCandidate, permissionRowB,
    checkPermissionRowAttributes, selectedAttribute, OutputCacheAdmissible, currentWalkEPD, selectedRootTTBR,
    currentTTBR0, sourceTmeFault, sourceVectorFault, sourceE0PDFault, blockFaultValue, currentICache, currentDCache,
    rootStartLevel, rootBaseValue, rootTableSize, ArmFull.Functions.AArch64_VAIsOutOfRange,
    w.lr, w.ir, w.lay, w.phys, w.tp, w.ha, w.hd, w.pie, w.tbi, w.tbid, w.nfd, w.e0pd, w.mtx, w.txsz,
    sourceAttributes_mair, r.ttbr0, r.ttbr1, r.httbr, r.tcrW, r.sctlrW, r.f227, r.f81, r.f101, r.bbm, r.epd0,
    r.icache, r.dcache]
  generalize ArmFull.Functions._get_TCR_EL2_Type_EPD1 tcr = e1
  revert e1
  decide +kernel))

/-- The closed per-card check (decided per card in `QueriesAll`). -/
def ClosedAt (p : Plan) (c : World.Card) : Prop :=
  ∀ (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) {domain : QueryDomain}
    {spec : TopologyImageSpec domain}, WorldSpec spec → ∀ {R : Regs} {tcr sctlr : BitVec 64}, WorldRegs R tcr sctlr →
    ∀ e : ArmCertWalk.State, e.regs = R →
    CheckedEntry.checkQueries spec (sourceAttributes rho caller) World.permissionRows World.mapping 1030
      (queriesG p World.base (World.data c).gpr) 4 e = true

/-- a124 for a card from its closed check, at the source-pinned raw and the World entry. -/
theorem a124_of (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) (p : Plan) (closed : ClosedAt p c) {o : OracleChoice} :
    ∀ (checkedTopology : CheckedTopology.check (Raw.Ro sem rho caller c pcount o)
        (addresses p World.base (World.entry sem rho caller c pcount)) 4 = true),
      CheckedEntry.checkQueries (CheckedTopology.spec (Raw.Ro sem rho caller c pcount o)
          (addresses p World.base (World.entry sem rho caller c pcount)) 4 checkedTopology)
        (sourceAttributes rho caller) World.permissionRows World.mapping 1030
        (queries p World.base (World.entry sem rho caller c pcount)) 4
        (ArmBridge.CruxGenGuarded.beforeFetchState (World.entry sem rho caller c pcount)) = true := by
  intro h
  rw [queries_eq, entry_gpr]
  exact closed rho caller (worldSpec_of_raw sem rho caller c pcount o _ h (World.payload c pcount).data)
    (worldRegs_before (worldRegs_of_source sem rho caller c pcount)) _ (beforeFetch_regs _)

end XlateSecp.Queries

#print axioms XlateSecp.Queries.a124_of
