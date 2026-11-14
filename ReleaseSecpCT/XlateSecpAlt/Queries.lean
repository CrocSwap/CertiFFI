import XlateSecpAlt.Images
import XlateSecpAlt.Topology
import XlateSecp.Queries

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

namespace XlateSecpAlt.Queries

open Sail ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ArmBridge.Draft
open ReleaseProfile.MachineSource ReleaseProfile.GB10 TranslateSpan TranslateSpan.SecpRawDeployment XlateSecpAlt.Topology

theorem worldSpec_of_raw (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) (o : OracleChoice)
    (addrs : List (BitVec 64)) (h : CheckedTopology.check (XlateSecpAlt.Raw.Ro sem rho caller c pcount o) addrs 4 = true) (d : DataPart) :
    XlateSecp.Queries.WorldSpec (CheckedTopology.spec (XlateSecpAlt.Raw.Ro sem rho caller c pcount o) addrs 4 h) := by
  have sspec := XlateSecpAlt.Raw.Ro_source sem rho caller c pcount o addrs h
  obtain ⟨ha, hd, pie, tbi, tbid, nfd, e0pd, mtx, txsz, cpie, chpd⟩ := sourceSpec_walkLiterals rho caller sspec d
  exact ⟨rfl, rfl, rfl, sourcePhysical_eq rho caller, ha, hd, pie, tbi, tbid, nfd, e0pd, mtx, txsz,
    XlateSecp.Queries.tp_classic _ chpd cpie (nv1Mode_el20 _ sspec.regime)⟩

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
    (c : XlateSecp.World.Card) (pcount : BitVec 88) :
    XlateSecp.Queries.WorldRegs (XlateSecpAlt.World.entry sem rho caller c pcount).regs
      (controlWord rho.val caller.caller .TCR_EL2) (controlWord rho.val caller.caller .SCTLR_EL2) := by
  have hd : (XlateSecpAlt.World.entry sem rho caller c pcount).regs = sourceRegs rho caller (XlateSecpAlt.World.payload c pcount).data := rfl
  rw [hd]
  refine ⟨rfl, rfl, (show sourceBank64 rho caller (XlateSecpAlt.World.payload c pcount).data .HTTBR = _ from by
      rw [sourceBank64_entry rho caller _ .HTTBR (by decide)]; rfl),
    sourceRegs_bank64 rho caller _ .TCR_EL2, sourceRegs_bank64 rho caller _ .SCTLR_EL2,
    sourceRegs_feature rho caller _ 227 (by decide) false _ rfl,
    sourceRegs_feature rho caller _ 81 (by decide) true _ rfl,
    sourceRegs_feature rho caller _ 101 (by decide) true _ rfl, rfl, ?_, ?_, ?_⟩
  · bit1 .TCR_EL2 7 false
  · bit1 .SCTLR_EL2 12 true
  · bit1 .SCTLR_EL2 2 true

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

/-- a124 for a card from its closed check, at the source-pinned raw and the World entry. -/
theorem a124_of (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) (p : Plan) (closed : XlateSecp.Queries.ClosedAt p c) {o : OracleChoice} :
    ∀ (checkedTopology : CheckedTopology.check (XlateSecpAlt.Raw.Ro sem rho caller c pcount o)
        (addresses p XlateSecp.World.base (XlateSecpAlt.World.entry sem rho caller c pcount)) 4 = true),
      CheckedEntry.checkQueries (CheckedTopology.spec (XlateSecpAlt.Raw.Ro sem rho caller c pcount o)
          (addresses p XlateSecp.World.base (XlateSecpAlt.World.entry sem rho caller c pcount)) 4 checkedTopology)
        (sourceAttributes rho caller) XlateSecp.World.permissionRows XlateSecp.World.mapping 1030
        (queries p XlateSecp.World.base (XlateSecpAlt.World.entry sem rho caller c pcount)) 4
        (ArmBridge.CruxGenGuarded.beforeFetchState (XlateSecpAlt.World.entry sem rho caller c pcount)) = true := by
  intro h
  rw [XlateSecp.Queries.queries_eq, entry_gpr]
  exact closed rho caller (worldSpec_of_raw sem rho caller c pcount o _ h (XlateSecpAlt.World.payload c pcount).data)
    (XlateSecp.Queries.worldRegs_before (worldRegs_of_source sem rho caller c pcount)) _ (beforeFetch_regs _)

end XlateSecpAlt.Queries

#print axioms XlateSecpAlt.Queries.a124_of
