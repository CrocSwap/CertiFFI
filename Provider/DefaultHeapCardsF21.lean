-- F21 (CertiFFI,): card for normalP; ids for the new premises are PROPOSALS.
import HeapFinalLeaf
-- Proposed classifications require independent review before release admission.
import CertiFFIClaim.Premises
import DefaultHeapNormal
import DefaultHeapNormalP
import DefaultHeapShimCt
import DefaultHeapTrapInitial
import DefaultHeapTrapCt
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open HeapV2StepCerts NativeMteTagCheck CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.ValBind ReleaseProfile.DefaultHeapTrap
open HeapV2StepCerts.E17General RtDit.Release RtDit RtDit.Shim RtDit.Window RtDit.ShimEv
open ArmBridge.CruxGenGuarded.Release (shimPC shimMap)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ReleaseProfile.DefaultHeapCards
/-- Claim card for `ReleaseProfile.DefaultHeapShimFactory.normal`: its statement with every hypothesis typed by kind and registry id. -/
theorem card_normalP
    (real : Type)
    [Sail.SailReal real]
    {domain : QueryDomain}
    (spec : TopologyImageSpec domain)
    (config : AttributeConfig)
    (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins)
    (scope : Nat → Prop)
    (image : MemReloc.Image)
    (loadBase : MemReloc.Word)
    (base : BitVec 64)
    (offS : Nat → BitVec 64)
    (budget : Nat)
    (catalogue : ControlCatalogue)
    (e : NativeState)
    (room : CertiFFI.Claim.RunCheck "card:budget" ((357 + 12) ≤ budget))
    (aligned : CertiFFI.Claim.RunCheck "card:plan-offsets" (∀ j, (offS j).toNat % 4 = 0))
    (offPre : CertiFFI.Claim.RunCheck "card:plan-offsets" (∀ j, j ≤ 6 → offS j = shimPC j))
    (offPost : CertiFFI.Claim.RunCheck "card:plan-offsets" (∀ j, (357 + 8) ≤ j → j ≤ (357 + 11) → offS j = shimPC (j - (357 + 1))))
    (codeSlot : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ImageTableSeparated scope loadBase mapping (RtShim2.ShimMem.slotBytes pins mapping)))
    (inv0_v1_pins_f4 : CertiFFI.Claim.Premise "card:default-initial/v1/pins/f4" .trm (e.regs.FeatureImpl[4]! = true))
    (inv0_v1_pins_rme : CertiFFI.Claim.Premise "card:default-initial/v1/pins/rme" .trm (e.regs.FeatureImpl[232]! = false))
    (inv0_v1_pins_spe : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/spe" (e.regs.bank_Bool ArmFull.Bank_Bool.SPESampleInFlight = false))
    (inv0_v1_pins_el : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/el" (e.regs.PSTATE.EL = 0#2))
    (inv0_v1_pins_nrw : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/nrw" (e.regs.PSTATE.nRW = 0#1))
    (inv0_v1_pins_edecr : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/edecr" (ArmFull.Functions._get_EDECR_Type_RCE (e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.EDECR) = 0#1))
    (inv0_v1_pins_cti : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/cti" (ArmFull.Functions._get_CTIDEVCTL_Type_RCE (e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.CTIDEVCTL) = 0#1))
    (inv0_v1_pins_st : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/st" (ArmFull.Functions._get_EDSCR_Type_STATUS (e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) = 2#6))
    (inv0_v1_pins_edesr : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/edesr" (e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.EDESR = 0#32))
    (inv0_v1_pins_btt : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/btt" (e.regs.Branchtypetaken ≠ ArmFull.BranchType.BranchType_RESET))
    (inv0_v1_pins_emu : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/emu" (e.regs.__emulator_termination_opcode = none))
    (inv0_v1_pins_e2h : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/e2h" (ArmFull.Functions._get_HCR_EL2_Type_E2H (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
    (inv0_v1_pins_tge : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/tge" (ArmFull.Functions._get_HCR_EL2_Type_TGE (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
    (inv0_v1_pins_scrns : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/scrns" (ArmFull.Functions._get_SCR_EL3_Type_NS (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 1#1))
    (inv0_v1_pins_pmbe : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/pmbe" (ArmFull.Functions._get_PMBLIMITR_EL1_Type_E (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PMBLIMITR_EL1) = 0#1))
    (inv0_v1_pins_mdss : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/mdss" (ArmFull.Functions._get_MDSCR_EL1_Type_SS (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDSCR_EL1) = 0#1))
    (inv0_v1_pins_pmbs : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/pmbs" (Sail.BitVec.extractLsb (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PMBSR_EL1) 17 17 = 0#1))
    (inv0_v1_pins_da : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/da" (e.regs.PSTATE.A = 0#1))
    (inv0_v1_pins_di : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/di" (e.regs.PSTATE.I = 0#1))
    (inv0_v1_pins_df : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/df" (e.regs.PSTATE.F = 0#1))
    (inv0_v1_pins_il : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/il" (e.regs.PSTATE.IL = 0#1))
    (inv0_v1_pins_pss : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/pss" (e.regs.PSTATE.SS = 0#1))
    (inv0_v1_pins_btype : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/btype" (e.regs.PSTATE.BTYPE = 0#2))
    (inv0_v1_pins_btn : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pins/btn" (e.regs.BTypeNext = 0#2))
    (inv0_v1_features_a0 : CertiFFI.Claim.Premise "card:default-initial/v1/features/a0" .trm (e.regs.FeatureImpl[0]! = false))
    (inv0_v1_features_a1 : CertiFFI.Claim.Premise "card:default-initial/v1/features/a1" .trm (e.regs.FeatureImpl[1]! = false))
    (inv0_v1_features_a2 : CertiFFI.Claim.Premise "card:default-initial/v1/features/a2" .trm (e.regs.FeatureImpl[2]! = false))
    (inv0_v1_features_a3 : CertiFFI.Claim.Premise "card:default-initial/v1/features/a3" .trm (e.regs.FeatureImpl[3]! = false))
    (inv0_v1_features_b1 : CertiFFI.Claim.Premise "card:default-initial/v1/features/b1" .trm (e.regs.FeatureImpl[5]! = true))
    (inv0_v1_features_b2 : CertiFFI.Claim.Premise "card:default-initial/v1/features/b2" .trm (e.regs.FeatureImpl[6]! = true))
    (inv0_v1_features_b3 : CertiFFI.Claim.Premise "card:default-initial/v1/features/b3" .trm (e.regs.FeatureImpl[7]! = true))
    (inv0_v1_features_vhe : CertiFFI.Claim.Premise "card:default-initial/v1/features/vhe" .trm (e.regs.FeatureImpl[54]! = true))
    (inv0_v1_debug_mde : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/debug/mde" (ArmFull.Functions._get_MDSCR_EL1_Type_MDE (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDSCR_EL1) = 0#1))
    (inv0_v1_debug_hde : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/debug/hde" (ArmFull.Functions._get_EDSCR_Type_HDE (e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) = 0#1))
    (inv0_v1_current_images_covered : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/covered" (∀ (row : PermissionRow), row ∈ rows → row.slot ∈ (rowsFootprint spec.imageRows).slots))
    (inv0_v1_current_images_topology : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/topology" (TopologyImageAt spec (ArmBridge.CruxGenGuarded.beforeFetchState e)))
    (inv0_v1_current_images_attributes : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/attributes" (AttributeImage (rowsObserve spec.imageRows) config (ArmBridge.CruxGenGuarded.beforeFetchState e).mem))
    (inv0_v1_current_images_writeback : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/writeback" (WriteBackAttributeImage (rowsObserve spec.imageRows) config (ArmBridge.CruxGenGuarded.beforeFetchState e).mem))
    (inv0_v1_current_images_permissions : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/permissions" (PermissionImage rows spec.params (ArmBridge.CruxGenGuarded.beforeFetchState e).regs spec.controls
  (ArmBridge.CruxGenGuarded.beforeFetchState e).mem))
    (inv0_v1_current_host_regime_el3a64 : CertiFFI.Claim.Premise "card:default-initial/v1/current/host/regime/el3a64" .trm ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[7]! = true))
    (inv0_v1_current_host_regime_noEl3a32 : CertiFFI.Claim.Premise "card:default-initial/v1/current/host/regime/noEl3a32" .trm ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[3]! = false))
    (inv0_v1_current_host_regime_noRME : CertiFFI.Claim.Premise "card:default-initial/v1/current/host/regime/noRME" .trm ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[232]! = false))
    (inv0_v1_current_host_regime_a64 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/regime/a64" ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.PSTATE.nRW = 0#1))
    (inv0_v1_current_host_regime_tg : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/regime/tg" (ArmFull.Functions._get_TCR_EL2_Type_TG0
    ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) =
  0#2))
    (inv0_v1_current_host_regime_e2h : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/regime/e2h" (ArmFull.Functions._get_HCR_EL2_Type_E2H
    ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) =
  1#1))
    (inv0_v1_current_host_regime_d128 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/regime/d128" ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[178]! = true →
  ArmFull.Functions._get_TCR2_EL2_Type_D128
      ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR2_EL2) =
    0#1))
    (inv0_v1_current_host_regime_aie : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/regime/aie" ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[178]! = true →
  ArmFull.Functions._get_TCR2_EL2_Type_AIE
      ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR2_EL2) =
    0#1))
    (inv0_v1_current_host_regime_pnch : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/regime/pnch" ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[178]! = true →
  ArmFull.Functions._get_TCR2_EL2_Type_PnCH
      ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR2_EL2) =
    0#1))
    (inv0_v1_current_host_regime_ds : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/regime/ds" (Sail.BitVec.slice ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) 59
    1 =
  0#1))
    (inv0_v1_current_host_controls_regime : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/controls/regime" (spec.controls.regime = S1LogicalReference.Regime.el20))
    (inv0_v1_current_host_controls_ha : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/controls/ha" (spec.controls.ha = (hostHA (ArmBridge.CruxGenGuarded.beforeFetchState e).regs == 1#1)))
    (inv0_v1_current_host_controls_hd : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/controls/hd" (spec.controls.hd = (hostHD (ArmBridge.CruxGenGuarded.beforeFetchState e).regs == 1#1)))
    (inv0_v1_current_host_controls_pie : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/controls/pie" (spec.controls.pie = (hostPIE (ArmBridge.CruxGenGuarded.beforeFetchState e).regs == 1#1)))
    (inv0_v1_current_host_controls_hpd : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/controls/hpd" (spec.controls.hpd =
  ((if (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[48]! = true then
      Sail.BitVec.extractLsb
        ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) 41 41
    else 0#1) ==
    1#1)))
    (inv0_v1_current_host_controls_pir : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/controls/pir" (spec.controls.pie = true →
  spec.controls.pir =
    ArmFull.Functions.Mk_S1PIRType
      ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PIR_EL2)))
    (inv0_v1_current_host_controls_pire0 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/controls/pire0" (spec.controls.pie = true →
  spec.controls.pire0 =
    ArmFull.Functions.Mk_S1PIRType
      ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PIRE0_EL2)))
    (inv0_v1_current_host_controls_overlay : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/controls/overlay" ((spec.controls.poe || spec.controls.e0poe) = outputOverlayEnabled (ArmBridge.CruxGenGuarded.beforeFetchState e).regs))
    (inv0_v1_current_host_physical_legal : CertiFFI.Claim.Premise "card:default-initial/v1/current/host/physical/legal" .interim (LegalPAMax spec.physicalConfig.paMax))
    (inv0_v1_current_host_physical_pa : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/physical/pa" ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_Int ArmFull.Bank_Int.__supported_pa_size =
  spec.physicalConfig.paMax))
    (inv0_v1_current_host_physical_lpa : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/physical/lpa" ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[69]! = spec.physicalConfig.lpa))
    (inv0_v1_current_host_physical_lpa2 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/physical/lpa2" ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[156]! = spec.physicalConfig.lpa2))
    (inv0_v1_current_host_ips : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/ips" (spec.physicalConfig.ips =
  ArmFull.Functions._get_TCR_EL2_Type_IPS
    ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2)))
    (inv0_v1_current_host_endian : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/endian" (ArmFull.Functions._get_SCTLR_EL2_Type_EE
    ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCTLR_EL2) =
  0#1))
    (inv0_v1_current_host_mair : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/mair" (config.mair = (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MAIR_EL2))
    (inv0_v1_current_host_xs : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/xs" ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[166]! = config.xs))
    (inv0_v1_current_host_mte2 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/mte2" ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[134]! = config.mte2))
    (inv0_v1_current_host_el : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/host/el" ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.PSTATE.EL = 0#2 ∨
  (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.PSTATE.EL = 1#2))
    (inv0_v1_current_core_ha : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/core/ha" (({spec.params with txsz := _get_TCR_EL2_Type_T0SZ ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .TCR_EL2)} : S1TTWParams).ha = hostHA (ArmBridge.CruxGenGuarded.beforeFetchState e).regs))
    (inv0_v1_current_core_hd : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/core/hd" (({spec.params with txsz := _get_TCR_EL2_Type_T0SZ ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .TCR_EL2)} : S1TTWParams).hd = hostHD (ArmBridge.CruxGenGuarded.beforeFetchState e).regs))
    (inv0_v1_current_core_pie : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/core/pie" (({spec.params with txsz := _get_TCR_EL2_Type_T0SZ ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .TCR_EL2)} : S1TTWParams).pie = hostPIE (ArmBridge.CruxGenGuarded.beforeFetchState e).regs))
    (inv0_v1_current_core_wxn : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/core/wxn" (({spec.params with txsz := _get_TCR_EL2_Type_T0SZ ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .TCR_EL2)} : S1TTWParams).wxn = _get_SCTLR_EL2_Type_WXN ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .SCTLR_EL2)))
    (inv0_v1_current_core_mtx : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/core/mtx" (({spec.params with txsz := _get_TCR_EL2_Type_T0SZ ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .TCR_EL2)} : S1TTWParams).mtx = (if (ArmBridge.CruxGenGuarded.beforeFetchState e).regs.FeatureImpl[191]! then Sail.BitVec.extractLsb ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .TCR_EL2) 60 60 else 0#1)))
    (inv0_v1_current_core_txsz : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/core/txsz" (({spec.params with txsz := _get_TCR_EL2_Type_T0SZ ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .TCR_EL2)} : S1TTWParams).txsz = _get_TCR_EL2_Type_T0SZ ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .TCR_EL2)))
    (inv0_v1_current_geometry : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/geometry" (spec.params.txsz =
  normalizeTxsz (ArmBridge.CruxGenGuarded.beforeFetchState e).regs
    (ArmFull.Functions._get_TCR_EL2_Type_T0SZ
      ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2))))
    (inv0_v1_current_guards_tbi : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/guards/tbi" ((translateGuardView spec.params).tbi = (currentHostGuardView (ArmBridge.CruxGenGuarded.beforeFetchState e).regs).tbi))
    (inv0_v1_current_guards_tbid : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/guards/tbid" ((translateGuardView spec.params).tbid = (currentHostGuardView (ArmBridge.CruxGenGuarded.beforeFetchState e).regs).tbid))
    (inv0_v1_current_guards_nfd : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/guards/nfd" ((translateGuardView spec.params).nfd = (currentHostGuardView (ArmBridge.CruxGenGuarded.beforeFetchState e).regs).nfd))
    (inv0_v1_current_guards_e0pd : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/guards/e0pd" ((translateGuardView spec.params).e0pd = (currentHostGuardView (ArmBridge.CruxGenGuarded.beforeFetchState e).regs).e0pd))
    (inv0_v1_current_rawFault : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/rawFault" (sourceTxszFault (ArmBridge.CruxGenGuarded.beforeFetchState e).regs ({spec.params with txsz := _get_TCR_EL2_Type_T0SZ ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_BitVec_64 .TCR_EL2)} : S1TTWParams) = false))
    (inv0_v1_current_enabled : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/enabled" (currentTranslationEnabled (ArmBridge.CruxGenGuarded.beforeFetchState e).regs = true))
    (inv0_v1_current_cache : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/cache" ((ArmBridge.CruxGenGuarded.beforeFetchState e).regs.bank_Bool ArmFull.Bank_Bool.__tlb_enabled = false))
    (inv0_v1_quiet_a64 : CertiFFI.Claim.Premise "card:default-initial/v1/quiet/a64" .trm (ArmCert.HookQuiet.V0.feature e.regs ArmFull.Feature.FEAT_AA64EL0 = true))
    (inv0_v1_quiet_el0 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/el0" (e.regs.PSTATE.EL = 0#2))
    (inv0_v1_quiet_nrw : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/nrw" (e.regs.PSTATE.nRW = 0#1))
    (inv0_v1_quiet_scrRW : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/scrRW" (ArmFull.Functions._get_SCR_EL3_Type_RW (ArmCert.HookQuiet.V0.reg64 e.regs ArmFull.Bank_BitVec_64.SCR_EL3) = 1#1))
    (inv0_v1_quiet_hcrRW : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/hcrRW" (ArmFull.Functions._get_HCR_EL2_Type_RW (ArmCert.HookQuiet.V0.reg64 e.regs ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
    (inv0_v1_quiet_spe : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/spe" (e.regs.bank_Bool ArmFull.Bank_Bool.SPESampleInFlight = false))
    (inv0_v1_quiet_pmuIrqMask : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/pmuIrqMask" (ArmCert.HookQuiet.V0.reg64 e.regs ArmFull.Bank_BitVec_64.PMINTENCLR_EL1 = 0#64))
    (inv0_v1_quiet_brbePaused : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/brbePaused" (ArmFull.Functions._get_BRBFCR_EL1_Type_PAUSED (ArmCert.HookQuiet.V0.reg64 e.regs ArmFull.Bank_BitVec_64.BRBFCR_EL1) =
  1#1))
    (inv0_v1_quiet_pmuCountLower : CertiFFI.Claim.Premise "card:default-initial/v1/quiet/pmuCountLower" .interim (0 ≤ e.regs.bank_Int ArmFull.Bank_Int.NUM_PMU_COUNTERS))
    (inv0_v1_quiet_pmuCountUpper : CertiFFI.Claim.Premise "card:default-initial/v1/quiet/pmuCountUpper" .interim (e.regs.bank_Int ArmFull.Bank_Int.NUM_PMU_COUNTERS ≤ 31))
    (inv0_v1_quiet_ordinary : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/ordinary" (ArmFull.Functions._get_CNTCR_Type_SCEN (e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.CNTCR) = 0#1))
    (inv0_v1_quiet_timers_cntp : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/timers/cntp" (true = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTP_CTL_EL0).getLsbD 0 = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTP_CTL_EL0).getLsbD 1 = true ∨ ((ArmCert.HookQuiet.V0.realm e.regs) && (_get_CNTHCTL_EL2_Type_CNTPMASK (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHCTL_EL2) == 1#1)) = true ∨ (((ArmCert.HookQuiet.V0.physicalOffset e.regs)).toNat ≤ (ArmCert.HookQuiet.V0.physical e.regs) ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget < 2^64 ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget - ((ArmCert.HookQuiet.V0.physicalOffset e.regs)).toNat < (ArmCert.HookQuiet.V0.reg64 e.regs .CNTP_CVAL_EL0).toNat)))
    (inv0_v1_quiet_timers_cnthp : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/timers/cnthp" (true = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHP_CTL_EL2).getLsbD 0 = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHP_CTL_EL2).getLsbD 1 = true ∨ false = true ∨ ((0#64).toNat ≤ (ArmCert.HookQuiet.V0.physical e.regs) ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget < 2^64 ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget - (0#64).toNat < (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHP_CVAL_EL2).toNat)))
    (inv0_v1_quiet_timers_cnthps : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/timers/cnthps" ((ArmCert.HookQuiet.V0.feature e.regs .FEAT_SEL2) = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHPS_CTL_EL2).getLsbD 0 = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHPS_CTL_EL2).getLsbD 1 = true ∨ false = true ∨ ((0#64).toNat ≤ (ArmCert.HookQuiet.V0.physical e.regs) ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget < 2^64 ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget - (0#64).toNat < (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHPS_CVAL_EL2).toNat)))
    (inv0_v1_quiet_timers_cntps : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/timers/cntps" (true = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTPS_CTL_EL1).getLsbD 0 = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTPS_CTL_EL1).getLsbD 1 = true ∨ false = true ∨ (((ArmCert.HookQuiet.V0.physicalOffset e.regs)).toNat ≤ (ArmCert.HookQuiet.V0.physical e.regs) ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget < 2^64 ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget - ((ArmCert.HookQuiet.V0.physicalOffset e.regs)).toNat < (ArmCert.HookQuiet.V0.reg64 e.regs .CNTPS_CVAL_EL1).toNat)))
    (inv0_v1_quiet_timers_cntv : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/timers/cntv" (true = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTV_CTL_EL0).getLsbD 0 = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTV_CTL_EL0).getLsbD 1 = true ∨ ((ArmCert.HookQuiet.V0.realm e.regs) && (_get_CNTHCTL_EL2_Type_CNTVMASK (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHCTL_EL2) == 1#1)) = true ∨ (((ArmCert.HookQuiet.V0.reg64 e.regs .CNTVOFF_EL2)).toNat ≤ (ArmCert.HookQuiet.V0.physical e.regs) ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget < 2^64 ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget - ((ArmCert.HookQuiet.V0.reg64 e.regs .CNTVOFF_EL2)).toNat < (ArmCert.HookQuiet.V0.reg64 e.regs .CNTV_CVAL_EL0).toNat)))
    (inv0_v1_quiet_timers_cnthv : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/timers/cnthv" ((ArmCert.HookQuiet.V0.feature e.regs .FEAT_VHE) = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHV_CTL_EL2).getLsbD 0 = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHV_CTL_EL2).getLsbD 1 = true ∨ false = true ∨ ((0#64).toNat ≤ (ArmCert.HookQuiet.V0.physical e.regs) ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget < 2^64 ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget - (0#64).toNat < (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHV_CVAL_EL2).toNat)))
    (inv0_v1_quiet_timers_cnthvs : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/quiet/timers/cnthvs" (((ArmCert.HookQuiet.V0.feature e.regs .FEAT_SEL2) && (ArmCert.HookQuiet.V0.feature e.regs .FEAT_VHE)) = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHVS_CTL_EL2).getLsbD 0 = false ∨ (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHVS_CTL_EL2).getLsbD 1 = true ∨ false = true ∨ ((0#64).toNat ≤ (ArmCert.HookQuiet.V0.physical e.regs) ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget < 2^64 ∧ (ArmCert.HookQuiet.V0.physical e.regs) + budget - (0#64).toNat < (ArmCert.HookQuiet.V0.reg64 e.regs .CNTHVS_CVAL_EL2).toNat)))
    (inv0_v1_gic : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/gic" (e.regs.bank_Option_InterruptID ArmFull.Bank_Option_InterruptID.__GIC_Pending = none))
    (inv0_v1_pc : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pc" (e.regs._PC = base + offS 0))
    (inv0_closed : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/closed" (ArmCert.Translate.Model.ClosedMembershipAt spec config rows mapping
  (ArmBridge.CruxGenGuarded.Release.shimMap spec mapping base pins) (ArmBridge.CruxGenGuarded.beforeFetchState e)))
    (inv0_placed : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/placed" (MemReloc.ImageOn scope image e loadBase mapping))
    (inv0_branch_base_hFeature_AA32EL0 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_AA32EL0" .trm (e.regs.FeatureImpl[0]! = false))
    (inv0_branch_base_hFeature_AA32EL1 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_AA32EL1" .trm (e.regs.FeatureImpl[1]! = false))
    (inv0_branch_base_hFeature_AA32EL2 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_AA32EL2" .trm (e.regs.FeatureImpl[2]! = false))
    (inv0_branch_base_hFeature_AA32EL3 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_AA32EL3" .trm (e.regs.FeatureImpl[3]! = false))
    (inv0_branch_base_hFeature_AA64EL0 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_AA64EL0" .trm (e.regs.FeatureImpl[4]! = true))
    (inv0_branch_base_hFeature_AA64EL1 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_AA64EL1" .trm (e.regs.FeatureImpl[5]! = true))
    (inv0_branch_base_hFeature_AA64EL2 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_AA64EL2" .trm (e.regs.FeatureImpl[6]! = true))
    (inv0_branch_base_hFeature_AA64EL3 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_AA64EL3" .trm (e.regs.FeatureImpl[7]! = true))
    (inv0_branch_base_hFeature_AES : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_AES" .trm (e.regs.FeatureImpl[12]! = true))
    (inv0_branch_base_hFeature_AFP : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_AFP" .trm (e.regs.FeatureImpl[153]! = true))
    (inv0_branch_base_hFeature_AdvSIMD : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_AdvSIMD" .trm (e.regs.FeatureImpl[13]! = true))
    (inv0_branch_base_hFeature_BF16 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_BF16" .trm (e.regs.FeatureImpl[143]! = true))
    (inv0_branch_base_hFeature_BRBE : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_BRBE" .trm (e.regs.FeatureImpl[230]! = false))
    (inv0_branch_base_hFeature_BTI : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_BTI" .trm (e.regs.FeatureImpl[123]! = true))
    (inv0_branch_base_hFeature_CRC32 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_CRC32" .trm (e.regs.FeatureImpl[45]! = true))
    (inv0_branch_base_hFeature_DGH : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_DGH" .trm (e.regs.FeatureImpl[144]! = true))
    (inv0_branch_base_hFeature_DIT : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_DIT" .trm (e.regs.FeatureImpl[103]! = true))
    (inv0_branch_base_hFeature_DPB : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_DPB" .trm (e.regs.FeatureImpl[60]! = true))
    (inv0_branch_base_hFeature_DPB2 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_DPB2" .trm (e.regs.FeatureImpl[126]! = true))
    (inv0_branch_base_hFeature_Debugv8p9 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_Debugv8p9" .trm (e.regs.FeatureImpl[185]! = false))
    (inv0_branch_base_hFeature_DotProd : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_DotProd" .trm (e.regs.FeatureImpl[105]! = true))
    (inv0_branch_base_hFeature_ECV : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_ECV" .trm (e.regs.FeatureImpl[145]! = true))
    (inv0_branch_base_hFeature_FCMA : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_FCMA" .trm (e.regs.FeatureImpl[89]! = true))
    (inv0_branch_base_hFeature_FHM : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_FHM" .trm (e.regs.FeatureImpl[107]! = true))
    (inv0_branch_base_hFeature_FP : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_FP" .trm (e.regs.FeatureImpl[27]! = true))
    (inv0_branch_base_hFeature_FP16 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_FP16" .trm (e.regs.FeatureImpl[65]! = true))
    (inv0_branch_base_hFeature_FRINTTS : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_FRINTTS" .trm (e.regs.FeatureImpl[130]! = true))
    (inv0_branch_base_hFeature_FlagM : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_FlagM" .trm (e.regs.FeatureImpl[108]! = true))
    (inv0_branch_base_hFeature_FlagM2 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_FlagM2" .trm (e.regs.FeatureImpl[131]! = true))
    (inv0_branch_base_hFeature_I8MM : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_I8MM" .trm (e.regs.FeatureImpl[67]! = true))
    (inv0_branch_base_hFeature_JSCVT : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_JSCVT" .trm (e.regs.FeatureImpl[92]! = true))
    (inv0_branch_base_hFeature_LRCPC : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_LRCPC" .trm (e.regs.FeatureImpl[93]! = true))
    (inv0_branch_base_hFeature_LRCPC2 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_LRCPC2" .trm (e.regs.FeatureImpl[110]! = true))
    (inv0_branch_base_hFeature_LSE : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_LSE" .trm (e.regs.FeatureImpl[50]! = true))
    (inv0_branch_base_hFeature_LSE2 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_LSE2" .trm (e.regs.FeatureImpl[111]! = true))
    (inv0_branch_base_hFeature_MOPS : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_MOPS" .trm (e.regs.FeatureImpl[171]! = false))
    (inv0_branch_base_hFeature_MTE : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_MTE" .trm (e.regs.FeatureImpl[133]! = true))
    (inv0_branch_base_hFeature_PACIMP : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_PACIMP" .trm (e.regs.FeatureImpl[95]! = false))
    (inv0_branch_base_hFeature_PFAR : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_PFAR" .trm (e.regs.FeatureImpl[200]! = false))
    (inv0_branch_base_hFeature_PMULL : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_PMULL" .trm (e.regs.FeatureImpl[36]! = true))
    (inv0_branch_base_hFeature_RDM : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_RDM" .trm (e.regs.FeatureImpl[53]! = true))
    (inv0_branch_base_hFeature_RME : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_RME" .trm (e.regs.FeatureImpl[232]! = false))
    (inv0_branch_base_hFeature_SB : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SB" .trm (e.regs.FeatureImpl[138]! = true))
    (inv0_branch_base_hFeature_SHA1 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SHA1" .trm (e.regs.FeatureImpl[40]! = true))
    (inv0_branch_base_hFeature_SHA256 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SHA256" .trm (e.regs.FeatureImpl[41]! = true))
    (inv0_branch_base_hFeature_SHA3 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SHA3" .trm (e.regs.FeatureImpl[76]! = true))
    (inv0_branch_base_hFeature_SHA512 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SHA512" .trm (e.regs.FeatureImpl[77]! = true))
    (inv0_branch_base_hFeature_SM3 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SM3" .trm (e.regs.FeatureImpl[78]! = true))
    (inv0_branch_base_hFeature_SM4 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SM4" .trm (e.regs.FeatureImpl[79]! = true))
    (inv0_branch_base_hFeature_SME : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SME" .trm (e.regs.FeatureImpl[233]! = false))
    (inv0_branch_base_hFeature_SME_F64F64 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SME_F64F64" .trm (e.regs.FeatureImpl[234]! = false))
    (inv0_branch_base_hFeature_SME_FA64 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SME_FA64" .trm (e.regs.FeatureImpl[235]! = false))
    (inv0_branch_base_hFeature_SME_I16I64 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SME_I16I64" .trm (e.regs.FeatureImpl[236]! = false))
    (inv0_branch_base_hFeature_SVE : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SVE" .trm (e.regs.FeatureImpl[81]! = true))
    (inv0_branch_base_hFeature_SVE2 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SVE2" .trm (e.regs.FeatureImpl[221]! = true))
    (inv0_branch_base_hFeature_SVE_AES : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SVE_AES" .trm (e.regs.FeatureImpl[222]! = true))
    (inv0_branch_base_hFeature_SVE_BitPerm : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SVE_BitPerm" .trm (e.regs.FeatureImpl[223]! = true))
    (inv0_branch_base_hFeature_SVE_PMULL128 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SVE_PMULL128" .trm (e.regs.FeatureImpl[224]! = true))
    (inv0_branch_base_hFeature_SVE_SHA3 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SVE_SHA3" .trm (e.regs.FeatureImpl[225]! = true))
    (inv0_branch_base_hFeature_SVE_SM4 : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_SVE_SM4" .trm (e.regs.FeatureImpl[226]! = true))
    (inv0_branch_base_hFeature_TME : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_TME" .trm (e.regs.FeatureImpl[227]! = false))
    (inv0_branch_base_hFeature_WFxT : CertiFFI.Claim.Premise "card:default-initial/branch/base/hFeature_WFxT" .trm (e.regs.FeatureImpl[165]! = true))
    (inv0_branch_base_hDebugBP : CertiFFI.Claim.Premise "card:default-initial/branch/base/hDebugBP" .interim (e.regs.bank_Int ArmFull.Bank_Int.NUM_BREAKPOINTS = 6))
    (inv0_branch_base_hDebugWP : CertiFFI.Claim.Premise "card:default-initial/branch/base/hDebugWP" .interim (e.regs.bank_Int ArmFull.Bank_Int.NUM_WATCHPOINTS = 4))
    (inv0_branch_base_hDebugCTX : CertiFFI.Claim.Premise "card:default-initial/branch/base/hDebugCTX" .interim (e.regs.bank_Int ArmFull.Bank_Int.__num_ctx_breakpoints = 2))
    (inv0_branch_base_hEDSCR_STATUS : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hEDSCR_STATUS" (ArmFull.Functions._get_EDSCR_Type_STATUS (e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) = 2#6))
    (inv0_branch_base_hSPE : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hSPE" (e.regs.bank_Bool ArmFull.Bank_Bool.SPESampleInFlight = false))
    (inv0_branch_base_hEL : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hEL" (e.regs.PSTATE.EL = 0#2))
    (inv0_branch_base_hnRW : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hnRW" (e.regs.PSTATE.nRW = 0#1))
    (inv0_branch_base_hIL : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hIL" (e.regs.PSTATE.IL = 0#1))
    (inv0_branch_base_hE2H : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hE2H" (ArmFull.Functions._get_HCR_EL2_Type_E2H (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
    (inv0_branch_base_hTGE : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hTGE" (ArmFull.Functions._get_HCR_EL2_Type_TGE (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
    (inv0_branch_base_hSCR_NS : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hSCR_NS" (ArmFull.Functions._get_SCR_EL3_Type_NS (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 1#1))
    (inv0_branch_base_hSCR_NSE : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hSCR_NSE" (ArmFull.Functions._get_SCR_EL3_Type_NSE (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 0#1))
    (inv0_branch_base_hMDSCR_SS : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hMDSCR_SS" (ArmFull.Functions._get_MDSCR_EL1_Type_SS (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDSCR_EL1) = 0#1))
    (inv0_branch_base_hPSTATE_SS : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hPSTATE_SS" (e.regs.PSTATE.SS = 0#1))
    (inv0_branch_base_hOSUC : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hOSUC" (ArmFull.Functions._get_EDESR_Type_OSUC (e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32.EDESR) = 0#1))
    (inv0_branch_base_hPMB_E : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hPMB_E" (ArmFull.Functions._get_PMBLIMITR_EL1_Type_E (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.PMBLIMITR_EL1) = 0#1))
    (inv0_branch_base_hSCR_RW : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hSCR_RW" (ArmFull.Functions._get_SCR_EL3_Type_RW (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 1#1))
    (inv0_branch_base_hSCR_EEL2 : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hSCR_EEL2" (ArmFull.Functions._get_SCR_EL3_Type_EEL2 (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 0#1))
    (inv0_branch_base_hTBI0 : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hTBI0" (ArmFull.Functions._get_TCR_EL2_Type_TBI0 (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) = 1#1))
    (inv0_branch_base_hTBID0 : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hTBID0" (ArmFull.Functions._get_TCR_EL2_Type_TBID0 (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) = 0#1))
    (inv0_branch_base_hNSPB : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hNSPB" (ArmFull.Functions._get_MDCR_EL3_Type_NSPB (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDCR_EL3) = 3#2))
    (inv0_branch_base_hNSPBE : CertiFFI.Claim.DeploymentObligation "card:default-initial/branch/base/hNSPBE" (ArmFull.Functions._get_MDCR_EL3_Type_NSPBE (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDCR_EL3) = 0#1))
    (inv0_branch_vhe : CertiFFI.Claim.Premise "card:default-initial/branch/vhe" .trm (e.regs.FeatureImpl[54]! = true))
    (inv0_branch_gcs : CertiFFI.Claim.Premise "card:default-initial/branch/gcs" .trm (e.regs.FeatureImpl[245]! = false))
    (inv0_raw : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/raw" (ArmCertWalk.RawImageAt spec.imageRows e.mem))
    (inv0_noUpd : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/noUpd" (∀ (wr : Bool) (acc : ArmFull.AccessDescriptor),
  ArmCert.Translate.Model.DataShape wr acc →
    ArmCertWalk.NoUpdateRows
        (let __src := spec.params;
        { ha := __src.ha, hd := __src.hd, tbi := __src.tbi, tbid := __src.tbid, nfd := __src.nfd, e0pd := __src.e0pd,
          d128 := __src.d128, aie := __src.aie, mair2 := __src.mair2, ds := __src.ds, ps := __src.ps,
          txsz := __src.txsz, epan := __src.epan, dct := __src.dct, nv1 := __src.nv1, cmow := __src.cmow,
          pnch := __src.pnch, disch := __src.disch, haft := ArmCert.Translate.Model.hostHAFT e.regs, mtx := __src.mtx,
          skl := __src.skl, pie := __src.pie, pir := __src.pir, pire0 := __src.pire0, emec := __src.emec,
          amec := __src.amec, t0sz := __src.t0sz, t1sz := __src.t1sz, uwxn := __src.uwxn, tgx := __src.tgx,
          irgn := __src.irgn, orgn := __src.orgn, sh := __src.sh, hpd := __src.hpd, ee := __src.ee, wxn := __src.wxn,
          ntlsmd := __src.ntlsmd, dc := __src.dc, sif := __src.sif, mair := __src.mair })
        acc spec.imageRows =
      true))
    (inv0_post_spe : CertiFFI.Claim.DeploymentObligation "card:default-initial/post/spe" (e.regs.bank_Bool ArmFull.Bank_Bool.SPESampleInFlight = false))
    (inv0_post_el0 : CertiFFI.Claim.DeploymentObligation "card:default-initial/post/el0" (e.regs.PSTATE.EL = 0#2))
    (inv0_post_nrw : CertiFFI.Claim.DeploymentObligation "card:default-initial/post/nrw" (e.regs.PSTATE.nRW = 0#1))
    (inv0_post_noRME : CertiFFI.Claim.Premise "card:default-initial/post/noRME" .trm (e.regs.FeatureImpl[232]! = false))
    (inv0_post_vhe : CertiFFI.Claim.Premise "card:default-initial/post/vhe" .trm (e.regs.FeatureImpl[54]! = true))
    (inv0_post_aa64el0 : CertiFFI.Claim.Premise "card:default-initial/post/aa64el0" .trm (e.regs.FeatureImpl[4]! = true))
    (inv0_post_ns : CertiFFI.Claim.DeploymentObligation "card:default-initial/post/ns" (Sail.BitVec.extractLsb (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) 0 0 = 1#1))
    (inv0_post_e2h : CertiFFI.Claim.DeploymentObligation "card:default-initial/post/e2h" (Sail.BitVec.extractLsb (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) 34 34 = 1#1))
    (inv0_post_tge : CertiFFI.Claim.DeploymentObligation "card:default-initial/post/tge" (Sail.BitVec.extractLsb (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) 27 27 = 1#1))
    (inv0_post_e0e : CertiFFI.Claim.DeploymentObligation "card:default-initial/post/e0e" (Sail.BitVec.extractLsb (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1))
    (inv0_mode_noEL2A32 : CertiFFI.Claim.Premise "card:default-initial/mode/noEL2A32" .trm (e.regs.FeatureImpl[2]! = false))
    (inv0_mode_el2A64 : CertiFFI.Claim.Premise "card:default-initial/mode/el2A64" .trm (e.regs.FeatureImpl[6]! = true))
    (inv0_mode_vhe : CertiFFI.Claim.Premise "card:default-initial/mode/vhe" .trm (e.regs.FeatureImpl[54]! = true))
    (inv0_mode_el : CertiFFI.Claim.DeploymentObligation "card:default-initial/mode/el" (e.regs.PSTATE.EL = 0#2))
    (inv0_mode_ns : CertiFFI.Claim.DeploymentObligation "card:default-initial/mode/ns" (ArmFull.Functions._get_SCR_EL3_Type_NS (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 1#1))
    (inv0_mode_tge : CertiFFI.Claim.DeploymentObligation "card:default-initial/mode/tge" (ArmFull.Functions._get_HCR_EL2_Type_TGE (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
    (inv0_debug_mde : CertiFFI.Claim.DeploymentObligation "card:default-initial/debug/mde" (ArmFull.Functions._get_MDSCR_EL1_Type_MDE (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDSCR_EL1) = 0#1))
    (inv0_debug_hde : CertiFFI.Claim.DeploymentObligation "card:default-initial/debug/hde" (ArmFull.Functions._get_EDSCR_Type_HDE (e.regs.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) = 0#1))
    (inv0_feat : CertiFFI.Claim.Premise "card:shim-entry-invariant/feat" .trm (e.regs.FeatureImpl[7]! = true ∧
  e.regs.FeatureImpl[3]! = false ∧ e.regs.FeatureImpl[227]! = false ∧ e.regs.FeatureImpl[111]! = true))
    (inv0_dcache : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/dcache" (ArmCertWalk.currentDCache e.regs = true))
    (inv0_controls_host_el : CertiFFI.Claim.DeploymentObligation "card:default-controls/host/el" (e.regs.PSTATE.EL = 0#2))
    (inv0_controls_host_nrw : CertiFFI.Claim.DeploymentObligation "card:default-controls/host/nrw" (e.regs.PSTATE.nRW = 0#1))
    (inv0_controls_host_aa64 : CertiFFI.Claim.Premise "card:default-controls/host/aa64" .trm (e.regs.FeatureImpl[4]! = true))
    (inv0_controls_host_rme : CertiFFI.Claim.Premise "card:default-controls/host/rme" .trm (e.regs.FeatureImpl[232]! = false))
    (inv0_controls_host_vhe : CertiFFI.Claim.Premise "card:default-controls/host/vhe" .trm (e.regs.FeatureImpl[54]! = true))
    (inv0_controls_host_ns : CertiFFI.Claim.DeploymentObligation "card:default-controls/host/ns" (ArmFull.Functions._get_SCR_EL3_Type_NS (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCR_EL3) = 1#1))
    (inv0_controls_host_e2h : CertiFFI.Claim.DeploymentObligation "card:default-controls/host/e2h" (ArmFull.Functions._get_HCR_EL2_Type_E2H (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
    (inv0_controls_host_tge : CertiFFI.Claim.DeploymentObligation "card:default-controls/host/tge" (ArmFull.Functions._get_HCR_EL2_Type_TGE (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2) = 1#1))
    (inv0_controls_tco : CertiFFI.Claim.DeploymentObligation "card:default-controls/tco" (e.regs.PSTATE.TCO = 0#1))
    (inv0_controls_tcf0 : CertiFFI.Claim.DeploymentObligation "card:default-controls/tcf0" (ArmFull.Functions._get_SCTLR_EL2_Type_TCF0 (e.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCTLR_EL2) = 0#2))
    (inv0_controls_preparation : CertiFFI.Claim.DeploymentObligation "card:default-controls/preparation" (NativeMteTagCheck.PreparationAt catalogue e))
    (entryRows : CertiFFI.Claim.DeploymentObligation "card:default369-initial-tag-status-rows" (TagStatusRows e (e.choiceOcc.getD 1354 0) 112))
    (shimStatic : CertiFFI.Claim.DeploymentObligation "card:code-static" (RtDit.ShimFetch.ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte))
    (himage : CertiFFI.Claim.RunCheck "card:default-image-binding" (image = HeapV2.image base))
    (hload : CertiFFI.Claim.RunCheck "card:default-load-base-binding" (loadBase = base))
    (mrsEntry_dit : CertiFFI.Claim.Premise "card:default-initial-mrs-profile/dit" .trm (e.regs.FeatureImpl[103]! = true))
    (mrsEntry_bti : CertiFFI.Claim.Premise "card:default-initial-mrs-profile/bti" .trm (e.regs.FeatureImpl[123]! = true))
    (mrsEntry_tme : CertiFFI.Claim.Premise "card:default-initial-mrs-profile/tme" .trm (e.regs.FeatureImpl[227]! = false))
    (isbEntry_aa32el2 : CertiFFI.Claim.Premise "card:default-initial-isb-profile/aa32el2" .trm (e.regs.FeatureImpl[2]! = false))
    (isbEntry_aa32el3 : CertiFFI.Claim.Premise "card:default-initial-isb-profile/aa32el3" .trm (e.regs.FeatureImpl[3]! = false))
    (isbEntry_aa64el2 : CertiFFI.Claim.Premise "card:default-initial-isb-profile/aa64el2" .trm (e.regs.FeatureImpl[6]! = true))
    (isbEntry_aa64el3 : CertiFFI.Claim.Premise "card:default-initial-isb-profile/aa64el3" .trm (e.regs.FeatureImpl[7]! = true))
    (isbEntry_brbe : CertiFFI.Claim.Premise "card:default-initial-isb-profile/brbe" .trm (e.regs.FeatureImpl[230]! = false))
    (residue : CertiFFI.Claim.Premise "E32" .decided (RtBl.CallerInv.CallerResidue e))
    (slotE : CertiFFI.Claim.DeploymentObligation "card:slot-present" (RtShim.SlotPrem.ShimSlotPresent pins mapping e))
    (spE : CertiFFI.Claim.CallerContract "comp:caller:shim-caller-contract" (e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16))
    (static : CertiFFI.Claim.DeploymentObligation "card:code-static" (RtShim.SlotPrem.ShimSlotStatic pins mapping (rowsFootprint spec.imageRows)))
    (spAligned : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers" ((BitVec.ofNat 64 pins.sp).toNat % 16 = 0))
    (E_S : CertiFFI.Claim.DeploymentObligation "card:body-entry/S" (NativeBodyDeploy.BodyStatic spec mapping base pins))
    (E_hoff : CertiFFI.Claim.RunCheck "card:plan-offsets" (offS 7 = ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf 0))
    (E_hscope : CertiFFI.Claim.DeploymentObligation "card:body-entry/hscope" (∀ (o : Nat), HeapV2StepCerts.codeScope o → scope o))
    (E_presentE : CertiFFI.Claim.DeploymentObligation "card:body-entry/presentE" (HeapV2StepCerts.C3.DataPresent pins mapping e))
    (E_x0E : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers" (HeapV2StepCerts.RegBind.regVal e (HeapV2StepCerts.RegBind.Reg.x 0) = BitVec.ofInt 64 ↑pins.x0))
    (E_x1E : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers" (HeapV2StepCerts.RegBind.regVal e (HeapV2StepCerts.RegBind.Reg.x 1) = BitVec.ofInt 64 ↑pins.x1))
    (E_normal : CertiFFI.Claim.CallerContract "card:path-selector" (HeapV2StepCerts.ValBind.NormalPath pins (HeapV2StepCerts.E17General.qOf e)))
    (codeStore : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ImageTableSeparated scope base mapping (Residue.StoreBytes pins mapping)))
    (slotStore : CertiFFI.Claim.DeploymentObligation "card:default-slot-store-separation" (∀ a, RtShim2.ShimMem.slotBytes pins mapping a → ¬ Residue.StoreBytes pins mapping a))
    (low : CertiFFI.Claim.CallerContract "card:default-caller-return-low" ((e.regs.gpr[30]'(by decide)).toNat < 2 ^ 55))
    (target : CertiFFI.Claim.CallerContract "card:default-caller-return-target" (e.regs.gpr[30]'(by decide) = base + offS 369))
    (ndPA : CertiFFI.Claim.DeploymentObligation "card:default-mapping-no-double-map-pa" (TranslateMem.NoDoubleMapPA pins mapping))
    (ndSlot : CertiFFI.Claim.DeploymentObligation "card:default-mapping-no-double-map-slot" (TranslateMem.NoDoubleMapSlot pins mapping))
    (layout : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers" (TranslateMem.RegionsDisjoint pins ∧ (pins.x1 + 32 ≤ pins.sp ∨ pins.sp + 16 ≤ pins.x1) ∧ pins.sp + 16 ≤ 2 ^ 64))
    (agreesShim : CertiFFI.Claim.DeploymentObligation "card:consumer-map-agrees" (ConsumerMapAgrees spec mapping (shimMap spec mapping base pins))) :
    (∀ j, j ≤ 369 → ArmCert.Premises.TranslationAgreesV1.TranslationAgrees
      (Release.mapAt spec mapping base pins j) (stateAt real e j)) ∧
    (∀ j, 5 ≤ j → j ≤ 367 → (stateAt real e j).regs.PSTATE.DIT = 1#1) ∧
    (stateAt real e 369).regs.PSTATE.DIT = e.regs.PSTATE.DIT ∧
    (stateAt real e 369).regs._PC = e.regs.gpr[30]'(by decide) ∧
    ((∀ r ∈ Residue.frameRegs, RegBind.regVal (stateAt real e 369) (.x r) = RegBind.regVal e (.x r)) ∧
      (stateAt real e 369).regs.gpr[(GPRSummary.key (19#5 : BitVec 5).toNat).val] = e.regs.gpr[19]'(by decide) ∧
      (stateAt real e 369).regs.gpr[30]'(by decide) = e.regs.gpr[30]'(by decide) ∧
      (stateAt real e 369).regs.SP_EL0 = e.regs.SP_EL0 ∧
      (stateAt real e 369).regs._Z = e.regs._Z ∧
      (∀ a, ¬ Residue.StoreBytes pins mapping a → (stateAt real e 364).mem[a]? = (stateAt real e 7).mem[a]?) ∧
      (∀ i : Fin 18, RegBind.regVal (stateAt real e 364) (.x (Fin.castLE (by decide) i)) = 0#64) ∧
      (stateAt real e 364).regs.PSTATE.Z = 1#1 ∧ Release.ResidueNCV real e) ∧
    Release.Functional mapping pins e (stateAt real e 369) :=
  ReleaseProfile.DefaultHeapShimFactory.normalP real spec config rows mapping pins scope image loadBase base offS
    budget catalogue e room.holds aligned.holds offPre.holds offPost.holds codeSlot.holds
    ⟨⟨⟨inv0_v1_pins_f4.holds, inv0_v1_pins_rme.holds, inv0_v1_pins_spe.holds, inv0_v1_pins_el.holds,
    inv0_v1_pins_nrw.holds, inv0_v1_pins_edecr.holds, inv0_v1_pins_cti.holds, inv0_v1_pins_st.holds,
    inv0_v1_pins_edesr.holds, inv0_v1_pins_btt.holds, inv0_v1_pins_emu.holds, inv0_v1_pins_e2h.holds,
    inv0_v1_pins_tge.holds, inv0_v1_pins_scrns.holds, inv0_v1_pins_pmbe.holds, inv0_v1_pins_mdss.holds,
    inv0_v1_pins_pmbs.holds, inv0_v1_pins_da.holds, inv0_v1_pins_di.holds, inv0_v1_pins_df.holds,
    inv0_v1_pins_il.holds, inv0_v1_pins_pss.holds, inv0_v1_pins_btype.holds, inv0_v1_pins_btn.holds⟩,
    ⟨inv0_v1_features_a0.holds, inv0_v1_features_a1.holds, inv0_v1_features_a2.holds, inv0_v1_features_a3.holds,
    inv0_v1_features_b1.holds, inv0_v1_features_b2.holds, inv0_v1_features_b3.holds,
    inv0_v1_features_vhe.holds⟩, ⟨inv0_v1_debug_mde.holds, inv0_v1_debug_hde.holds⟩,
    ⟨⟨inv0_v1_current_images_covered.holds, inv0_v1_current_images_topology.holds,
    inv0_v1_current_images_attributes.holds, inv0_v1_current_images_writeback.holds,
    inv0_v1_current_images_permissions.holds⟩, ⟨⟨inv0_v1_current_host_regime_el3a64.holds,
    inv0_v1_current_host_regime_noEl3a32.holds, inv0_v1_current_host_regime_noRME.holds,
    inv0_v1_current_host_regime_a64.holds, inv0_v1_current_host_regime_tg.holds,
    inv0_v1_current_host_regime_e2h.holds, inv0_v1_current_host_regime_d128.holds,
    inv0_v1_current_host_regime_aie.holds, inv0_v1_current_host_regime_pnch.holds,
    inv0_v1_current_host_regime_ds.holds⟩, ⟨inv0_v1_current_host_controls_regime.holds,
    inv0_v1_current_host_controls_ha.holds, inv0_v1_current_host_controls_hd.holds,
    inv0_v1_current_host_controls_pie.holds, inv0_v1_current_host_controls_hpd.holds,
    inv0_v1_current_host_controls_pir.holds, inv0_v1_current_host_controls_pire0.holds,
    inv0_v1_current_host_controls_overlay.holds⟩, ⟨inv0_v1_current_host_physical_legal.holds,
    inv0_v1_current_host_physical_pa.holds, inv0_v1_current_host_physical_lpa.holds,
    inv0_v1_current_host_physical_lpa2.holds⟩, inv0_v1_current_host_ips.holds,
    inv0_v1_current_host_endian.holds, inv0_v1_current_host_mair.holds, inv0_v1_current_host_xs.holds,
    inv0_v1_current_host_mte2.holds, inv0_v1_current_host_el.holds⟩, ⟨inv0_v1_current_core_ha.holds,
    inv0_v1_current_core_hd.holds, inv0_v1_current_core_pie.holds, inv0_v1_current_core_wxn.holds,
    inv0_v1_current_core_mtx.holds, inv0_v1_current_core_txsz.holds⟩, inv0_v1_current_geometry.holds,
    (ReleaseProfile.HeapFinalLeaf.guard_of_fields inv0_v1_current_guards_tbi.holds
    inv0_v1_current_guards_tbid.holds inv0_v1_current_guards_nfd.holds inv0_v1_current_guards_e0pd.holds),
    inv0_v1_current_rawFault.holds, inv0_v1_current_enabled.holds, inv0_v1_current_cache.holds⟩,
    ⟨inv0_v1_quiet_a64.holds, inv0_v1_quiet_el0.holds, inv0_v1_quiet_nrw.holds, inv0_v1_quiet_scrRW.holds,
    inv0_v1_quiet_hcrRW.holds, (ReleaseProfile.HeapFinalLeaf.security_of_noRME e.regs
    inv0_controls_host_rme.holds), inv0_v1_quiet_spe.holds, inv0_v1_quiet_pmuIrqMask.holds,
    inv0_v1_quiet_brbePaused.holds, inv0_v1_quiet_pmuCountLower.holds, inv0_v1_quiet_pmuCountUpper.holds,
    inv0_v1_quiet_ordinary.holds, ⟨inv0_v1_quiet_timers_cntp.holds, inv0_v1_quiet_timers_cnthp.holds,
    inv0_v1_quiet_timers_cnthps.holds, inv0_v1_quiet_timers_cntps.holds, inv0_v1_quiet_timers_cntv.holds,
    inv0_v1_quiet_timers_cnthv.holds, inv0_v1_quiet_timers_cnthvs.holds⟩⟩, inv0_v1_gic.holds, inv0_v1_pc.holds⟩,
    inv0_closed.holds, inv0_placed.holds, ⟨⟨inv0_branch_base_hFeature_AA32EL0.holds,
    inv0_branch_base_hFeature_AA32EL1.holds, inv0_branch_base_hFeature_AA32EL2.holds,
    inv0_branch_base_hFeature_AA32EL3.holds, inv0_branch_base_hFeature_AA64EL0.holds,
    inv0_branch_base_hFeature_AA64EL1.holds, inv0_branch_base_hFeature_AA64EL2.holds,
    inv0_branch_base_hFeature_AA64EL3.holds, inv0_branch_base_hFeature_AES.holds,
    inv0_branch_base_hFeature_AFP.holds, inv0_branch_base_hFeature_AdvSIMD.holds,
    inv0_branch_base_hFeature_BF16.holds, inv0_branch_base_hFeature_BRBE.holds,
    inv0_branch_base_hFeature_BTI.holds, inv0_branch_base_hFeature_CRC32.holds,
    inv0_branch_base_hFeature_DGH.holds, inv0_branch_base_hFeature_DIT.holds,
    inv0_branch_base_hFeature_DPB.holds, inv0_branch_base_hFeature_DPB2.holds,
    inv0_branch_base_hFeature_Debugv8p9.holds, inv0_branch_base_hFeature_DotProd.holds,
    inv0_branch_base_hFeature_ECV.holds, inv0_branch_base_hFeature_FCMA.holds,
    inv0_branch_base_hFeature_FHM.holds, inv0_branch_base_hFeature_FP.holds,
    inv0_branch_base_hFeature_FP16.holds, inv0_branch_base_hFeature_FRINTTS.holds,
    inv0_branch_base_hFeature_FlagM.holds, inv0_branch_base_hFeature_FlagM2.holds,
    inv0_branch_base_hFeature_I8MM.holds, inv0_branch_base_hFeature_JSCVT.holds,
    inv0_branch_base_hFeature_LRCPC.holds, inv0_branch_base_hFeature_LRCPC2.holds,
    inv0_branch_base_hFeature_LSE.holds, inv0_branch_base_hFeature_LSE2.holds,
    inv0_branch_base_hFeature_MOPS.holds, inv0_branch_base_hFeature_MTE.holds,
    inv0_branch_base_hFeature_PACIMP.holds, inv0_branch_base_hFeature_PFAR.holds,
    inv0_branch_base_hFeature_PMULL.holds, inv0_branch_base_hFeature_RDM.holds,
    inv0_branch_base_hFeature_RME.holds, inv0_branch_base_hFeature_SB.holds,
    inv0_branch_base_hFeature_SHA1.holds, inv0_branch_base_hFeature_SHA256.holds,
    inv0_branch_base_hFeature_SHA3.holds, inv0_branch_base_hFeature_SHA512.holds,
    inv0_branch_base_hFeature_SM3.holds, inv0_branch_base_hFeature_SM4.holds,
    inv0_branch_base_hFeature_SME.holds, inv0_branch_base_hFeature_SME_F64F64.holds,
    inv0_branch_base_hFeature_SME_FA64.holds, inv0_branch_base_hFeature_SME_I16I64.holds,
    inv0_branch_base_hFeature_SVE.holds, inv0_branch_base_hFeature_SVE2.holds,
    inv0_branch_base_hFeature_SVE_AES.holds, inv0_branch_base_hFeature_SVE_BitPerm.holds,
    inv0_branch_base_hFeature_SVE_PMULL128.holds, inv0_branch_base_hFeature_SVE_SHA3.holds,
    inv0_branch_base_hFeature_SVE_SM4.holds, inv0_branch_base_hFeature_TME.holds,
    inv0_branch_base_hFeature_WFxT.holds, inv0_branch_base_hDebugBP.holds, inv0_branch_base_hDebugWP.holds,
    inv0_branch_base_hDebugCTX.holds, inv0_branch_base_hEDSCR_STATUS.holds, inv0_branch_base_hSPE.holds,
    inv0_branch_base_hEL.holds, inv0_branch_base_hnRW.holds, inv0_branch_base_hIL.holds,
    inv0_branch_base_hE2H.holds, inv0_branch_base_hTGE.holds, inv0_branch_base_hSCR_NS.holds,
    inv0_branch_base_hSCR_NSE.holds, inv0_branch_base_hMDSCR_SS.holds, inv0_branch_base_hPSTATE_SS.holds,
    inv0_branch_base_hOSUC.holds, inv0_branch_base_hPMB_E.holds, inv0_branch_base_hSCR_RW.holds,
    inv0_branch_base_hSCR_EEL2.holds, inv0_branch_base_hTBI0.holds, inv0_branch_base_hTBID0.holds,
    inv0_branch_base_hNSPB.holds, inv0_branch_base_hNSPBE.holds⟩, inv0_branch_vhe.holds, inv0_branch_gcs.holds⟩,
    inv0_raw.holds, inv0_noUpd.holds, ⟨inv0_post_spe.holds, inv0_post_el0.holds, inv0_post_nrw.holds,
    inv0_post_noRME.holds, inv0_post_vhe.holds, inv0_post_aa64el0.holds, inv0_post_ns.holds,
    inv0_post_e2h.holds, inv0_post_tge.holds, inv0_post_e0e.holds⟩, ⟨inv0_mode_noEL2A32.holds,
    inv0_mode_el2A64.holds, inv0_mode_vhe.holds, inv0_mode_el.holds, inv0_mode_ns.holds, inv0_mode_tge.holds⟩,
    ⟨inv0_debug_mde.holds, inv0_debug_hde.holds⟩, inv0_feat.holds, inv0_dcache.holds,
    ⟨⟨inv0_controls_host_el.holds, inv0_controls_host_nrw.holds, inv0_controls_host_aa64.holds,
    inv0_controls_host_rme.holds, inv0_controls_host_vhe.holds, inv0_controls_host_ns.holds,
    inv0_controls_host_e2h.holds, inv0_controls_host_tge.holds⟩, inv0_controls_tco.holds, inv0_controls_tcf0.holds, inv0_controls_preparation.holds⟩⟩ entryRows.holds
    shimStatic.holds himage.holds hload.holds ⟨mrsEntry_dit.holds, mrsEntry_bti.holds, mrsEntry_tme.holds⟩
    ⟨isbEntry_aa32el2.holds, isbEntry_aa32el3.holds, isbEntry_aa64el2.holds, isbEntry_aa64el3.holds,
    isbEntry_brbe.holds⟩ residue.holds slotE.holds spE.holds static.holds spAligned.holds ⟨E_S.holds,
    E_hoff.holds, E_hscope.holds, E_presentE.holds, E_x0E.holds, E_x1E.holds, E_normal.holds⟩ codeStore.holds
    slotStore.holds low.holds target.holds ndPA.holds ndSlot.holds layout.holds.1 layout.holds.2.1 layout.holds.2.2 agreesShim.holds

/-- Back-derivation: the source root follows from the card, so card and root state the same claim. -/
theorem card_normalP_root : type_of% @ReleaseProfile.DefaultHeapShimFactory.normalP := by
  intro real inst domain spec config rows mapping pins scope image loadBase base offS budget catalogue e room
    aligned offPre offPost codeSlot inv0 entryRows shimStatic himage hload mrsEntry isbEntry residue slotE spE
    static spAligned E codeStore slotStore low target ndPA ndSlot hd slotDisj spHi agreesShim
  exact @card_normalP real inst domain spec config rows mapping pins scope image loadBase base offS budget
    catalogue e ⟨room⟩ ⟨aligned⟩ ⟨offPre⟩ ⟨offPost⟩ ⟨codeSlot⟩ ⟨inv0.v1.pins.f4⟩ ⟨inv0.v1.pins.rme⟩
    ⟨inv0.v1.pins.spe⟩ ⟨inv0.v1.pins.el⟩ ⟨inv0.v1.pins.nrw⟩ ⟨inv0.v1.pins.edecr⟩ ⟨inv0.v1.pins.cti⟩
    ⟨inv0.v1.pins.st⟩ ⟨inv0.v1.pins.edesr⟩ ⟨inv0.v1.pins.btt⟩ ⟨inv0.v1.pins.emu⟩ ⟨inv0.v1.pins.e2h⟩
    ⟨inv0.v1.pins.tge⟩ ⟨inv0.v1.pins.scrns⟩ ⟨inv0.v1.pins.pmbe⟩ ⟨inv0.v1.pins.mdss⟩ ⟨inv0.v1.pins.pmbs⟩
    ⟨inv0.v1.pins.da⟩ ⟨inv0.v1.pins.di⟩ ⟨inv0.v1.pins.df⟩ ⟨inv0.v1.pins.il⟩ ⟨inv0.v1.pins.pss⟩
    ⟨inv0.v1.pins.btype⟩ ⟨inv0.v1.pins.btn⟩ ⟨inv0.v1.features.a0⟩ ⟨inv0.v1.features.a1⟩ ⟨inv0.v1.features.a2⟩
    ⟨inv0.v1.features.a3⟩ ⟨inv0.v1.features.b1⟩ ⟨inv0.v1.features.b2⟩ ⟨inv0.v1.features.b3⟩
    ⟨inv0.v1.features.vhe⟩ ⟨inv0.v1.debug.mde⟩ ⟨inv0.v1.debug.hde⟩ ⟨inv0.v1.current.images.covered⟩
    ⟨inv0.v1.current.images.topology⟩ ⟨inv0.v1.current.images.attributes⟩ ⟨inv0.v1.current.images.writeback⟩
    ⟨inv0.v1.current.images.permissions⟩ ⟨inv0.v1.current.host.regime.el3a64⟩
    ⟨inv0.v1.current.host.regime.noEl3a32⟩ ⟨inv0.v1.current.host.regime.noRME⟩ ⟨inv0.v1.current.host.regime.a64⟩
    ⟨inv0.v1.current.host.regime.tg⟩ ⟨inv0.v1.current.host.regime.e2h⟩ ⟨inv0.v1.current.host.regime.d128⟩
    ⟨inv0.v1.current.host.regime.aie⟩ ⟨inv0.v1.current.host.regime.pnch⟩ ⟨inv0.v1.current.host.regime.ds⟩
    ⟨inv0.v1.current.host.controls.regime⟩ ⟨inv0.v1.current.host.controls.ha⟩ ⟨inv0.v1.current.host.controls.hd⟩
    ⟨inv0.v1.current.host.controls.pie⟩ ⟨inv0.v1.current.host.controls.hpd⟩ ⟨inv0.v1.current.host.controls.pir⟩
    ⟨inv0.v1.current.host.controls.pire0⟩ ⟨inv0.v1.current.host.controls.overlay⟩
    ⟨inv0.v1.current.host.physical.legal⟩ ⟨inv0.v1.current.host.physical.pa⟩ ⟨inv0.v1.current.host.physical.lpa⟩
    ⟨inv0.v1.current.host.physical.lpa2⟩ ⟨inv0.v1.current.host.ips⟩ ⟨inv0.v1.current.host.endian⟩
    ⟨inv0.v1.current.host.mair⟩ ⟨inv0.v1.current.host.xs⟩ ⟨inv0.v1.current.host.mte2⟩ ⟨inv0.v1.current.host.el⟩
    ⟨inv0.v1.current.core.ha⟩ ⟨inv0.v1.current.core.hd⟩ ⟨inv0.v1.current.core.pie⟩ ⟨inv0.v1.current.core.wxn⟩
    ⟨inv0.v1.current.core.mtx⟩ ⟨inv0.v1.current.core.txsz⟩ ⟨inv0.v1.current.geometry⟩ ⟨(congrArg
    TranslateGuardView.tbi inv0.v1.current.guards)⟩ ⟨(congrArg TranslateGuardView.tbid inv0.v1.current.guards)⟩
    ⟨(congrArg TranslateGuardView.nfd inv0.v1.current.guards)⟩ ⟨(congrArg TranslateGuardView.e0pd
    inv0.v1.current.guards)⟩ ⟨inv0.v1.current.rawFault⟩ ⟨inv0.v1.current.enabled⟩ ⟨inv0.v1.current.cache⟩
    ⟨inv0.v1.quiet.a64⟩ ⟨inv0.v1.quiet.el0⟩ ⟨inv0.v1.quiet.nrw⟩ ⟨inv0.v1.quiet.scrRW⟩ ⟨inv0.v1.quiet.hcrRW⟩
    ⟨inv0.v1.quiet.spe⟩ ⟨inv0.v1.quiet.pmuIrqMask⟩ ⟨inv0.v1.quiet.brbePaused⟩ ⟨inv0.v1.quiet.pmuCountLower⟩
    ⟨inv0.v1.quiet.pmuCountUpper⟩ ⟨inv0.v1.quiet.ordinary⟩ ⟨inv0.v1.quiet.timers.1⟩ ⟨inv0.v1.quiet.timers.2.1⟩
    ⟨inv0.v1.quiet.timers.2.2.1⟩ ⟨inv0.v1.quiet.timers.2.2.2.1⟩ ⟨inv0.v1.quiet.timers.2.2.2.2.1⟩
    ⟨inv0.v1.quiet.timers.2.2.2.2.2.1⟩ ⟨inv0.v1.quiet.timers.2.2.2.2.2.2⟩ ⟨inv0.v1.gic⟩ ⟨inv0.v1.pc⟩
    ⟨inv0.closed⟩ ⟨inv0.placed⟩ ⟨inv0.branch.base.hFeature_AA32EL0⟩ ⟨inv0.branch.base.hFeature_AA32EL1⟩
    ⟨inv0.branch.base.hFeature_AA32EL2⟩ ⟨inv0.branch.base.hFeature_AA32EL3⟩ ⟨inv0.branch.base.hFeature_AA64EL0⟩
    ⟨inv0.branch.base.hFeature_AA64EL1⟩ ⟨inv0.branch.base.hFeature_AA64EL2⟩ ⟨inv0.branch.base.hFeature_AA64EL3⟩
    ⟨inv0.branch.base.hFeature_AES⟩ ⟨inv0.branch.base.hFeature_AFP⟩ ⟨inv0.branch.base.hFeature_AdvSIMD⟩
    ⟨inv0.branch.base.hFeature_BF16⟩ ⟨inv0.branch.base.hFeature_BRBE⟩ ⟨inv0.branch.base.hFeature_BTI⟩
    ⟨inv0.branch.base.hFeature_CRC32⟩ ⟨inv0.branch.base.hFeature_DGH⟩ ⟨inv0.branch.base.hFeature_DIT⟩
    ⟨inv0.branch.base.hFeature_DPB⟩ ⟨inv0.branch.base.hFeature_DPB2⟩ ⟨inv0.branch.base.hFeature_Debugv8p9⟩
    ⟨inv0.branch.base.hFeature_DotProd⟩ ⟨inv0.branch.base.hFeature_ECV⟩ ⟨inv0.branch.base.hFeature_FCMA⟩
    ⟨inv0.branch.base.hFeature_FHM⟩ ⟨inv0.branch.base.hFeature_FP⟩ ⟨inv0.branch.base.hFeature_FP16⟩
    ⟨inv0.branch.base.hFeature_FRINTTS⟩ ⟨inv0.branch.base.hFeature_FlagM⟩ ⟨inv0.branch.base.hFeature_FlagM2⟩
    ⟨inv0.branch.base.hFeature_I8MM⟩ ⟨inv0.branch.base.hFeature_JSCVT⟩ ⟨inv0.branch.base.hFeature_LRCPC⟩
    ⟨inv0.branch.base.hFeature_LRCPC2⟩ ⟨inv0.branch.base.hFeature_LSE⟩ ⟨inv0.branch.base.hFeature_LSE2⟩
    ⟨inv0.branch.base.hFeature_MOPS⟩ ⟨inv0.branch.base.hFeature_MTE⟩ ⟨inv0.branch.base.hFeature_PACIMP⟩
    ⟨inv0.branch.base.hFeature_PFAR⟩ ⟨inv0.branch.base.hFeature_PMULL⟩ ⟨inv0.branch.base.hFeature_RDM⟩
    ⟨inv0.branch.base.hFeature_RME⟩ ⟨inv0.branch.base.hFeature_SB⟩ ⟨inv0.branch.base.hFeature_SHA1⟩
    ⟨inv0.branch.base.hFeature_SHA256⟩ ⟨inv0.branch.base.hFeature_SHA3⟩ ⟨inv0.branch.base.hFeature_SHA512⟩
    ⟨inv0.branch.base.hFeature_SM3⟩ ⟨inv0.branch.base.hFeature_SM4⟩ ⟨inv0.branch.base.hFeature_SME⟩
    ⟨inv0.branch.base.hFeature_SME_F64F64⟩ ⟨inv0.branch.base.hFeature_SME_FA64⟩
    ⟨inv0.branch.base.hFeature_SME_I16I64⟩ ⟨inv0.branch.base.hFeature_SVE⟩ ⟨inv0.branch.base.hFeature_SVE2⟩
    ⟨inv0.branch.base.hFeature_SVE_AES⟩ ⟨inv0.branch.base.hFeature_SVE_BitPerm⟩
    ⟨inv0.branch.base.hFeature_SVE_PMULL128⟩ ⟨inv0.branch.base.hFeature_SVE_SHA3⟩
    ⟨inv0.branch.base.hFeature_SVE_SM4⟩ ⟨inv0.branch.base.hFeature_TME⟩ ⟨inv0.branch.base.hFeature_WFxT⟩
    ⟨inv0.branch.base.hDebugBP⟩ ⟨inv0.branch.base.hDebugWP⟩ ⟨inv0.branch.base.hDebugCTX⟩
    ⟨inv0.branch.base.hEDSCR_STATUS⟩ ⟨inv0.branch.base.hSPE⟩ ⟨inv0.branch.base.hEL⟩ ⟨inv0.branch.base.hnRW⟩
    ⟨inv0.branch.base.hIL⟩ ⟨inv0.branch.base.hE2H⟩ ⟨inv0.branch.base.hTGE⟩ ⟨inv0.branch.base.hSCR_NS⟩
    ⟨inv0.branch.base.hSCR_NSE⟩ ⟨inv0.branch.base.hMDSCR_SS⟩ ⟨inv0.branch.base.hPSTATE_SS⟩
    ⟨inv0.branch.base.hOSUC⟩ ⟨inv0.branch.base.hPMB_E⟩ ⟨inv0.branch.base.hSCR_RW⟩ ⟨inv0.branch.base.hSCR_EEL2⟩
    ⟨inv0.branch.base.hTBI0⟩ ⟨inv0.branch.base.hTBID0⟩ ⟨inv0.branch.base.hNSPB⟩ ⟨inv0.branch.base.hNSPBE⟩
    ⟨inv0.branch.vhe⟩ ⟨inv0.branch.gcs⟩ ⟨inv0.raw⟩ ⟨inv0.noUpd⟩ ⟨inv0.post.spe⟩ ⟨inv0.post.el0⟩ ⟨inv0.post.nrw⟩
    ⟨inv0.post.noRME⟩ ⟨inv0.post.vhe⟩ ⟨inv0.post.aa64el0⟩ ⟨inv0.post.ns⟩ ⟨inv0.post.e2h⟩ ⟨inv0.post.tge⟩
    ⟨inv0.post.e0e⟩ ⟨inv0.mode.noEL2A32⟩ ⟨inv0.mode.el2A64⟩ ⟨inv0.mode.vhe⟩ ⟨inv0.mode.el⟩ ⟨inv0.mode.ns⟩
    ⟨inv0.mode.tge⟩ ⟨inv0.debug.mde⟩ ⟨inv0.debug.hde⟩ ⟨inv0.feat⟩ ⟨inv0.dcache⟩ ⟨inv0.controls.host.el⟩
    ⟨inv0.controls.host.nrw⟩ ⟨inv0.controls.host.aa64⟩ ⟨inv0.controls.host.rme⟩ ⟨inv0.controls.host.vhe⟩
    ⟨inv0.controls.host.ns⟩ ⟨inv0.controls.host.e2h⟩ ⟨inv0.controls.host.tge⟩ ⟨inv0.controls.tco⟩ ⟨inv0.controls.tcf0⟩ ⟨inv0.controls.preparation⟩ ⟨entryRows⟩ ⟨shimStatic⟩ ⟨himage⟩
    ⟨hload⟩ ⟨mrsEntry.dit⟩ ⟨mrsEntry.bti⟩ ⟨mrsEntry.tme⟩ ⟨isbEntry.aa32el2⟩ ⟨isbEntry.aa32el3⟩
    ⟨isbEntry.aa64el2⟩ ⟨isbEntry.aa64el3⟩ ⟨isbEntry.brbe⟩ ⟨residue⟩ ⟨slotE⟩ ⟨spE⟩ ⟨static⟩ ⟨spAligned⟩ ⟨E.S⟩
    ⟨E.hoff⟩ ⟨E.hscope⟩ ⟨E.presentE⟩ ⟨E.x0E⟩ ⟨E.x1E⟩ ⟨E.normal⟩ ⟨codeStore⟩ ⟨slotStore⟩ ⟨low⟩ ⟨target⟩ ⟨ndPA⟩
    ⟨ndSlot⟩ ⟨⟨hd, slotDisj, spHi⟩⟩ ⟨agreesShim⟩


#print axioms card_normalP
#print axioms card_normalP_root

end ReleaseProfile.DefaultHeapCards
