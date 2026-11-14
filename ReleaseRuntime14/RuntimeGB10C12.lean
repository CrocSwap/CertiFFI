import ReleaseProfile.GB10.Producers
import RuntimeC12LeafCards

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-!
# Runtime c12 full/fullpc/CT C1 boundaries over the canonical GB10 source (generated)

Configuration binders are canonical-source projections; produced atoms come from
entry agreement via shared Producer lemmas; every other atom stays an explicit input
with its original proposition. Speed mode: compiles, not verified.
-/

namespace ReleaseProfile.GB10.Runtime

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10


#check "CURRENT_DECL GB10.Runtime.fullFromSource_c12"
/-- Runtime full c12 C1 at the canonical source: 212 atoms produced from entry
agreement, 29 explicit inputs (program/memory/caller data and Heap-retained classes). -/
def fullFromSource_c12 (real : Type) [inst : Sail.SailReal real] {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (cfg : Configuration rho caller) (entry : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg entry.regs) (sspec : SourceSpec rho caller spec)
    (timers : TimersQuiet entry.regs budget) :=
  fun (a10 : _) (a11 : _) (a17 : _) (a18 : _) (a19 : _) (a20 : _) (a21 : _) (a22 : _) (a23 : _) (a24 : _) (a25 : _) (a28 : _) (a29 : _) (a30 : _) (a31 : _) (a32 : _) (a67 : _) (a68 : _) (a69 : _) (a70 : _) (a71 : _) (a133 : _) (a134 : _) (a135 : _) (a222 : _) (a223 : _) (a255 : _) (a256 : _) (a257 : _) =>
    @ReleaseProfile.DefaultRuntimeCards.card_release_full_c12
      real inst domain spec (sourceAttributes rho caller) rows
      mapping table sc bytes a10 a11
      base ifunc p budget inputs a17
      a18 a19 a20 a21 a22 a23
      a24 a25 (sourceCatalogue rho caller) entry a28 a29
      a30 a31 a32 ⟨feature_at cfg entry ag 4 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 232 (by decide) false _ rfl⟩ ⟨quiet_spe cfg entry ag⟩
      ⟨pstate_EL cfg entry ag⟩ ⟨pstate_nRW cfg entry ag⟩ ⟨field32_EDECR_RCE _ _ _ (control32_entry cfg entry ag .EDECR)⟩ ⟨field32_CTIDEVCTL_RCE _ _ _ (control32_entry cfg entry ag .CTIDEVCTL)⟩ ⟨quiet_edscr_status cfg entry ag⟩ ⟨quiet_edesr cfg entry ag⟩
      ⟨quiet_branch cfg entry ag⟩ ⟨quiet_emulator cfg entry ag⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_PMBLIMITR_EL1_E _ _ _ (control_entry cfg entry ag .PMBLIMITR_EL1 (by decide))⟩
      ⟨field_MDSCR_EL1_SS _ _ _ (control_entry cfg entry ag .MDSCR_EL1 (by decide))⟩ ⟨quiet_pmbsr cfg entry ag⟩ ⟨pstate_A cfg entry ag⟩ ⟨pstate_I cfg entry ag⟩ ⟨pstate_F cfg entry ag⟩ ⟨pstate_IL cfg entry ag⟩
      ⟨pstate_SS cfg entry ag⟩ ⟨pstate_BTYPE cfg entry ag⟩ ⟨quiet_btype_next cfg entry ag⟩ ⟨feature_at cfg entry ag 0 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 1 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 2 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 3 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 5 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 6 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 7 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 54 (by decide) true _ rfl⟩ ⟨field_MDSCR_EL1_MDE _ _ _ (control_entry cfg entry ag .MDSCR_EL1 (by decide))⟩
      ⟨field32_EDSCR_HDE _ _ _ (control32_entry cfg entry ag ._EDSCR)⟩ a67 a68 a69 a70 a71
      ⟨feature_at cfg entry ag 7 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 3 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 232 (by decide) false _ rfl⟩ ⟨pstate_nRW cfg entry ag⟩ ⟨field_TCR_EL2_TG0 _ _ _ (control_before_TCR_EL2 cfg entry ag)⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_before_HCR_EL2 cfg entry ag)⟩
      ⟨tcr2_guard_D128 cfg entry ag⟩ ⟨tcr2_guard_AIE cfg entry ag⟩ ⟨tcr2_guard_PnCH cfg entry ag⟩ ⟨tcr_ds_before cfg entry ag⟩ ⟨sspec.regime⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.ha d⟩
      ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.hd d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pie d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.hpd d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pir d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pire0 d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.overlay d⟩
      ⟨by rw [sspec.physical]; exact legalPAMax_source _ _⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); rw [sspec.physical]; rfl⟩ ⟨by show entry.regs.FeatureImpl[69]! = _; rw [sspec.physical, getElem!_pos _ 69 (by decide)]; exact actual_coordinate cfg entry.regs ag ⟨.feature 69, rfl⟩⟩ ⟨by show entry.regs.FeatureImpl[156]! = _; rw [sspec.physical, getElem!_pos _ 156 (by decide)]; exact actual_coordinate cfg entry.regs ag ⟨.feature 156, rfl⟩⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); rw [sspec.physical]; rfl⟩ ⟨field_SCTLR_EL2_EE _ _ _ (control_before_SCTLR_EL2 cfg entry ag)⟩
      ⟨attribute_mair cfg entry ag⟩ ⟨attribute_xs cfg entry ag⟩ ⟨attribute_mte2 cfg entry ag⟩ ⟨Or.inl (pstate_EL cfg entry ag)⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsHa d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsHd d⟩
      ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsPie d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsWxn d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsMtx d⟩ ⟨rfl⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.normalizedTxsz d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardTbi d⟩
      ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardTbid d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardNfd d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardE0pd d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.rawFault d⟩ ⟨translation_enabled cfg entry ag⟩ ⟨quiet_tlb cfg entry ag⟩
      ⟨by show entry.regs.FeatureImpl[4]! = true; exact feature_at cfg entry ag 4 (by decide) true _ rfl⟩ ⟨pstate_EL cfg entry ag⟩ ⟨pstate_nRW cfg entry ag⟩ ⟨field_SCR_EL3_RW _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_RW _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨quiet_spe cfg entry ag⟩
      ⟨pmintenclr_zero cfg entry ag⟩ ⟨field_BRBFCR_EL1_PAUSED _ _ _ (control_entry cfg entry ag .BRBFCR_EL1 (by decide))⟩ ⟨pmu_lower cfg entry ag⟩ ⟨pmu_upper cfg entry ag⟩ ⟨field32_CNTCR_SCEN _ _ _ (control32_entry cfg entry ag .CNTCR)⟩ ⟨timers.cntp⟩
      ⟨timers.cnthp⟩ ⟨timers.cnthps⟩ ⟨timers.cntps⟩ ⟨timers.cntv⟩ ⟨timers.cnthv⟩ ⟨timers.cnthvs⟩
      ⟨quiet_gic cfg entry ag⟩ a133 a134 a135 ⟨feature_at cfg entry ag 0 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 1 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 2 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 3 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 4 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 5 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 6 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 7 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 12 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 153 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 13 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 143 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 230 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 123 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 45 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 144 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 103 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 60 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 126 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 185 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 105 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 145 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 89 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 107 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 27 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 65 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 130 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 108 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 131 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 67 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 92 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 93 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 110 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 50 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 111 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 171 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 133 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 95 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 200 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 36 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 53 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 232 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 138 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 40 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 41 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 76 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 77 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 78 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 79 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 233 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 234 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 235 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 236 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 81 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 221 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 222 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 223 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 224 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 225 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 226 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 227 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 165 (by decide) true _ rfl⟩
      ⟨num_breakpoints cfg entry ag⟩ ⟨num_watchpoints cfg entry ag⟩ ⟨num_ctx_breakpoints cfg entry ag⟩ ⟨quiet_edscr_status cfg entry ag⟩ ⟨quiet_spe cfg entry ag⟩ ⟨pstate_EL cfg entry ag⟩
      ⟨pstate_nRW cfg entry ag⟩ ⟨pstate_IL cfg entry ag⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_SCR_EL3_NSE _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩
      ⟨field_MDSCR_EL1_SS _ _ _ (control_entry cfg entry ag .MDSCR_EL1 (by decide))⟩ ⟨pstate_SS cfg entry ag⟩ ⟨quiet_osuc cfg entry ag⟩ ⟨field_PMBLIMITR_EL1_E _ _ _ (control_entry cfg entry ag .PMBLIMITR_EL1 (by decide))⟩ ⟨field_SCR_EL3_RW _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_SCR_EL3_EEL2 _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩
      ⟨field_TCR_EL2_TBI0 _ _ _ (control_entry cfg entry ag .TCR_EL2 (by decide))⟩ ⟨field_TCR_EL2_TBID0 _ _ _ (control_entry cfg entry ag .TCR_EL2 (by decide))⟩ ⟨field_MDCR_EL3_NSPB _ _ _ (control_entry cfg entry ag .MDCR_EL3 (by decide))⟩ ⟨field_MDCR_EL3_NSPBE _ _ _ (control_entry cfg entry ag .MDCR_EL3 (by decide))⟩ ⟨feature_at cfg entry ag 54 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 245 (by decide) false _ rfl⟩
      a222 a223 ⟨quiet_spe cfg entry ag⟩ ⟨pstate_EL cfg entry ag⟩ ⟨pstate_nRW cfg entry ag⟩ ⟨feature_at cfg entry ag 232 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 54 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 4 (by decide) true _ rfl⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_SCTLR_EL2_E0E _ _ _ (control_entry cfg entry ag .SCTLR_EL2 (by decide))⟩
      ⟨feature_at cfg entry ag 2 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 6 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 54 (by decide) true _ rfl⟩ ⟨pstate_EL cfg entry ag⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩
      ⟨field_MDSCR_EL1_MDE _ _ _ (control_entry cfg entry ag .MDSCR_EL1 (by decide))⟩ ⟨field32_EDSCR_HDE _ _ _ (control32_entry cfg entry ag ._EDSCR)⟩ ⟨⟨feature_at cfg entry ag 7 (by decide) true _ rfl, feature_at cfg entry ag 3 (by decide) false _ rfl, feature_at cfg entry ag 227 (by decide) false _ rfl, feature_at cfg entry ag 111 (by decide) true _ rfl⟩⟩ ⟨dcache_entry cfg entry ag⟩ ⟨pstate_EL cfg entry ag⟩ ⟨pstate_nRW cfg entry ag⟩
      ⟨feature_at cfg entry ag 4 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 232 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 54 (by decide) true _ rfl⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩
      ⟨pstate_TCO cfg entry ag⟩ ⟨field_SCTLR_EL2_TCF0 _ _ _ (control_entry cfg entry ag .SCTLR_EL2 (by decide))⟩ ⟨preparation cfg entry ag⟩ a255 a256 a257

#check "CURRENT_DECL GB10.Runtime.FullResidual_c12"
/-- Retained original full c12 inputs, explicit at the source substitution; timers named premise. -/
structure FullResidual_c12 {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (entry : ArmBridge.Draft.NativeState) : Prop where
  timers : TimersQuiet entry.regs budget
  a10 : CertiFFI.Claim.RunCheck "card:r14-code-binds" (ArmCert.Translate.Model.StaticPie.Binds bytes R14Scoped.slices)
  a11 : CertiFFI.Claim.RunCheck "card:r14-code-binds" (R14E17.CodeBinds bytes)
  a17 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/covers" (PipeR14.ScopeCovers sc)
  a18 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/separated" (ArmCert.Translate.Model.ImageTableSeparated sc base mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a19 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/contiguous" (∀ (c : Nat × Nat), c ∈ R14E17.codeVAs → ArmCert.Translate.Model.ImageWordContiguous mapping base c.fst)
  a20 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/notMMIO" (∀ (c : Nat × Nat), c ∈ R14E17.codeVAs → ArmCertWalk.MappedNotMMIO mapping (MemReloc.imageAddress base c.fst))
  a21 : CertiFFI.Claim.CallerContract "card:input-vector-shape" (inputs.length = PipeR14.n0_c12)
  a22 : CertiFFI.Claim.CallerContract "card:path-selector" (ArmCertPipe.PathOK (ArmCertValue.extend inputs PipeR14.D_c12) PipeR14.guards_c12)
  a23 : CertiFFI.Claim.DeploymentObligation "card:data-starts" (PipeR14.Physical.DataStartsR14 mapping p (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte PipeR14.dataSites_c12 PipeR14.regions_c12 (PipeR14.AccessAnchors.sites_c12 p) sc base)
  a24 : CertiFFI.Claim.CallerContract "card:pins-agree" (PipeR14.PinsAgree p PipeR14.rs_c12 PipeR14.forms_c12 inputs)
  a25 : CertiFFI.Claim.DeploymentObligation "E34" ((List.map (fun x => x.logical) spec.logicalRows).Nodup)
  a28 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ArmCert.Translate.Model.ImageTableSeparated sc base mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a29 : CertiFFI.Claim.DeploymentObligation "card:load-base-page" (base.toNat % 4096 = 0)
  a30 : CertiFFI.Claim.DeploymentObligation "E31" (base.toNat < 2 ^ 54)
  a31 : CertiFFI.Claim.DeploymentObligation "card:consumer-map-agrees" (ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table))
  a32 : CertiFFI.Claim.RunCheck "card:budget" (PipeR14.plan_c12.length ≤ budget)
  a67 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/covered" (∀ (row : ArmCert.Translate.Model.PermissionRow), row ∈ rows → row.slot ∈ (ArmCert.Translate.Model.rowsFootprint spec.imageRows).slots)
  a68 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/topology" (ArmCert.Translate.Model.TopologyImageAt spec (ArmBridge.CruxGenGuarded.beforeFetchState entry))
  a69 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/attributes" (ArmCert.Translate.Model.AttributeImage (ArmCert.Translate.Model.rowsObserve spec.imageRows) (sourceAttributes rho caller) (ArmBridge.CruxGenGuarded.beforeFetchState entry).mem)
  a70 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/writeback" (ArmCert.Translate.Model.WriteBackAttributeImage (ArmCert.Translate.Model.rowsObserve spec.imageRows) (sourceAttributes rho caller) (ArmBridge.CruxGenGuarded.beforeFetchState entry).mem)
  a71 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/permissions" (ArmCert.Translate.Model.PermissionImage rows spec.params (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs spec.controls (ArmBridge.CruxGenGuarded.beforeFetchState entry).mem)
  a133 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pc" (entry.regs._PC = base + PipeR14.offset_c12 0)
  a134 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/closed" (ArmCert.Translate.Model.ClosedMembershipAt spec (sourceAttributes rho caller) rows mapping (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table) (ArmBridge.CruxGenGuarded.beforeFetchState entry))
  a135 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/placed" (MemReloc.ImageOn sc (ArmCert.Translate.Model.StaticPie.referenceImageI bytes base ifunc) entry base mapping)
  a222 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/raw" (ArmCertWalk.RawImageAt spec.imageRows entry.mem)
  a223 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/noUpd" (∀ (wr : Bool) (acc : ArmFull.AccessDescriptor), ArmCert.Translate.Model.DataShape wr acc → ArmCertWalk.NoUpdateRows (have __src := spec.params; { ha := __src.ha, hd := __src.hd, tbi := __src.tbi, tbid := __src.tbid, nfd := __src.nfd, e0pd := __src.e0pd, d128 := __src.d128, aie := __src.aie, mair2 := __src.mair2, ds := __src.ds, ps := __src.ps, txsz := __src.txsz, epan := __src.epan, dct := __src.dct, nv1 := __src.nv1, cmow := __src.cmow, pnch := __src.pnch, disch := __src.disch, haft := ArmCert.Translate.Model.hostHAFT entry.regs, mtx := __src.mtx, skl := __src.skl, pie := __src.pie, pir := __src.pir, pire0 := __src.pire0, emec := __src.emec, amec := __src.amec, t0sz := __src.t0sz, t1sz := __src.t1sz, uwxn := __src.uwxn, tgx := __src.tgx, irgn := __src.irgn, orgn := __src.orgn, sh := __src.sh, hpd := __src.hpd, ee := __src.ee, wxn := __src.wxn, ntlsmd := __src.ntlsmd, dc := __src.dc, sif := __src.sif, mair := __src.mair }) acc spec.imageRows = true)
  a255 : CertiFFI.Claim.DeploymentObligation "card:runtime-initial/extra" (ArmCertPipe.AgreesAt mapping (PipeR14.pinv p) PipeR14.regions_c12 PipeR14.σ0_c12 inputs PipeR14.plan_c12 0 entry)
  a256 : CertiFFI.Claim.DeploymentObligation "card:runtime-initial/statusRows" (NativeMteTagCheck.TagStatusRows entry (entry.choiceOcc.getD 1354 0) ReleaseProfile.DefaultRuntime.capacity_c12)
  a257 : CertiFFI.Claim.DeploymentObligation "card:runtime14-view-agree" (ReleaseR14.VA.ViewAgree_c12 p mapping)

#check "CURRENT_DECL GB10.Runtime.full_c1_explicit_c12"
def full_c1_explicit_c12 (real : Type) [inst : Sail.SailReal real] {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (cfg : Configuration rho caller) (entry : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg entry.regs) (sspec : SourceSpec rho caller spec)
    (res : FullResidual_c12 spec rows mapping table sc bytes base ifunc p budget inputs rho caller entry) :=
  fullFromSource_c12 real spec rows mapping table sc bytes base ifunc p budget inputs rho caller cfg entry ag sspec res.timers res.a10 res.a11 res.a17 res.a18 res.a19 res.a20 res.a21 res.a22 res.a23 res.a24 res.a25 res.a28 res.a29 res.a30 res.a31 res.a32 res.a67 res.a68 res.a69 res.a70 res.a71 res.a133 res.a134 res.a135 res.a222 res.a223 res.a255 res.a256 res.a257

#check "CURRENT_DECL GB10.Runtime.full_imageLoaded_c12"
/-- Runtime ImageLoadedAsReviewed: the reviewed image (R14Scoped.slices + closure code words) is placed. -/
theorem full_imageLoaded_c12 {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (entry : ArmBridge.Draft.NativeState)
    (res : FullResidual_c12 spec rows mapping table sc bytes base ifunc p budget inputs rho caller entry) :
    MemReloc.ImageOn sc (ArmCert.Translate.Model.StaticPie.referenceImageI bytes base ifunc) entry base mapping ∧ ArmCert.Translate.Model.StaticPie.Binds bytes R14Scoped.slices ∧ R14E17.CodeBinds bytes :=
  ⟨res.a135.holds, res.a10.holds, res.a11.holds⟩

#check "CURRENT_DECL GB10.Runtime.fullpcFromSource_c12"
/-- Runtime fullpc c12 C1 at the canonical source: 212 atoms produced from entry
agreement, 29 explicit inputs (program/memory/caller data and Heap-retained classes). -/
def fullpcFromSource_c12 (real : Type) [inst : Sail.SailReal real] {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (cfg : Configuration rho caller) (entry : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg entry.regs) (sspec : SourceSpec rho caller spec)
    (timers : TimersQuiet entry.regs budget) :=
  fun (a10 : _) (a11 : _) (a17 : _) (a18 : _) (a19 : _) (a20 : _) (a21 : _) (a22 : _) (a23 : _) (a24 : _) (a25 : _) (a28 : _) (a29 : _) (a30 : _) (a31 : _) (a32 : _) (a67 : _) (a68 : _) (a69 : _) (a70 : _) (a71 : _) (a133 : _) (a134 : _) (a135 : _) (a222 : _) (a223 : _) (a255 : _) (a256 : _) (a257 : _) =>
    @ReleaseProfile.DefaultRuntimeCards.card_release_fullpc_c12
      real inst domain spec (sourceAttributes rho caller) rows
      mapping table sc bytes a10 a11
      base ifunc p budget inputs a17
      a18 a19 a20 a21 a22 a23
      a24 a25 (sourceCatalogue rho caller) entry a28 a29
      a30 a31 a32 ⟨feature_at cfg entry ag 4 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 232 (by decide) false _ rfl⟩ ⟨quiet_spe cfg entry ag⟩
      ⟨pstate_EL cfg entry ag⟩ ⟨pstate_nRW cfg entry ag⟩ ⟨field32_EDECR_RCE _ _ _ (control32_entry cfg entry ag .EDECR)⟩ ⟨field32_CTIDEVCTL_RCE _ _ _ (control32_entry cfg entry ag .CTIDEVCTL)⟩ ⟨quiet_edscr_status cfg entry ag⟩ ⟨quiet_edesr cfg entry ag⟩
      ⟨quiet_branch cfg entry ag⟩ ⟨quiet_emulator cfg entry ag⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_PMBLIMITR_EL1_E _ _ _ (control_entry cfg entry ag .PMBLIMITR_EL1 (by decide))⟩
      ⟨field_MDSCR_EL1_SS _ _ _ (control_entry cfg entry ag .MDSCR_EL1 (by decide))⟩ ⟨quiet_pmbsr cfg entry ag⟩ ⟨pstate_A cfg entry ag⟩ ⟨pstate_I cfg entry ag⟩ ⟨pstate_F cfg entry ag⟩ ⟨pstate_IL cfg entry ag⟩
      ⟨pstate_SS cfg entry ag⟩ ⟨pstate_BTYPE cfg entry ag⟩ ⟨quiet_btype_next cfg entry ag⟩ ⟨feature_at cfg entry ag 0 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 1 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 2 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 3 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 5 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 6 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 7 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 54 (by decide) true _ rfl⟩ ⟨field_MDSCR_EL1_MDE _ _ _ (control_entry cfg entry ag .MDSCR_EL1 (by decide))⟩
      ⟨field32_EDSCR_HDE _ _ _ (control32_entry cfg entry ag ._EDSCR)⟩ a67 a68 a69 a70 a71
      ⟨feature_at cfg entry ag 7 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 3 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 232 (by decide) false _ rfl⟩ ⟨pstate_nRW cfg entry ag⟩ ⟨field_TCR_EL2_TG0 _ _ _ (control_before_TCR_EL2 cfg entry ag)⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_before_HCR_EL2 cfg entry ag)⟩
      ⟨tcr2_guard_D128 cfg entry ag⟩ ⟨tcr2_guard_AIE cfg entry ag⟩ ⟨tcr2_guard_PnCH cfg entry ag⟩ ⟨tcr_ds_before cfg entry ag⟩ ⟨sspec.regime⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.ha d⟩
      ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.hd d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pie d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.hpd d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pir d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pire0 d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.overlay d⟩
      ⟨by rw [sspec.physical]; exact legalPAMax_source _ _⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); rw [sspec.physical]; rfl⟩ ⟨by show entry.regs.FeatureImpl[69]! = _; rw [sspec.physical, getElem!_pos _ 69 (by decide)]; exact actual_coordinate cfg entry.regs ag ⟨.feature 69, rfl⟩⟩ ⟨by show entry.regs.FeatureImpl[156]! = _; rw [sspec.physical, getElem!_pos _ 156 (by decide)]; exact actual_coordinate cfg entry.regs ag ⟨.feature 156, rfl⟩⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); rw [sspec.physical]; rfl⟩ ⟨field_SCTLR_EL2_EE _ _ _ (control_before_SCTLR_EL2 cfg entry ag)⟩
      ⟨attribute_mair cfg entry ag⟩ ⟨attribute_xs cfg entry ag⟩ ⟨attribute_mte2 cfg entry ag⟩ ⟨Or.inl (pstate_EL cfg entry ag)⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsHa d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsHd d⟩
      ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsPie d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsWxn d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsMtx d⟩ ⟨rfl⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.normalizedTxsz d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardTbi d⟩
      ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardTbid d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardNfd d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardE0pd d⟩ ⟨by have hr := regs_eq_source cfg entry.regs ag; generalize dataOf entry.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.rawFault d⟩ ⟨translation_enabled cfg entry ag⟩ ⟨quiet_tlb cfg entry ag⟩
      ⟨by show entry.regs.FeatureImpl[4]! = true; exact feature_at cfg entry ag 4 (by decide) true _ rfl⟩ ⟨pstate_EL cfg entry ag⟩ ⟨pstate_nRW cfg entry ag⟩ ⟨field_SCR_EL3_RW _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_RW _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨quiet_spe cfg entry ag⟩
      ⟨pmintenclr_zero cfg entry ag⟩ ⟨field_BRBFCR_EL1_PAUSED _ _ _ (control_entry cfg entry ag .BRBFCR_EL1 (by decide))⟩ ⟨pmu_lower cfg entry ag⟩ ⟨pmu_upper cfg entry ag⟩ ⟨field32_CNTCR_SCEN _ _ _ (control32_entry cfg entry ag .CNTCR)⟩ ⟨timers.cntp⟩
      ⟨timers.cnthp⟩ ⟨timers.cnthps⟩ ⟨timers.cntps⟩ ⟨timers.cntv⟩ ⟨timers.cnthv⟩ ⟨timers.cnthvs⟩
      ⟨quiet_gic cfg entry ag⟩ a133 a134 a135 ⟨feature_at cfg entry ag 0 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 1 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 2 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 3 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 4 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 5 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 6 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 7 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 12 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 153 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 13 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 143 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 230 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 123 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 45 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 144 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 103 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 60 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 126 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 185 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 105 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 145 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 89 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 107 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 27 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 65 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 130 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 108 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 131 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 67 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 92 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 93 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 110 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 50 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 111 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 171 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 133 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 95 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 200 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 36 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 53 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 232 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 138 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 40 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 41 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 76 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 77 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 78 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 79 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 233 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 234 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 235 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 236 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 81 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 221 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 222 (by decide) true _ rfl⟩
      ⟨feature_at cfg entry ag 223 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 224 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 225 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 226 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 227 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 165 (by decide) true _ rfl⟩
      ⟨num_breakpoints cfg entry ag⟩ ⟨num_watchpoints cfg entry ag⟩ ⟨num_ctx_breakpoints cfg entry ag⟩ ⟨quiet_edscr_status cfg entry ag⟩ ⟨quiet_spe cfg entry ag⟩ ⟨pstate_EL cfg entry ag⟩
      ⟨pstate_nRW cfg entry ag⟩ ⟨pstate_IL cfg entry ag⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_SCR_EL3_NSE _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩
      ⟨field_MDSCR_EL1_SS _ _ _ (control_entry cfg entry ag .MDSCR_EL1 (by decide))⟩ ⟨pstate_SS cfg entry ag⟩ ⟨quiet_osuc cfg entry ag⟩ ⟨field_PMBLIMITR_EL1_E _ _ _ (control_entry cfg entry ag .PMBLIMITR_EL1 (by decide))⟩ ⟨field_SCR_EL3_RW _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_SCR_EL3_EEL2 _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩
      ⟨field_TCR_EL2_TBI0 _ _ _ (control_entry cfg entry ag .TCR_EL2 (by decide))⟩ ⟨field_TCR_EL2_TBID0 _ _ _ (control_entry cfg entry ag .TCR_EL2 (by decide))⟩ ⟨field_MDCR_EL3_NSPB _ _ _ (control_entry cfg entry ag .MDCR_EL3 (by decide))⟩ ⟨field_MDCR_EL3_NSPBE _ _ _ (control_entry cfg entry ag .MDCR_EL3 (by decide))⟩ ⟨feature_at cfg entry ag 54 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 245 (by decide) false _ rfl⟩
      a222 a223 ⟨quiet_spe cfg entry ag⟩ ⟨pstate_EL cfg entry ag⟩ ⟨pstate_nRW cfg entry ag⟩ ⟨feature_at cfg entry ag 232 (by decide) false _ rfl⟩
      ⟨feature_at cfg entry ag 54 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 4 (by decide) true _ rfl⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_SCTLR_EL2_E0E _ _ _ (control_entry cfg entry ag .SCTLR_EL2 (by decide))⟩
      ⟨feature_at cfg entry ag 2 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 6 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 54 (by decide) true _ rfl⟩ ⟨pstate_EL cfg entry ag⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩
      ⟨field_MDSCR_EL1_MDE _ _ _ (control_entry cfg entry ag .MDSCR_EL1 (by decide))⟩ ⟨field32_EDSCR_HDE _ _ _ (control32_entry cfg entry ag ._EDSCR)⟩ ⟨⟨feature_at cfg entry ag 7 (by decide) true _ rfl, feature_at cfg entry ag 3 (by decide) false _ rfl, feature_at cfg entry ag 227 (by decide) false _ rfl, feature_at cfg entry ag 111 (by decide) true _ rfl⟩⟩ ⟨dcache_entry cfg entry ag⟩ ⟨pstate_EL cfg entry ag⟩ ⟨pstate_nRW cfg entry ag⟩
      ⟨feature_at cfg entry ag 4 (by decide) true _ rfl⟩ ⟨feature_at cfg entry ag 232 (by decide) false _ rfl⟩ ⟨feature_at cfg entry ag 54 (by decide) true _ rfl⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg entry ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg entry ag .HCR_EL2 (by decide))⟩
      ⟨pstate_TCO cfg entry ag⟩ ⟨field_SCTLR_EL2_TCF0 _ _ _ (control_entry cfg entry ag .SCTLR_EL2 (by decide))⟩ ⟨preparation cfg entry ag⟩ a255 a256 a257

#check "CURRENT_DECL GB10.Runtime.FullPCResidual_c12"
/-- Retained original fullpc c12 inputs, explicit at the source substitution; timers named premise. -/
structure FullPCResidual_c12 {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (entry : ArmBridge.Draft.NativeState) : Prop where
  timers : TimersQuiet entry.regs budget
  a10 : CertiFFI.Claim.RunCheck "card:r14-code-binds" (ArmCert.Translate.Model.StaticPie.Binds bytes R14Scoped.slices)
  a11 : CertiFFI.Claim.RunCheck "card:r14-code-binds" (R14E17.CodeBinds bytes)
  a17 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/covers" (PipeR14.ScopeCovers sc)
  a18 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/separated" (ArmCert.Translate.Model.ImageTableSeparated sc base mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a19 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/contiguous" (∀ (c : Nat × Nat), c ∈ R14E17.codeVAs → ArmCert.Translate.Model.ImageWordContiguous mapping base c.fst)
  a20 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/notMMIO" (∀ (c : Nat × Nat), c ∈ R14E17.codeVAs → ArmCertWalk.MappedNotMMIO mapping (MemReloc.imageAddress base c.fst))
  a21 : CertiFFI.Claim.CallerContract "card:input-vector-shape" (inputs.length = PipeR14.n0_c12)
  a22 : CertiFFI.Claim.CallerContract "card:path-selector" (ArmCertPipe.PathOK (ArmCertValue.extend inputs PipeR14.D_c12) PipeR14.guards_c12)
  a23 : CertiFFI.Claim.DeploymentObligation "card:data-starts" (PipeR14.Physical.DataStartsR14 mapping p (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte PipeR14.dataSites_c12 PipeR14.regions_c12 (PipeR14.AccessAnchors.sites_c12 p) sc base)
  a24 : CertiFFI.Claim.CallerContract "card:pins-agree" (PipeR14.PinsAgree p PipeR14.rs_c12 PipeR14.forms_c12 inputs)
  a25 : CertiFFI.Claim.DeploymentObligation "E34" ((List.map (fun x => x.logical) spec.logicalRows).Nodup)
  a28 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ArmCert.Translate.Model.ImageTableSeparated sc base mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a29 : CertiFFI.Claim.DeploymentObligation "card:load-base-page" (base.toNat % 4096 = 0)
  a30 : CertiFFI.Claim.DeploymentObligation "E31" (base.toNat < 2 ^ 54)
  a31 : CertiFFI.Claim.DeploymentObligation "card:consumer-map-agrees" (ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table))
  a32 : CertiFFI.Claim.RunCheck "card:budget" (PipeR14.plan_c12.length ≤ budget)
  a67 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/covered" (∀ (row : ArmCert.Translate.Model.PermissionRow), row ∈ rows → row.slot ∈ (ArmCert.Translate.Model.rowsFootprint spec.imageRows).slots)
  a68 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/topology" (ArmCert.Translate.Model.TopologyImageAt spec (ArmBridge.CruxGenGuarded.beforeFetchState entry))
  a69 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/attributes" (ArmCert.Translate.Model.AttributeImage (ArmCert.Translate.Model.rowsObserve spec.imageRows) (sourceAttributes rho caller) (ArmBridge.CruxGenGuarded.beforeFetchState entry).mem)
  a70 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/writeback" (ArmCert.Translate.Model.WriteBackAttributeImage (ArmCert.Translate.Model.rowsObserve spec.imageRows) (sourceAttributes rho caller) (ArmBridge.CruxGenGuarded.beforeFetchState entry).mem)
  a71 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/permissions" (ArmCert.Translate.Model.PermissionImage rows spec.params (ArmBridge.CruxGenGuarded.beforeFetchState entry).regs spec.controls (ArmBridge.CruxGenGuarded.beforeFetchState entry).mem)
  a133 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pc" (entry.regs._PC = base + PipeR14.offset_c12 0)
  a134 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/closed" (ArmCert.Translate.Model.ClosedMembershipAt spec (sourceAttributes rho caller) rows mapping (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table) (ArmBridge.CruxGenGuarded.beforeFetchState entry))
  a135 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/placed" (MemReloc.ImageOn sc (ArmCert.Translate.Model.StaticPie.referenceImageI bytes base ifunc) entry base mapping)
  a222 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/raw" (ArmCertWalk.RawImageAt spec.imageRows entry.mem)
  a223 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/noUpd" (∀ (wr : Bool) (acc : ArmFull.AccessDescriptor), ArmCert.Translate.Model.DataShape wr acc → ArmCertWalk.NoUpdateRows (have __src := spec.params; { ha := __src.ha, hd := __src.hd, tbi := __src.tbi, tbid := __src.tbid, nfd := __src.nfd, e0pd := __src.e0pd, d128 := __src.d128, aie := __src.aie, mair2 := __src.mair2, ds := __src.ds, ps := __src.ps, txsz := __src.txsz, epan := __src.epan, dct := __src.dct, nv1 := __src.nv1, cmow := __src.cmow, pnch := __src.pnch, disch := __src.disch, haft := ArmCert.Translate.Model.hostHAFT entry.regs, mtx := __src.mtx, skl := __src.skl, pie := __src.pie, pir := __src.pir, pire0 := __src.pire0, emec := __src.emec, amec := __src.amec, t0sz := __src.t0sz, t1sz := __src.t1sz, uwxn := __src.uwxn, tgx := __src.tgx, irgn := __src.irgn, orgn := __src.orgn, sh := __src.sh, hpd := __src.hpd, ee := __src.ee, wxn := __src.wxn, ntlsmd := __src.ntlsmd, dc := __src.dc, sif := __src.sif, mair := __src.mair }) acc spec.imageRows = true)
  a255 : CertiFFI.Claim.DeploymentObligation "card:runtime-initial/extra" (ArmCertPipe.AgreesAt mapping (PipeR14.pinv p) PipeR14.regions_c12 PipeR14.σ0_c12 inputs PipeR14.plan_c12 0 entry)
  a256 : CertiFFI.Claim.DeploymentObligation "card:runtime-initial/statusRows" (NativeMteTagCheck.TagStatusRows entry (entry.choiceOcc.getD 1354 0) ReleaseProfile.DefaultRuntime.capacity_c12)
  a257 : CertiFFI.Claim.DeploymentObligation "card:runtime14-view-agree" (ReleaseR14.VA.ViewAgree_c12 p mapping)

#check "CURRENT_DECL GB10.Runtime.fullpc_c1_explicit_c12"
def fullpc_c1_explicit_c12 (real : Type) [inst : Sail.SailReal real] {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (cfg : Configuration rho caller) (entry : ArmBridge.Draft.NativeState)
    (ag : AgreesAt cfg entry.regs) (sspec : SourceSpec rho caller spec)
    (res : FullPCResidual_c12 spec rows mapping table sc bytes base ifunc p budget inputs rho caller entry) :=
  fullpcFromSource_c12 real spec rows mapping table sc bytes base ifunc p budget inputs rho caller cfg entry ag sspec res.timers res.a10 res.a11 res.a17 res.a18 res.a19 res.a20 res.a21 res.a22 res.a23 res.a24 res.a25 res.a28 res.a29 res.a30 res.a31 res.a32 res.a67 res.a68 res.a69 res.a70 res.a71 res.a133 res.a134 res.a135 res.a222 res.a223 res.a255 res.a256 res.a257

#check "CURRENT_DECL GB10.Runtime.fullpc_imageLoaded_c12"
/-- Runtime ImageLoadedAsReviewed: the reviewed image (R14Scoped.slices + closure code words) is placed. -/
theorem fullpc_imageLoaded_c12 {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (entry : ArmBridge.Draft.NativeState)
    (res : FullPCResidual_c12 spec rows mapping table sc bytes base ifunc p budget inputs rho caller entry) :
    MemReloc.ImageOn sc (ArmCert.Translate.Model.StaticPie.referenceImageI bytes base ifunc) entry base mapping ∧ ArmCert.Translate.Model.StaticPie.Binds bytes R14Scoped.slices ∧ R14E17.CodeBinds bytes :=
  ⟨res.a135.holds, res.a10.holds, res.a11.holds⟩

#check "CURRENT_DECL GB10.Runtime.ctFromSource_c12"
/-- Runtime ct c12 C1 at the canonical source: 424 atoms produced from entry
agreement, 49 explicit inputs (program/memory/caller data and Heap-retained classes). -/
def ctFromSource_c12 (real : Type) [inst : Sail.SailReal real] {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs1 : List (BitVec 64))
    (inputs2 : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
    (cfg1 : Configuration rho callers.first) (cfg2 : Configuration rho callers.second)
    (entry1 entry2 : ArmBridge.Draft.NativeState)
    (ag1 : AgreesAt cfg1 entry1.regs) (ag2 : AgreesAt cfg2 entry2.regs)
    (sspec : SourceSpec rho callers.first spec)
    (timers1 : TimersQuiet entry1.regs budget) (timers2 : TimersQuiet entry2.regs budget) :=
  fun (a10 : _) (a11 : _) (a16 : _) (a17 : _) (a18 : _) (a19 : _) (a20 : _) (a21 : _) (a25 : _) (a26 : _) (a27 : _) (a29 : _) (a30 : _) (a31 : _) (a32 : _) (a33 : _) (a68 : _) (a69 : _) (a70 : _) (a71 : _) (a72 : _) (a134 : _) (a135 : _) (a136 : _) (a223 : _) (a224 : _) (a256 : _) (a257 : _) (a259 : _) (a260 : _) (a261 : _) (a263 : _) (a264 : _) (a265 : _) (a266 : _) (a267 : _) (a302 : _) (a303 : _) (a304 : _) (a305 : _) (a306 : _) (a368 : _) (a369 : _) (a370 : _) (a457 : _) (a458 : _) (a490 : _) (a491 : _) (a492 : _) =>
    @ReleaseProfile.DefaultRuntimeCards.card_release_ct_c12
      real inst domain spec (sourceAttributes rho callers.first) rows
      mapping table sc bytes a10 a11
      base ifunc p budget a16 a17
      a18 a19 a20 a21 (sourceCatalogue rho callers.first) (sourceCatalogue rho callers.first)
      inputs1 a25 a26 a27 entry1 a29
      a30 a31 a32 a33 ⟨feature_at cfg1 entry1 ag1 4 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 232 (by decide) false _ rfl⟩
      ⟨quiet_spe cfg1 entry1 ag1⟩ ⟨pstate_EL cfg1 entry1 ag1⟩ ⟨pstate_nRW cfg1 entry1 ag1⟩ ⟨field32_EDECR_RCE _ _ _ (control32_entry cfg1 entry1 ag1 .EDECR)⟩ ⟨field32_CTIDEVCTL_RCE _ _ _ (control32_entry cfg1 entry1 ag1 .CTIDEVCTL)⟩ ⟨quiet_edscr_status cfg1 entry1 ag1⟩
      ⟨quiet_edesr cfg1 entry1 ag1⟩ ⟨quiet_branch cfg1 entry1 ag1⟩ ⟨quiet_emulator cfg1 entry1 ag1⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg1 entry1 ag1 .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg1 entry1 ag1 .HCR_EL2 (by decide))⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg1 entry1 ag1 .SCR_EL3 (by decide))⟩
      ⟨field_PMBLIMITR_EL1_E _ _ _ (control_entry cfg1 entry1 ag1 .PMBLIMITR_EL1 (by decide))⟩ ⟨field_MDSCR_EL1_SS _ _ _ (control_entry cfg1 entry1 ag1 .MDSCR_EL1 (by decide))⟩ ⟨quiet_pmbsr cfg1 entry1 ag1⟩ ⟨pstate_A cfg1 entry1 ag1⟩ ⟨pstate_I cfg1 entry1 ag1⟩ ⟨pstate_F cfg1 entry1 ag1⟩
      ⟨pstate_IL cfg1 entry1 ag1⟩ ⟨pstate_SS cfg1 entry1 ag1⟩ ⟨pstate_BTYPE cfg1 entry1 ag1⟩ ⟨quiet_btype_next cfg1 entry1 ag1⟩ ⟨feature_at cfg1 entry1 ag1 0 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 1 (by decide) false _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 2 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 3 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 5 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 6 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 7 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 54 (by decide) true _ rfl⟩
      ⟨field_MDSCR_EL1_MDE _ _ _ (control_entry cfg1 entry1 ag1 .MDSCR_EL1 (by decide))⟩ ⟨field32_EDSCR_HDE _ _ _ (control32_entry cfg1 entry1 ag1 ._EDSCR)⟩ a68 a69 a70 a71
      a72 ⟨feature_at cfg1 entry1 ag1 7 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 3 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 232 (by decide) false _ rfl⟩ ⟨pstate_nRW cfg1 entry1 ag1⟩ ⟨field_TCR_EL2_TG0 _ _ _ (control_before_TCR_EL2 cfg1 entry1 ag1)⟩
      ⟨field_HCR_EL2_E2H _ _ _ (control_before_HCR_EL2 cfg1 entry1 ag1)⟩ ⟨tcr2_guard_D128 cfg1 entry1 ag1⟩ ⟨tcr2_guard_AIE cfg1 entry1 ag1⟩ ⟨tcr2_guard_PnCH cfg1 entry1 ag1⟩ ⟨tcr_ds_before cfg1 entry1 ag1⟩ ⟨sspec.regime⟩
      ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.ha d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.hd d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pie d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.hpd d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pir d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pire0 d⟩
      ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.overlay d⟩ ⟨by rw [sspec.physical]; exact legalPAMax_source _ _⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); rw [sspec.physical]; rfl⟩ ⟨by show entry1.regs.FeatureImpl[69]! = _; rw [sspec.physical, getElem!_pos _ 69 (by decide)]; exact actual_coordinate cfg1 entry1.regs ag1 ⟨.feature 69, rfl⟩⟩ ⟨by show entry1.regs.FeatureImpl[156]! = _; rw [sspec.physical, getElem!_pos _ 156 (by decide)]; exact actual_coordinate cfg1 entry1.regs ag1 ⟨.feature 156, rfl⟩⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); rw [sspec.physical]; rfl⟩
      ⟨field_SCTLR_EL2_EE _ _ _ (control_before_SCTLR_EL2 cfg1 entry1 ag1)⟩ ⟨attribute_mair cfg1 entry1 ag1⟩ ⟨attribute_xs cfg1 entry1 ag1⟩ ⟨attribute_mte2 cfg1 entry1 ag1⟩ ⟨Or.inl (pstate_EL cfg1 entry1 ag1)⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsHa d⟩
      ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsHd d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsPie d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsWxn d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsMtx d⟩ ⟨rfl⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.normalizedTxsz d⟩
      ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardTbi d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardTbid d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardNfd d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardE0pd d⟩ ⟨by have hr := regs_eq_source cfg1 entry1.regs ag1; generalize dataOf entry1.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.rawFault d⟩ ⟨translation_enabled cfg1 entry1 ag1⟩
      ⟨quiet_tlb cfg1 entry1 ag1⟩ ⟨by show entry1.regs.FeatureImpl[4]! = true; exact feature_at cfg1 entry1 ag1 4 (by decide) true _ rfl⟩ ⟨pstate_EL cfg1 entry1 ag1⟩ ⟨pstate_nRW cfg1 entry1 ag1⟩ ⟨field_SCR_EL3_RW _ _ _ (control_entry cfg1 entry1 ag1 .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_RW _ _ _ (control_entry cfg1 entry1 ag1 .HCR_EL2 (by decide))⟩
      ⟨quiet_spe cfg1 entry1 ag1⟩ ⟨pmintenclr_zero cfg1 entry1 ag1⟩ ⟨field_BRBFCR_EL1_PAUSED _ _ _ (control_entry cfg1 entry1 ag1 .BRBFCR_EL1 (by decide))⟩ ⟨pmu_lower cfg1 entry1 ag1⟩ ⟨pmu_upper cfg1 entry1 ag1⟩ ⟨field32_CNTCR_SCEN _ _ _ (control32_entry cfg1 entry1 ag1 .CNTCR)⟩
      ⟨timers1.cntp⟩ ⟨timers1.cnthp⟩ ⟨timers1.cnthps⟩ ⟨timers1.cntps⟩ ⟨timers1.cntv⟩ ⟨timers1.cnthv⟩
      ⟨timers1.cnthvs⟩ ⟨quiet_gic cfg1 entry1 ag1⟩ a134 a135 a136 ⟨feature_at cfg1 entry1 ag1 0 (by decide) false _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 1 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 2 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 3 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 4 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 5 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 6 (by decide) true _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 7 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 12 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 153 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 13 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 143 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 230 (by decide) false _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 123 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 45 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 144 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 103 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 60 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 126 (by decide) true _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 185 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 105 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 145 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 89 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 107 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 27 (by decide) true _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 65 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 130 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 108 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 131 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 67 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 92 (by decide) true _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 93 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 110 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 50 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 111 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 171 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 133 (by decide) true _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 95 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 200 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 36 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 53 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 232 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 138 (by decide) true _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 40 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 41 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 76 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 77 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 78 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 79 (by decide) true _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 233 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 234 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 235 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 236 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 81 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 221 (by decide) true _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 222 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 223 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 224 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 225 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 226 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 227 (by decide) false _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 165 (by decide) true _ rfl⟩ ⟨num_breakpoints cfg1 entry1 ag1⟩ ⟨num_watchpoints cfg1 entry1 ag1⟩ ⟨num_ctx_breakpoints cfg1 entry1 ag1⟩ ⟨quiet_edscr_status cfg1 entry1 ag1⟩ ⟨quiet_spe cfg1 entry1 ag1⟩
      ⟨pstate_EL cfg1 entry1 ag1⟩ ⟨pstate_nRW cfg1 entry1 ag1⟩ ⟨pstate_IL cfg1 entry1 ag1⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg1 entry1 ag1 .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg1 entry1 ag1 .HCR_EL2 (by decide))⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg1 entry1 ag1 .SCR_EL3 (by decide))⟩
      ⟨field_SCR_EL3_NSE _ _ _ (control_entry cfg1 entry1 ag1 .SCR_EL3 (by decide))⟩ ⟨field_MDSCR_EL1_SS _ _ _ (control_entry cfg1 entry1 ag1 .MDSCR_EL1 (by decide))⟩ ⟨pstate_SS cfg1 entry1 ag1⟩ ⟨quiet_osuc cfg1 entry1 ag1⟩ ⟨field_PMBLIMITR_EL1_E _ _ _ (control_entry cfg1 entry1 ag1 .PMBLIMITR_EL1 (by decide))⟩ ⟨field_SCR_EL3_RW _ _ _ (control_entry cfg1 entry1 ag1 .SCR_EL3 (by decide))⟩
      ⟨field_SCR_EL3_EEL2 _ _ _ (control_entry cfg1 entry1 ag1 .SCR_EL3 (by decide))⟩ ⟨field_TCR_EL2_TBI0 _ _ _ (control_entry cfg1 entry1 ag1 .TCR_EL2 (by decide))⟩ ⟨field_TCR_EL2_TBID0 _ _ _ (control_entry cfg1 entry1 ag1 .TCR_EL2 (by decide))⟩ ⟨field_MDCR_EL3_NSPB _ _ _ (control_entry cfg1 entry1 ag1 .MDCR_EL3 (by decide))⟩ ⟨field_MDCR_EL3_NSPBE _ _ _ (control_entry cfg1 entry1 ag1 .MDCR_EL3 (by decide))⟩ ⟨feature_at cfg1 entry1 ag1 54 (by decide) true _ rfl⟩
      ⟨feature_at cfg1 entry1 ag1 245 (by decide) false _ rfl⟩ a223 a224 ⟨quiet_spe cfg1 entry1 ag1⟩ ⟨pstate_EL cfg1 entry1 ag1⟩ ⟨pstate_nRW cfg1 entry1 ag1⟩
      ⟨feature_at cfg1 entry1 ag1 232 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 54 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 4 (by decide) true _ rfl⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg1 entry1 ag1 .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg1 entry1 ag1 .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg1 entry1 ag1 .HCR_EL2 (by decide))⟩
      ⟨field_SCTLR_EL2_E0E _ _ _ (control_entry cfg1 entry1 ag1 .SCTLR_EL2 (by decide))⟩ ⟨feature_at cfg1 entry1 ag1 2 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 6 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 54 (by decide) true _ rfl⟩ ⟨pstate_EL cfg1 entry1 ag1⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg1 entry1 ag1 .SCR_EL3 (by decide))⟩
      ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg1 entry1 ag1 .HCR_EL2 (by decide))⟩ ⟨field_MDSCR_EL1_MDE _ _ _ (control_entry cfg1 entry1 ag1 .MDSCR_EL1 (by decide))⟩ ⟨field32_EDSCR_HDE _ _ _ (control32_entry cfg1 entry1 ag1 ._EDSCR)⟩ ⟨⟨feature_at cfg1 entry1 ag1 7 (by decide) true _ rfl, feature_at cfg1 entry1 ag1 3 (by decide) false _ rfl, feature_at cfg1 entry1 ag1 227 (by decide) false _ rfl, feature_at cfg1 entry1 ag1 111 (by decide) true _ rfl⟩⟩ ⟨dcache_entry cfg1 entry1 ag1⟩ ⟨pstate_EL cfg1 entry1 ag1⟩
      ⟨pstate_nRW cfg1 entry1 ag1⟩ ⟨feature_at cfg1 entry1 ag1 4 (by decide) true _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 232 (by decide) false _ rfl⟩ ⟨feature_at cfg1 entry1 ag1 54 (by decide) true _ rfl⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg1 entry1 ag1 .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg1 entry1 ag1 .HCR_EL2 (by decide))⟩
      ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg1 entry1 ag1 .HCR_EL2 (by decide))⟩ ⟨pstate_TCO cfg1 entry1 ag1⟩ ⟨field_SCTLR_EL2_TCF0 _ _ _ (control_entry cfg1 entry1 ag1 .SCTLR_EL2 (by decide))⟩ ⟨preparation cfg1 entry1 ag1⟩ a256 a257
      inputs2 a259 a260 a261 entry2 a263
      a264 a265 a266 a267 ⟨feature_at cfg2 entry2 ag2 4 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 232 (by decide) false _ rfl⟩
      ⟨quiet_spe cfg2 entry2 ag2⟩ ⟨pstate_EL cfg2 entry2 ag2⟩ ⟨pstate_nRW cfg2 entry2 ag2⟩ ⟨field32_EDECR_RCE _ _ _ (control32_entry cfg2 entry2 ag2 .EDECR)⟩ ⟨field32_CTIDEVCTL_RCE _ _ _ (control32_entry cfg2 entry2 ag2 .CTIDEVCTL)⟩ ⟨quiet_edscr_status cfg2 entry2 ag2⟩
      ⟨quiet_edesr cfg2 entry2 ag2⟩ ⟨quiet_branch cfg2 entry2 ag2⟩ ⟨quiet_emulator cfg2 entry2 ag2⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg2 entry2 ag2 .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg2 entry2 ag2 .HCR_EL2 (by decide))⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg2 entry2 ag2 .SCR_EL3 (by decide))⟩
      ⟨field_PMBLIMITR_EL1_E _ _ _ (control_entry cfg2 entry2 ag2 .PMBLIMITR_EL1 (by decide))⟩ ⟨field_MDSCR_EL1_SS _ _ _ (control_entry cfg2 entry2 ag2 .MDSCR_EL1 (by decide))⟩ ⟨quiet_pmbsr cfg2 entry2 ag2⟩ ⟨pstate_A cfg2 entry2 ag2⟩ ⟨pstate_I cfg2 entry2 ag2⟩ ⟨pstate_F cfg2 entry2 ag2⟩
      ⟨pstate_IL cfg2 entry2 ag2⟩ ⟨pstate_SS cfg2 entry2 ag2⟩ ⟨pstate_BTYPE cfg2 entry2 ag2⟩ ⟨quiet_btype_next cfg2 entry2 ag2⟩ ⟨feature_at cfg2 entry2 ag2 0 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 1 (by decide) false _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 2 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 3 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 5 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 6 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 7 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 54 (by decide) true _ rfl⟩
      ⟨field_MDSCR_EL1_MDE _ _ _ (control_entry cfg2 entry2 ag2 .MDSCR_EL1 (by decide))⟩ ⟨field32_EDSCR_HDE _ _ _ (control32_entry cfg2 entry2 ag2 ._EDSCR)⟩ a302 a303 a304 a305
      a306 ⟨feature_at cfg2 entry2 ag2 7 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 3 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 232 (by decide) false _ rfl⟩ ⟨pstate_nRW cfg2 entry2 ag2⟩ ⟨field_TCR_EL2_TG0 _ _ _ (control_before_TCR_EL2 cfg2 entry2 ag2)⟩
      ⟨field_HCR_EL2_E2H _ _ _ (control_before_HCR_EL2 cfg2 entry2 ag2)⟩ ⟨tcr2_guard_D128 cfg2 entry2 ag2⟩ ⟨tcr2_guard_AIE cfg2 entry2 ag2⟩ ⟨tcr2_guard_PnCH cfg2 entry2 ag2⟩ ⟨tcr_ds_before cfg2 entry2 ag2⟩ ⟨sspec.regime⟩
      ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.ha d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.hd d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pie d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.hpd d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pir d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pire0 d⟩
      ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.overlay d⟩ ⟨by rw [sspec.physical]; exact legalPAMax_source _ _⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); rw [sspec.physical]; rfl⟩ ⟨by show entry2.regs.FeatureImpl[69]! = _; rw [sspec.physical, getElem!_pos _ 69 (by decide)]; exact actual_coordinate cfg2 entry2.regs ag2 ⟨.feature 69, rfl⟩⟩ ⟨by show entry2.regs.FeatureImpl[156]! = _; rw [sspec.physical, getElem!_pos _ 156 (by decide)]; exact actual_coordinate cfg2 entry2.regs ag2 ⟨.feature 156, rfl⟩⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); rw [sspec.physical]; rfl⟩
      ⟨field_SCTLR_EL2_EE _ _ _ (control_before_SCTLR_EL2 cfg2 entry2 ag2)⟩ ⟨attribute_mair_second (callers.first) cfg2 entry2 ag2⟩ ⟨attribute_xs_second (callers.first) cfg2 entry2 ag2⟩ ⟨attribute_mte2_second (callers.first) cfg2 entry2 ag2⟩ ⟨Or.inl (pstate_EL cfg2 entry2 ag2)⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsHa d⟩
      ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsHd d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsPie d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsWxn d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsMtx d⟩ ⟨rfl⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.normalizedTxsz d⟩
      ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardTbi d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardTbid d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardNfd d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardE0pd d⟩ ⟨by have hr := regs_eq_source cfg2 entry2.regs ag2; generalize dataOf entry2.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.rawFault d⟩ ⟨translation_enabled cfg2 entry2 ag2⟩
      ⟨quiet_tlb cfg2 entry2 ag2⟩ ⟨by show entry2.regs.FeatureImpl[4]! = true; exact feature_at cfg2 entry2 ag2 4 (by decide) true _ rfl⟩ ⟨pstate_EL cfg2 entry2 ag2⟩ ⟨pstate_nRW cfg2 entry2 ag2⟩ ⟨field_SCR_EL3_RW _ _ _ (control_entry cfg2 entry2 ag2 .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_RW _ _ _ (control_entry cfg2 entry2 ag2 .HCR_EL2 (by decide))⟩
      ⟨quiet_spe cfg2 entry2 ag2⟩ ⟨pmintenclr_zero cfg2 entry2 ag2⟩ ⟨field_BRBFCR_EL1_PAUSED _ _ _ (control_entry cfg2 entry2 ag2 .BRBFCR_EL1 (by decide))⟩ ⟨pmu_lower cfg2 entry2 ag2⟩ ⟨pmu_upper cfg2 entry2 ag2⟩ ⟨field32_CNTCR_SCEN _ _ _ (control32_entry cfg2 entry2 ag2 .CNTCR)⟩
      ⟨timers2.cntp⟩ ⟨timers2.cnthp⟩ ⟨timers2.cnthps⟩ ⟨timers2.cntps⟩ ⟨timers2.cntv⟩ ⟨timers2.cnthv⟩
      ⟨timers2.cnthvs⟩ ⟨quiet_gic cfg2 entry2 ag2⟩ a368 a369 a370 ⟨feature_at cfg2 entry2 ag2 0 (by decide) false _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 1 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 2 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 3 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 4 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 5 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 6 (by decide) true _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 7 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 12 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 153 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 13 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 143 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 230 (by decide) false _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 123 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 45 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 144 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 103 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 60 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 126 (by decide) true _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 185 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 105 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 145 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 89 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 107 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 27 (by decide) true _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 65 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 130 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 108 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 131 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 67 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 92 (by decide) true _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 93 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 110 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 50 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 111 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 171 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 133 (by decide) true _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 95 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 200 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 36 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 53 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 232 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 138 (by decide) true _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 40 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 41 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 76 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 77 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 78 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 79 (by decide) true _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 233 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 234 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 235 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 236 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 81 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 221 (by decide) true _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 222 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 223 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 224 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 225 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 226 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 227 (by decide) false _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 165 (by decide) true _ rfl⟩ ⟨num_breakpoints cfg2 entry2 ag2⟩ ⟨num_watchpoints cfg2 entry2 ag2⟩ ⟨num_ctx_breakpoints cfg2 entry2 ag2⟩ ⟨quiet_edscr_status cfg2 entry2 ag2⟩ ⟨quiet_spe cfg2 entry2 ag2⟩
      ⟨pstate_EL cfg2 entry2 ag2⟩ ⟨pstate_nRW cfg2 entry2 ag2⟩ ⟨pstate_IL cfg2 entry2 ag2⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg2 entry2 ag2 .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg2 entry2 ag2 .HCR_EL2 (by decide))⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg2 entry2 ag2 .SCR_EL3 (by decide))⟩
      ⟨field_SCR_EL3_NSE _ _ _ (control_entry cfg2 entry2 ag2 .SCR_EL3 (by decide))⟩ ⟨field_MDSCR_EL1_SS _ _ _ (control_entry cfg2 entry2 ag2 .MDSCR_EL1 (by decide))⟩ ⟨pstate_SS cfg2 entry2 ag2⟩ ⟨quiet_osuc cfg2 entry2 ag2⟩ ⟨field_PMBLIMITR_EL1_E _ _ _ (control_entry cfg2 entry2 ag2 .PMBLIMITR_EL1 (by decide))⟩ ⟨field_SCR_EL3_RW _ _ _ (control_entry cfg2 entry2 ag2 .SCR_EL3 (by decide))⟩
      ⟨field_SCR_EL3_EEL2 _ _ _ (control_entry cfg2 entry2 ag2 .SCR_EL3 (by decide))⟩ ⟨field_TCR_EL2_TBI0 _ _ _ (control_entry cfg2 entry2 ag2 .TCR_EL2 (by decide))⟩ ⟨field_TCR_EL2_TBID0 _ _ _ (control_entry cfg2 entry2 ag2 .TCR_EL2 (by decide))⟩ ⟨field_MDCR_EL3_NSPB _ _ _ (control_entry cfg2 entry2 ag2 .MDCR_EL3 (by decide))⟩ ⟨field_MDCR_EL3_NSPBE _ _ _ (control_entry cfg2 entry2 ag2 .MDCR_EL3 (by decide))⟩ ⟨feature_at cfg2 entry2 ag2 54 (by decide) true _ rfl⟩
      ⟨feature_at cfg2 entry2 ag2 245 (by decide) false _ rfl⟩ a457 a458 ⟨quiet_spe cfg2 entry2 ag2⟩ ⟨pstate_EL cfg2 entry2 ag2⟩ ⟨pstate_nRW cfg2 entry2 ag2⟩
      ⟨feature_at cfg2 entry2 ag2 232 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 54 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 4 (by decide) true _ rfl⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg2 entry2 ag2 .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg2 entry2 ag2 .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg2 entry2 ag2 .HCR_EL2 (by decide))⟩
      ⟨field_SCTLR_EL2_E0E _ _ _ (control_entry cfg2 entry2 ag2 .SCTLR_EL2 (by decide))⟩ ⟨feature_at cfg2 entry2 ag2 2 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 6 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 54 (by decide) true _ rfl⟩ ⟨pstate_EL cfg2 entry2 ag2⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg2 entry2 ag2 .SCR_EL3 (by decide))⟩
      ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg2 entry2 ag2 .HCR_EL2 (by decide))⟩ ⟨field_MDSCR_EL1_MDE _ _ _ (control_entry cfg2 entry2 ag2 .MDSCR_EL1 (by decide))⟩ ⟨field32_EDSCR_HDE _ _ _ (control32_entry cfg2 entry2 ag2 ._EDSCR)⟩ ⟨⟨feature_at cfg2 entry2 ag2 7 (by decide) true _ rfl, feature_at cfg2 entry2 ag2 3 (by decide) false _ rfl, feature_at cfg2 entry2 ag2 227 (by decide) false _ rfl, feature_at cfg2 entry2 ag2 111 (by decide) true _ rfl⟩⟩ ⟨dcache_entry cfg2 entry2 ag2⟩ ⟨pstate_EL cfg2 entry2 ag2⟩
      ⟨pstate_nRW cfg2 entry2 ag2⟩ ⟨feature_at cfg2 entry2 ag2 4 (by decide) true _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 232 (by decide) false _ rfl⟩ ⟨feature_at cfg2 entry2 ag2 54 (by decide) true _ rfl⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg2 entry2 ag2 .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg2 entry2 ag2 .HCR_EL2 (by decide))⟩
      ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg2 entry2 ag2 .HCR_EL2 (by decide))⟩ ⟨pstate_TCO cfg2 entry2 ag2⟩ ⟨field_SCTLR_EL2_TCF0 _ _ _ (control_entry cfg2 entry2 ag2 .SCTLR_EL2 (by decide))⟩ ⟨preparation_second (callers.first) cfg2 entry2 ag2⟩ a490 a491
      a492

#check "CURRENT_DECL GB10.Runtime.CTResidual_c12"
/-- Retained original ct c12 inputs, explicit at the source substitution; timers named premise. -/
structure CTResidual_c12 {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs1 : List (BitVec 64))
    (inputs2 : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho) (entry1 entry2 : ArmBridge.Draft.NativeState) : Prop where
  timers1 : TimersQuiet entry1.regs budget
  timers2 : TimersQuiet entry2.regs budget
  a10 : CertiFFI.Claim.RunCheck "card:r14-code-binds" (ArmCert.Translate.Model.StaticPie.Binds bytes R14Scoped.slices)
  a11 : CertiFFI.Claim.RunCheck "card:r14-code-binds" (R14E17.CodeBinds bytes)
  a16 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/covers" (PipeR14.ScopeCovers sc)
  a17 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/separated" (ArmCert.Translate.Model.ImageTableSeparated sc base mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a18 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/contiguous" (∀ (c : Nat × Nat), c ∈ R14E17.codeVAs → ArmCert.Translate.Model.ImageWordContiguous mapping base c.fst)
  a19 : CertiFFI.Claim.DeploymentObligation "card:runtime-code-static/notMMIO" (∀ (c : Nat × Nat), c ∈ R14E17.codeVAs → ArmCertWalk.MappedNotMMIO mapping (MemReloc.imageAddress base c.fst))
  a20 : CertiFFI.Claim.DeploymentObligation "card:data-starts" (PipeR14.Physical.DataStartsR14 mapping p (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte PipeR14.dataSites_c12 PipeR14.regions_c12 (PipeR14.AccessAnchors.sites_c12 p) sc base)
  a21 : CertiFFI.Claim.DeploymentObligation "E34" ((List.map (fun x => x.logical) spec.logicalRows).Nodup)
  a25 : CertiFFI.Claim.CallerContract "card:input-vector-shape" (inputs1.length = PipeR14.n0_c12)
  a26 : CertiFFI.Claim.CallerContract "card:path-selector" (ArmCertPipe.PathOK (ArmCertValue.extend inputs1 PipeR14.D_c12) PipeR14.guards_c12)
  a27 : CertiFFI.Claim.CallerContract "card:pins-agree" (PipeR14.PinsAgree p PipeR14.rs_c12 PipeR14.forms_c12 inputs1)
  a29 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ArmCert.Translate.Model.ImageTableSeparated sc base mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a30 : CertiFFI.Claim.DeploymentObligation "card:load-base-page" (base.toNat % 4096 = 0)
  a31 : CertiFFI.Claim.DeploymentObligation "E31" (base.toNat < 2 ^ 54)
  a32 : CertiFFI.Claim.DeploymentObligation "card:consumer-map-agrees" (ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table))
  a33 : CertiFFI.Claim.RunCheck "card:budget" (PipeR14.plan_c12.length ≤ budget)
  a68 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/covered" (∀ (row : ArmCert.Translate.Model.PermissionRow), row ∈ rows → row.slot ∈ (ArmCert.Translate.Model.rowsFootprint spec.imageRows).slots)
  a69 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/topology" (ArmCert.Translate.Model.TopologyImageAt spec (ArmBridge.CruxGenGuarded.beforeFetchState entry1))
  a70 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/attributes" (ArmCert.Translate.Model.AttributeImage (ArmCert.Translate.Model.rowsObserve spec.imageRows) (sourceAttributes rho callers.first) (ArmBridge.CruxGenGuarded.beforeFetchState entry1).mem)
  a71 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/writeback" (ArmCert.Translate.Model.WriteBackAttributeImage (ArmCert.Translate.Model.rowsObserve spec.imageRows) (sourceAttributes rho callers.first) (ArmBridge.CruxGenGuarded.beforeFetchState entry1).mem)
  a72 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/permissions" (ArmCert.Translate.Model.PermissionImage rows spec.params (ArmBridge.CruxGenGuarded.beforeFetchState entry1).regs spec.controls (ArmBridge.CruxGenGuarded.beforeFetchState entry1).mem)
  a134 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pc" (entry1.regs._PC = base + PipeR14.offset_c12 0)
  a135 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/closed" (ArmCert.Translate.Model.ClosedMembershipAt spec (sourceAttributes rho callers.first) rows mapping (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table) (ArmBridge.CruxGenGuarded.beforeFetchState entry1))
  a136 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/placed" (MemReloc.ImageOn sc (ArmCert.Translate.Model.StaticPie.referenceImageI bytes base ifunc) entry1 base mapping)
  a223 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/raw" (ArmCertWalk.RawImageAt spec.imageRows entry1.mem)
  a224 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/noUpd" (∀ (wr : Bool) (acc : ArmFull.AccessDescriptor), ArmCert.Translate.Model.DataShape wr acc → ArmCertWalk.NoUpdateRows (have __src := spec.params; { ha := __src.ha, hd := __src.hd, tbi := __src.tbi, tbid := __src.tbid, nfd := __src.nfd, e0pd := __src.e0pd, d128 := __src.d128, aie := __src.aie, mair2 := __src.mair2, ds := __src.ds, ps := __src.ps, txsz := __src.txsz, epan := __src.epan, dct := __src.dct, nv1 := __src.nv1, cmow := __src.cmow, pnch := __src.pnch, disch := __src.disch, haft := ArmCert.Translate.Model.hostHAFT entry1.regs, mtx := __src.mtx, skl := __src.skl, pie := __src.pie, pir := __src.pir, pire0 := __src.pire0, emec := __src.emec, amec := __src.amec, t0sz := __src.t0sz, t1sz := __src.t1sz, uwxn := __src.uwxn, tgx := __src.tgx, irgn := __src.irgn, orgn := __src.orgn, sh := __src.sh, hpd := __src.hpd, ee := __src.ee, wxn := __src.wxn, ntlsmd := __src.ntlsmd, dc := __src.dc, sif := __src.sif, mair := __src.mair }) acc spec.imageRows = true)
  a256 : CertiFFI.Claim.DeploymentObligation "card:runtime-initial/extra" (ArmCertPipe.AgreesAt mapping (PipeR14.pinv p) PipeR14.regions_c12 PipeR14.σ0_c12 inputs1 PipeR14.plan_c12 0 entry1)
  a257 : CertiFFI.Claim.DeploymentObligation "card:runtime-initial/statusRows" (NativeMteTagCheck.TagStatusRows entry1 (entry1.choiceOcc.getD 1354 0) ReleaseProfile.DefaultRuntime.capacity_c12)
  a259 : CertiFFI.Claim.CallerContract "card:input-vector-shape" (inputs2.length = PipeR14.n0_c12)
  a260 : CertiFFI.Claim.CallerContract "card:path-selector" (ArmCertPipe.PathOK (ArmCertValue.extend inputs2 PipeR14.D_c12) PipeR14.guards_c12)
  a261 : CertiFFI.Claim.CallerContract "card:pins-agree" (PipeR14.PinsAgree p PipeR14.rs_c12 PipeR14.forms_c12 inputs2)
  a263 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ArmCert.Translate.Model.ImageTableSeparated sc base mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a264 : CertiFFI.Claim.DeploymentObligation "card:load-base-page" (base.toNat % 4096 = 0)
  a265 : CertiFFI.Claim.DeploymentObligation "E31" (base.toNat < 2 ^ 54)
  a266 : CertiFFI.Claim.DeploymentObligation "card:consumer-map-agrees" (ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table))
  a267 : CertiFFI.Claim.RunCheck "card:budget" (PipeR14.plan_c12.length ≤ budget)
  a302 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/covered" (∀ (row : ArmCert.Translate.Model.PermissionRow), row ∈ rows → row.slot ∈ (ArmCert.Translate.Model.rowsFootprint spec.imageRows).slots)
  a303 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/topology" (ArmCert.Translate.Model.TopologyImageAt spec (ArmBridge.CruxGenGuarded.beforeFetchState entry2))
  a304 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/attributes" (ArmCert.Translate.Model.AttributeImage (ArmCert.Translate.Model.rowsObserve spec.imageRows) (sourceAttributes rho callers.first) (ArmBridge.CruxGenGuarded.beforeFetchState entry2).mem)
  a305 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/writeback" (ArmCert.Translate.Model.WriteBackAttributeImage (ArmCert.Translate.Model.rowsObserve spec.imageRows) (sourceAttributes rho callers.first) (ArmBridge.CruxGenGuarded.beforeFetchState entry2).mem)
  a306 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/permissions" (ArmCert.Translate.Model.PermissionImage rows spec.params (ArmBridge.CruxGenGuarded.beforeFetchState entry2).regs spec.controls (ArmBridge.CruxGenGuarded.beforeFetchState entry2).mem)
  a368 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pc" (entry2.regs._PC = base + PipeR14.offset_c12 0)
  a369 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/closed" (ArmCert.Translate.Model.ClosedMembershipAt spec (sourceAttributes rho callers.first) rows mapping (R14E17.consumerMap R14Plan.accesses_c12 R14Plan.codeWords_c12 R14Plan.entry_c12 p base.toNat mapping table) (ArmBridge.CruxGenGuarded.beforeFetchState entry2))
  a370 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/placed" (MemReloc.ImageOn sc (ArmCert.Translate.Model.StaticPie.referenceImageI bytes base ifunc) entry2 base mapping)
  a457 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/raw" (ArmCertWalk.RawImageAt spec.imageRows entry2.mem)
  a458 : CertiFFI.Claim.DeploymentObligation "card:runtime-default-initial/noUpd" (∀ (wr : Bool) (acc : ArmFull.AccessDescriptor), ArmCert.Translate.Model.DataShape wr acc → ArmCertWalk.NoUpdateRows (have __src := spec.params; { ha := __src.ha, hd := __src.hd, tbi := __src.tbi, tbid := __src.tbid, nfd := __src.nfd, e0pd := __src.e0pd, d128 := __src.d128, aie := __src.aie, mair2 := __src.mair2, ds := __src.ds, ps := __src.ps, txsz := __src.txsz, epan := __src.epan, dct := __src.dct, nv1 := __src.nv1, cmow := __src.cmow, pnch := __src.pnch, disch := __src.disch, haft := ArmCert.Translate.Model.hostHAFT entry2.regs, mtx := __src.mtx, skl := __src.skl, pie := __src.pie, pir := __src.pir, pire0 := __src.pire0, emec := __src.emec, amec := __src.amec, t0sz := __src.t0sz, t1sz := __src.t1sz, uwxn := __src.uwxn, tgx := __src.tgx, irgn := __src.irgn, orgn := __src.orgn, sh := __src.sh, hpd := __src.hpd, ee := __src.ee, wxn := __src.wxn, ntlsmd := __src.ntlsmd, dc := __src.dc, sif := __src.sif, mair := __src.mair }) acc spec.imageRows = true)
  a490 : CertiFFI.Claim.DeploymentObligation "card:runtime-initial/extra" (ArmCertPipe.AgreesAt mapping (PipeR14.pinv p) PipeR14.regions_c12 PipeR14.σ0_c12 inputs2 PipeR14.plan_c12 0 entry2)
  a491 : CertiFFI.Claim.DeploymentObligation "card:runtime-initial/statusRows" (NativeMteTagCheck.TagStatusRows entry2 (entry2.choiceOcc.getD 1354 0) ReleaseProfile.DefaultRuntime.capacity_c12)
  a492 : CertiFFI.Claim.DeploymentObligation "card:runtime14-view-agree" (ReleaseR14.VA.ViewAgree_c12 p mapping)

#check "CURRENT_DECL GB10.Runtime.ct_c1_explicit_c12"
def ct_c1_explicit_c12 (real : Type) [inst : Sail.SailReal real] {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs1 : List (BitVec 64))
    (inputs2 : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
    (cfg1 : Configuration rho callers.first) (cfg2 : Configuration rho callers.second)
    (entry1 entry2 : ArmBridge.Draft.NativeState)
    (ag1 : AgreesAt cfg1 entry1.regs) (ag2 : AgreesAt cfg2 entry2.regs)
    (sspec : SourceSpec rho callers.first spec)
    (res : CTResidual_c12 spec rows mapping table sc bytes base ifunc p budget inputs1 inputs2 rho callers entry1 entry2) :=
  ctFromSource_c12 real spec rows mapping table sc bytes base ifunc p budget inputs1 inputs2 rho callers cfg1 cfg2 entry1 entry2 ag1 ag2 sspec res.timers1 res.timers2 res.a10 res.a11 res.a16 res.a17 res.a18 res.a19 res.a20 res.a21 res.a25 res.a26 res.a27 res.a29 res.a30 res.a31 res.a32 res.a33 res.a68 res.a69 res.a70 res.a71 res.a72 res.a134 res.a135 res.a136 res.a223 res.a224 res.a256 res.a257 res.a259 res.a260 res.a261 res.a263 res.a264 res.a265 res.a266 res.a267 res.a302 res.a303 res.a304 res.a305 res.a306 res.a368 res.a369 res.a370 res.a457 res.a458 res.a490 res.a491 res.a492

#check "CURRENT_DECL GB10.Runtime.ct_imageLoaded_c12"
/-- Runtime ImageLoadedAsReviewed: the reviewed image (R14Scoped.slices + closure code words) is placed. -/
theorem ct_imageLoaded_c12 {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain)
    (rows : List ArmCert.Translate.Model.PermissionRow)
    (mapping : BitVec 64 → Option Nat)
    (table : Nat → Prop)
    (sc : Nat → Prop)
    (bytes : Array Nat)
    (base : BitVec 64)
    (ifunc : Nat → MemReloc.Word)
    (p : R14E17.Pins)
    (budget : Nat)
    (inputs1 : List (BitVec 64))
    (inputs2 : List (BitVec 64))
    (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho) (entry1 entry2 : ArmBridge.Draft.NativeState)
    (res : CTResidual_c12 spec rows mapping table sc bytes base ifunc p budget inputs1 inputs2 rho callers entry1 entry2) :
    MemReloc.ImageOn sc (ArmCert.Translate.Model.StaticPie.referenceImageI bytes base ifunc) entry1 base mapping ∧ MemReloc.ImageOn sc (ArmCert.Translate.Model.StaticPie.referenceImageI bytes base ifunc) entry2 base mapping ∧ ArmCert.Translate.Model.StaticPie.Binds bytes R14Scoped.slices ∧ R14E17.CodeBinds bytes :=
  ⟨res.a136.holds, res.a370.holds, res.a10.holds, res.a11.holds⟩

end ReleaseProfile.GB10.Runtime

#print axioms ReleaseProfile.GB10.Runtime.fullFromSource_c12
#print axioms ReleaseProfile.GB10.Runtime.full_c1_explicit_c12
#print axioms ReleaseProfile.GB10.Runtime.fullpcFromSource_c12
#print axioms ReleaseProfile.GB10.Runtime.fullpc_c1_explicit_c12
#print axioms ReleaseProfile.GB10.Runtime.ctFromSource_c12
#print axioms ReleaseProfile.GB10.Runtime.ct_c1_explicit_c12
