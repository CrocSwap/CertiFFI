import ReleaseProfile.GB10.HeapContext
import ReleaseProfile.GB10.StaticSplit

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-!
# Heap Initial0 C1 boundary over the canonical GB10 source

Original card ReleaseProfile.DefaultHeapCards.card_initial_0. Of the 260 original input atoms, 221 are produced
by exact-form producers from the actual-entry agreement(s) with the canonical source and
39 remain explicit inputs with their original wrapper/id/grade/proposition at the
source data substitution. The proof is the original card applied to every binder.
Generator: heap-port-d256/tools/gen_heap_port.py (no new producer or premise).
-/

namespace ReleaseProfile.GB10.Heap

open ReleaseProfile.MachineSource ReleaseProfile.GB10

#check "CURRENT_DECL GB10.Heap.initial0FromSource"
/-- Heap Initial0 C1: the original card at the canonical source; produced atoms discharged from
the entry agreement(s), every other atom an explicit input. -/
def initial0FromSource (real : Type) [inst : Sail.SailReal real] {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain) (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : ArmCert.Translate.Model.HeapV2E17.Pins) (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word) (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (tableRows : NativeSourceInit.Plan)
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState) (ag : AgreesAt cfg e.regs)
    (sspec : SourceSpec rho caller spec) (timers : TimersQuiet e.regs budget) :=
  fun (a16 : _) (a17 : _) (a18 : _) (a19 : _) (a20 : _) (a55 : _) (a56 : _) (a57 : _) (a58 : _) (a59 : _) (a121 : _) (a122 : _) (a123 : _) (a210 : _) (a211 : _) (a243 : _) (a244 : _) (a245 : _) (a246 : _) (a256 : _) (a257 : _) (a258 : _) (a259 : _) (a261 : CertiFFI.Claim.DeploymentObligation "card:body-entry/static" (ReleaseProfile.GB10.CodeStaticR mapping base (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)) (a262 : _) (a263 : _) (a264 : _) (a265 : _) (a266 : _) (a267 : _) (a268 : _) (a269 : _) (a270 : _) (a271 : _) (a272 : _) (a273 : _) (a274 : _) (a275 : _) (a276 : _) =>
    @ReleaseProfile.DefaultHeapCards.card_initial_0 real inst
      domain spec (sourceAttributes rho caller) rows mapping pins
      scope image loadBase base offS budget
      (sourceCatalogue rho caller) e a16 a17 a18 a19
      a20 ⟨feature_at cfg e ag 4 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 232 (by decide) false _ rfl⟩ ⟨quiet_spe cfg e ag⟩ ⟨pstate_EL cfg e ag⟩ ⟨pstate_nRW cfg e ag⟩
      ⟨field32_EDECR_RCE _ _ _ (control32_entry cfg e ag .EDECR)⟩ ⟨field32_CTIDEVCTL_RCE _ _ _ (control32_entry cfg e ag .CTIDEVCTL)⟩ ⟨quiet_edscr_status cfg e ag⟩ ⟨quiet_edesr cfg e ag⟩ ⟨quiet_branch cfg e ag⟩ ⟨quiet_emulator cfg e ag⟩
      ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg e ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg e ag .HCR_EL2 (by decide))⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg e ag .SCR_EL3 (by decide))⟩ ⟨field_PMBLIMITR_EL1_E _ _ _ (control_entry cfg e ag .PMBLIMITR_EL1 (by decide))⟩ ⟨field_MDSCR_EL1_SS _ _ _ (control_entry cfg e ag .MDSCR_EL1 (by decide))⟩ ⟨quiet_pmbsr cfg e ag⟩
      ⟨pstate_A cfg e ag⟩ ⟨pstate_I cfg e ag⟩ ⟨pstate_F cfg e ag⟩ ⟨pstate_IL cfg e ag⟩ ⟨pstate_SS cfg e ag⟩ ⟨pstate_BTYPE cfg e ag⟩
      ⟨quiet_btype_next cfg e ag⟩ ⟨feature_at cfg e ag 0 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 1 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 2 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 3 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 5 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 6 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 7 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 54 (by decide) true _ rfl⟩ ⟨field_MDSCR_EL1_MDE _ _ _ (control_entry cfg e ag .MDSCR_EL1 (by decide))⟩ ⟨field32_EDSCR_HDE _ _ _ (control32_entry cfg e ag ._EDSCR)⟩ a55
      a56 a57 a58 a59 ⟨feature_at cfg e ag 7 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 3 (by decide) false _ rfl⟩
      ⟨feature_at cfg e ag 232 (by decide) false _ rfl⟩ ⟨pstate_nRW cfg e ag⟩ ⟨field_TCR_EL2_TG0 _ _ _ (control_before_TCR_EL2 cfg e ag)⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_before_HCR_EL2 cfg e ag)⟩ ⟨tcr2_guard_D128 cfg e ag⟩ ⟨tcr2_guard_AIE cfg e ag⟩
      ⟨tcr2_guard_PnCH cfg e ag⟩ ⟨tcr_ds_before cfg e ag⟩ ⟨sspec.regime⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.ha d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.hd d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pie d⟩
      ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.hpd d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pir d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.pire0 d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.overlay d⟩ ⟨by rw [sspec.physical]; exact legalPAMax_source _ _⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); rw [sspec.physical]; rfl⟩
      ⟨by show e.regs.FeatureImpl[69]! = _; rw [sspec.physical, getElem!_pos _ 69 (by decide)]; exact actual_coordinate cfg e.regs ag ⟨.feature 69, rfl⟩⟩ ⟨by show e.regs.FeatureImpl[156]! = _; rw [sspec.physical, getElem!_pos _ 156 (by decide)]; exact actual_coordinate cfg e.regs ag ⟨.feature 156, rfl⟩⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); rw [sspec.physical]; rfl⟩ ⟨field_SCTLR_EL2_EE _ _ _ (control_before_SCTLR_EL2 cfg e ag)⟩ ⟨attribute_mair cfg e ag⟩ ⟨attribute_xs cfg e ag⟩
      ⟨attribute_mte2 cfg e ag⟩ ⟨Or.inl (pstate_EL cfg e ag)⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsHa d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsHd d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsPie d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsWxn d⟩
      ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.paramsMtx d⟩ ⟨rfl⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.normalizedTxsz d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardTbi d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardTbid d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardNfd d⟩
      ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.guardE0pd d⟩ ⟨by have hr := regs_eq_source cfg e.regs ag; generalize dataOf e.regs = d at hr; (try rw [beforeFetch_regs]); (first | rw [hr] | simp only [hr]); exact sspec.rawFault d⟩ ⟨translation_enabled cfg e ag⟩ ⟨quiet_tlb cfg e ag⟩ ⟨by show e.regs.FeatureImpl[4]! = true; exact feature_at cfg e ag 4 (by decide) true _ rfl⟩ ⟨pstate_EL cfg e ag⟩
      ⟨pstate_nRW cfg e ag⟩ ⟨field_SCR_EL3_RW _ _ _ (control_entry cfg e ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_RW _ _ _ (control_entry cfg e ag .HCR_EL2 (by decide))⟩ ⟨quiet_spe cfg e ag⟩ ⟨pmintenclr_zero cfg e ag⟩ ⟨field_BRBFCR_EL1_PAUSED _ _ _ (control_entry cfg e ag .BRBFCR_EL1 (by decide))⟩
      ⟨pmu_lower cfg e ag⟩ ⟨pmu_upper cfg e ag⟩ ⟨field32_CNTCR_SCEN _ _ _ (control32_entry cfg e ag .CNTCR)⟩ ⟨timers.cntp⟩ ⟨timers.cnthp⟩ ⟨timers.cnthps⟩
      ⟨timers.cntps⟩ ⟨timers.cntv⟩ ⟨timers.cnthv⟩ ⟨timers.cnthvs⟩ ⟨quiet_gic cfg e ag⟩ a121
      a122 a123 ⟨feature_at cfg e ag 0 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 1 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 2 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 3 (by decide) false _ rfl⟩
      ⟨feature_at cfg e ag 4 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 5 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 6 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 7 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 12 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 153 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 13 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 143 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 230 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 123 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 45 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 144 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 103 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 60 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 126 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 185 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 105 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 145 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 89 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 107 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 27 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 65 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 130 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 108 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 131 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 67 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 92 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 93 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 110 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 50 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 111 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 171 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 133 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 95 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 200 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 36 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 53 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 232 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 138 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 40 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 41 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 76 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 77 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 78 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 79 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 233 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 234 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 235 (by decide) false _ rfl⟩
      ⟨feature_at cfg e ag 236 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 81 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 221 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 222 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 223 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 224 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 225 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 226 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 227 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 165 (by decide) true _ rfl⟩ ⟨num_breakpoints cfg e ag⟩ ⟨num_watchpoints cfg e ag⟩
      ⟨num_ctx_breakpoints cfg e ag⟩ ⟨quiet_edscr_status cfg e ag⟩ ⟨quiet_spe cfg e ag⟩ ⟨pstate_EL cfg e ag⟩ ⟨pstate_nRW cfg e ag⟩ ⟨pstate_IL cfg e ag⟩
      ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg e ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg e ag .HCR_EL2 (by decide))⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg e ag .SCR_EL3 (by decide))⟩ ⟨field_SCR_EL3_NSE _ _ _ (control_entry cfg e ag .SCR_EL3 (by decide))⟩ ⟨field_MDSCR_EL1_SS _ _ _ (control_entry cfg e ag .MDSCR_EL1 (by decide))⟩ ⟨pstate_SS cfg e ag⟩
      ⟨quiet_osuc cfg e ag⟩ ⟨field_PMBLIMITR_EL1_E _ _ _ (control_entry cfg e ag .PMBLIMITR_EL1 (by decide))⟩ ⟨field_SCR_EL3_RW _ _ _ (control_entry cfg e ag .SCR_EL3 (by decide))⟩ ⟨field_SCR_EL3_EEL2 _ _ _ (control_entry cfg e ag .SCR_EL3 (by decide))⟩ ⟨field_TCR_EL2_TBI0 _ _ _ (control_entry cfg e ag .TCR_EL2 (by decide))⟩ ⟨field_TCR_EL2_TBID0 _ _ _ (control_entry cfg e ag .TCR_EL2 (by decide))⟩
      ⟨field_MDCR_EL3_NSPB _ _ _ (control_entry cfg e ag .MDCR_EL3 (by decide))⟩ ⟨field_MDCR_EL3_NSPBE _ _ _ (control_entry cfg e ag .MDCR_EL3 (by decide))⟩ ⟨feature_at cfg e ag 54 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 245 (by decide) false _ rfl⟩ a210 a211
      ⟨quiet_spe cfg e ag⟩ ⟨pstate_EL cfg e ag⟩ ⟨pstate_nRW cfg e ag⟩ ⟨feature_at cfg e ag 232 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 54 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 4 (by decide) true _ rfl⟩
      ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg e ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg e ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg e ag .HCR_EL2 (by decide))⟩ ⟨field_SCTLR_EL2_E0E _ _ _ (control_entry cfg e ag .SCTLR_EL2 (by decide))⟩ ⟨feature_at cfg e ag 2 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 6 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 54 (by decide) true _ rfl⟩ ⟨pstate_EL cfg e ag⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg e ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg e ag .HCR_EL2 (by decide))⟩ ⟨field_MDSCR_EL1_MDE _ _ _ (control_entry cfg e ag .MDSCR_EL1 (by decide))⟩ ⟨field32_EDSCR_HDE _ _ _ (control32_entry cfg e ag ._EDSCR)⟩
      ⟨⟨feature_at cfg e ag 7 (by decide) true _ rfl, feature_at cfg e ag 3 (by decide) false _ rfl, feature_at cfg e ag 227 (by decide) false _ rfl, feature_at cfg e ag 111 (by decide) true _ rfl⟩⟩ ⟨dcache_entry cfg e ag⟩ ⟨pstate_EL cfg e ag⟩ ⟨pstate_nRW cfg e ag⟩ ⟨feature_at cfg e ag 4 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 232 (by decide) false _ rfl⟩
      ⟨feature_at cfg e ag 54 (by decide) true _ rfl⟩ ⟨field_SCR_EL3_NS _ _ _ (control_entry cfg e ag .SCR_EL3 (by decide))⟩ ⟨field_HCR_EL2_E2H _ _ _ (control_entry cfg e ag .HCR_EL2 (by decide))⟩ ⟨field_HCR_EL2_TGE _ _ _ (control_entry cfg e ag .HCR_EL2 (by decide))⟩ ⟨pstate_TCO cfg e ag⟩ ⟨field_SCTLR_EL2_TCF0 _ _ _ (control_entry cfg e ag .SCTLR_EL2 (by decide))⟩
      ⟨preparation cfg e ag⟩ a243 a244 a245 a246 ⟨feature_at cfg e ag 103 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 123 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 227 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 2 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 3 (by decide) false _ rfl⟩ ⟨feature_at cfg e ag 6 (by decide) true _ rfl⟩ ⟨feature_at cfg e ag 7 (by decide) true _ rfl⟩
      ⟨feature_at cfg e ag 230 (by decide) false _ rfl⟩ ⟨field_SCR_EL3_GCSEn _ _ _ (control_entry cfg e ag .SCR_EL3 (by decide))⟩ a256 a257 a258 a259
      tableRows ⟨a261.holds.toFull⟩ a262 a263 a264 a265
      a266 a267 a268 a269 a270 a271
      a272 a273 a274 a275 a276

#check "CURRENT_DECL GB10.Heap.Initial0Residual"
/-- The retained original Initial0 inputs, stated explicitly at the source data substitution. -/
structure Initial0Residual {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain) (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : ArmCert.Translate.Model.HeapV2E17.Pins) (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word) (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (tableRows : NativeSourceInit.Plan)
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (e : ArmBridge.Draft.NativeState) : Prop where
  /-- named premise GB10.TimersQuiet (entry environment state). -/
  timers : TimersQuiet e.regs budget
  a16 : CertiFFI.Claim.RunCheck "card:budget" (357 + 12 ≤ budget)
  a17 : CertiFFI.Claim.RunCheck "card:plan-offsets" (∀ (j : Nat), (offS j).toNat % 4 = 0)
  a18 : CertiFFI.Claim.RunCheck "card:plan-offsets" (∀ (j : Nat), j ≤ 6 → offS j = ArmBridge.CruxGenGuarded.Release.shimPC j)
  a19 : CertiFFI.Claim.RunCheck "card:plan-offsets" (∀ (j : Nat), 357 + 8 ≤ j → j ≤ 357 + 11 → offS j = ArmBridge.CruxGenGuarded.Release.shimPC (j - (357 + 1)))
  a20 : CertiFFI.Claim.DeploymentObligation "comp:caller:image-table-separated" (ArmCert.Translate.Model.ImageTableSeparated scope loadBase mapping (RtShim2.ShimMem.slotBytes pins mapping))
  a55 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/covered" (∀ (row : ArmCert.Translate.Model.PermissionRow), row ∈ rows → row.slot ∈ (ArmCert.Translate.Model.rowsFootprint spec.imageRows).slots)
  a56 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/topology" (ArmCert.Translate.Model.TopologyImageAt spec (ArmBridge.CruxGenGuarded.beforeFetchState e))
  a57 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/attributes" (ArmCert.Translate.Model.AttributeImage (ArmCert.Translate.Model.rowsObserve spec.imageRows) (sourceAttributes rho caller) (ArmBridge.CruxGenGuarded.beforeFetchState e).mem)
  a58 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/writeback" (ArmCert.Translate.Model.WriteBackAttributeImage (ArmCert.Translate.Model.rowsObserve spec.imageRows) (sourceAttributes rho caller) (ArmBridge.CruxGenGuarded.beforeFetchState e).mem)
  a59 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/current/images/permissions" (ArmCert.Translate.Model.PermissionImage rows spec.params (ArmBridge.CruxGenGuarded.beforeFetchState e).regs spec.controls (ArmBridge.CruxGenGuarded.beforeFetchState e).mem)
  a121 : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pc" (e.regs._PC = base + offS 0)
  a122 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/closed" (ArmCert.Translate.Model.ClosedMembershipAt spec (sourceAttributes rho caller) rows mapping (ArmBridge.CruxGenGuarded.Release.shimMap spec mapping base pins) (ArmBridge.CruxGenGuarded.beforeFetchState e))
  a123 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/placed" (MemReloc.ImageOn scope image e loadBase mapping)
  a210 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/raw" (ArmCertWalk.RawImageAt spec.imageRows e.mem)
  a211 : CertiFFI.Claim.DeploymentObligation "card:default-shim-entry/noUpd" (∀ (wr : Bool) (acc : ArmFull.AccessDescriptor), ArmCert.Translate.Model.DataShape wr acc → ArmCertWalk.NoUpdateRows (have __src := spec.params; { ha := __src.ha, hd := __src.hd, tbi := __src.tbi, tbid := __src.tbid, nfd := __src.nfd, e0pd := __src.e0pd, d128 := __src.d128, aie := __src.aie, mair2 := __src.mair2, ds := __src.ds, ps := __src.ps, txsz := __src.txsz, epan := __src.epan, dct := __src.dct, nv1 := __src.nv1, cmow := __src.cmow, pnch := __src.pnch, disch := __src.disch, haft := ArmCert.Translate.Model.hostHAFT e.regs, mtx := __src.mtx, skl := __src.skl, pie := __src.pie, pir := __src.pir, pire0 := __src.pire0, emec := __src.emec, amec := __src.amec, t0sz := __src.t0sz, t1sz := __src.t1sz, uwxn := __src.uwxn, tgx := __src.tgx, irgn := __src.irgn, orgn := __src.orgn, sh := __src.sh, hpd := __src.hpd, ee := __src.ee, wxn := __src.wxn, ntlsmd := __src.ntlsmd, dc := __src.dc, sif := __src.sif, mair := __src.mair }) acc spec.imageRows = true)
  a243 : CertiFFI.Claim.DeploymentObligation "card:default-trap-initial-tag-status-row" (NativeMteTagCheck.TagStatusRows e (e.choiceOcc.getD 1354 0) 1)
  a244 : CertiFFI.Claim.DeploymentObligation "card:code-static" (RtDit.ShimFetch.ShimCodeStatic mapping base scope (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a245 : CertiFFI.Claim.RunCheck "card:default-image-binding" (image = ArmCert.Translate.Model.HeapV2.image base)
  a246 : CertiFFI.Claim.RunCheck "card:default-load-base-binding" (loadBase = base)
  a256 : CertiFFI.Claim.DeploymentObligation "card:slot-present" (RtShim.SlotPrem.ShimSlotPresent pins mapping e)
  a257 : CertiFFI.Claim.CallerContract "comp:caller:shim-caller-contract" (e.regs.SP_EL0 = BitVec.ofNat 64 pins.sp + BitVec.ofInt 64 16)
  a258 : CertiFFI.Claim.DeploymentObligation "card:code-static" (RtShim.SlotPrem.ShimSlotStatic pins mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows))
  a259 : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers" ((BitVec.ofNat 64 pins.sp).toNat % 16 = 0)
  a261 : CertiFFI.Claim.DeploymentObligation "card:body-entry/static" (ReleaseProfile.GB10.CodeStaticR mapping base (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte)
  a262 : CertiFFI.Claim.DeploymentObligation "card:body-entry/agrees" (ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (ArmCert.Translate.Model.HeapV2E17.consumerMapOn ArmCert.Translate.Model.HeapV2E17.noData pins base.toNat mapping (ArmCert.Translate.Model.rowsFootprint spec.imageRows).byte))
  a263 : CertiFFI.Claim.DeploymentObligation "card:body-entry/page" (base.toNat % 4096 = 0)
  a264 : CertiFFI.Claim.DeploymentObligation "card:body-entry/low" (base.toNat < 2 ^ 54)
  a265 : CertiFFI.Claim.RunCheck "card:plan-offsets" (offS 7 = ArmBridge.CruxGenGuarded.HeapV2Compose.offsetOf 0)
  a266 : CertiFFI.Claim.DeploymentObligation "card:body-entry/presentE" (HeapV2StepCerts.C3.DataPresent pins mapping e)
  a267 : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers" (HeapV2StepCerts.RegBind.regVal e (HeapV2StepCerts.RegBind.Reg.x 0) = BitVec.ofInt 64 ↑pins.x0)
  a268 : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers" (HeapV2StepCerts.RegBind.regVal e (HeapV2StepCerts.RegBind.Reg.x 1) = BitVec.ofInt 64 ↑pins.x1)
  a269 : CertiFFI.Claim.DeploymentObligation "card:body-entry/satE" (NativeSourceInit.Satisfies (ArmCert.Translate.Model.HeapV2.entryPlan base mapping HeapV2StepCerts.codeOffsets tableRows) e.mem)
  a270 : CertiFFI.Claim.DeploymentObligation "card:body-entry/planAvoidsSlot" (∀ (row : NativeSourceInit.PhysicalByte), row ∈ ArmCert.Translate.Model.HeapV2.entryPlan base mapping HeapV2StepCerts.codeOffsets tableRows → ¬RtShim2.ShimMem.slotBytes pins mapping row.fst)
  a271 : CertiFFI.Claim.DeploymentObligation "card:body-entry/codeMapped" (∀ (o : Nat), o ∈ HeapV2StepCerts.codeOffsets → ∃ pa, mapping (MemReloc.imageAddress base o) = some pa)
  a272 : CertiFFI.Claim.DeploymentObligation "card:body-entry/codePresent" (∀ (o : Nat), o ∈ HeapV2StepCerts.codeOffsets → ∃ byte, ArmCert.Translate.Model.HeapV2.image base o = some byte)
  a273 : CertiFFI.Claim.DeploymentObligation "card:body-entry/tables" (∀ (row : NativeSourceInit.PhysicalByte), row ∈ ArmCert.Translate.Model.imageRowsPlan spec.imageRows → row ∈ tableRows)
  a274 : CertiFFI.Claim.DeploymentObligation "card:body-entry/declared" (ArmCert.Translate.Model.PermissionRowsDeclared rows spec.imageRows)
  a275 : CertiFFI.Claim.DeploymentObligation "E34" ((List.map (fun x => x.logical) spec.logicalRows).Nodup)
  a276 : CertiFFI.Claim.CallerContract "card:path-selector" (HeapV2StepCerts.ValBind.TrapPath 1 pins (HeapV2StepCerts.E17General.qOf e))

#check "CURRENT_DECL GB10.Heap.initial0_c1_explicit"
/-- Initial0 C1 with the explicit residual (statement identity against the compiled card). -/
def initial0_c1_explicit (real : Type) [inst : Sail.SailReal real] {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain) (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (pins : ArmCert.Translate.Model.HeapV2E17.Pins) (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word) (base : BitVec 64) (offS : Nat → BitVec 64) (budget : Nat) (tableRows : NativeSourceInit.Plan)
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (cfg : Configuration rho caller) (e : ArmBridge.Draft.NativeState) (ag : AgreesAt cfg e.regs)
    (sspec : SourceSpec rho caller spec)
    (res : Initial0Residual spec rows mapping pins scope image loadBase base offS budget tableRows rho caller e) :=
  initial0FromSource real spec rows mapping pins scope image loadBase base offS budget tableRows rho caller cfg e ag sspec res.timers
    res.a16 res.a17 res.a18 res.a19 res.a20 res.a55 res.a56 res.a57 res.a58 res.a59 res.a121 res.a122 res.a123 res.a210 res.a211 res.a243 res.a244 res.a245 res.a246 res.a256 res.a257 res.a258 res.a259 res.a261 res.a262 res.a263 res.a264 res.a265 res.a266 res.a267 res.a268 res.a269 res.a270 res.a271 res.a272 res.a273 res.a274 res.a275 res.a276

end ReleaseProfile.GB10.Heap

#print axioms ReleaseProfile.GB10.Heap.initial0FromSource
#print axioms ReleaseProfile.GB10.Heap.initial0_c1_explicit
