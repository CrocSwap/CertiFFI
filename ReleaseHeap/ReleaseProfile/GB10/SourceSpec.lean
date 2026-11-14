import ReleaseProfile.GB10.ModelRegs
import BridgeDraft.StateProjection
import Bridge.CruxGenGuarded.Prefetch
import NativeMteTagCheck.Primitive
import ArmCertWalk.AttributeInputs
import ArmCertWalk.Profile
import ArmCertWalk.TranslateTxsz
import ArmCertWalk.TranslateEntryGuards
import ArmCertWalk.TranslateCacheData
import ArmCertWalk.OverlayEnable
import ArmCertWalk.NoUpdatePath
import ArmCertTranslateModel.TopologyImage
import ArmCertTranslateModel.HostFlags
import ArmCertTranslateModel.HostTranslateGuards
import ArmCertTranslateModel.HostAdmission
import ArmCertTranslateModel.PermissionImage
import ArmCertTranslateModel.Realization
import Walk.S1LogicalDescriptor
import ArmCert.HookQuiet.V0.Predicate

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-!
# Source-owned translation-spec configuration (dfc1 F2), shared by all worked boundaries

In C1 the spec's tables, layout and proof fields describe the OS's actual page tables at entry
(bound by the original TopologyImageAt atom), so they remain program/entry data. Every
configuration-bearing field the worked cards constrain is source-owned here: `SourceSpec`
equates it with a projection of the canonical source register file, for EVERY nonconfiguration
data part (no baseline data is chosen). The original atoms comparing the spec with the actual
entry are then produced from entry agreement. Raw T0SZ, normalizedTxsz and the raw-fault
proposition remain separate fields. Fields the cards never constrain stay universally quantified.
-/

namespace ReleaseProfile.GB10

open ReleaseProfile.MachineSource

/-- Source physical configuration: PA bits, TCR_EL2.IPS (D253), FEAT_LPA/FEAT_LPA2 values. -/
def sourcePhysical (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) :
    ArmCertWalk.PhysicalConfig :=
  ⟨interpret rho.val caller.caller ⟨.bank_Int .__supported_pa_size, rfl⟩,
   ArmFull.Functions._get_TCR_EL2_Type_IPS (controlWord rho.val caller.caller .TCR_EL2),
   FeatureSource.value rho.val.features 69, FeatureSource.value rho.val.features 156⟩

#check "CURRENT_DECL GB10.SourceSpec"
/-- The spec's configuration-bearing fields are source projections (card-constrained fields). -/
structure SourceSpec (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    {domain : ArmCert.Translate.Model.QueryDomain} (spec : ArmCert.Translate.Model.TopologyImageSpec domain) :
    Prop where
  physical : spec.physicalConfig = sourcePhysical rho caller
  regime : spec.controls.regime = S1LogicalReference.Regime.el20
  ha : ∀ d : DataPart, spec.controls.ha =
    (ArmCert.Translate.Model.hostHA (sourceRegs rho caller d) == 1#1)
  hd : ∀ d : DataPart, spec.controls.hd =
    (ArmCert.Translate.Model.hostHD (sourceRegs rho caller d) == 1#1)
  pie : ∀ d : DataPart, spec.controls.pie =
    (ArmCert.Translate.Model.hostPIE (sourceRegs rho caller d) == 1#1)
  hpd : ∀ d : DataPart, spec.controls.hpd =
    ((if (sourceRegs rho caller d).FeatureImpl[48]! = true then
        Sail.BitVec.extractLsb ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) 41 41
      else 0#1) == 1#1)
  pir : ∀ d : DataPart, spec.controls.pie = true → spec.controls.pir =
    ArmFull.Functions.Mk_S1PIRType ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.PIR_EL2)
  pire0 : ∀ d : DataPart, spec.controls.pie = true → spec.controls.pire0 =
    ArmFull.Functions.Mk_S1PIRType ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.PIRE0_EL2)
  overlay : ∀ d : DataPart, (spec.controls.poe || spec.controls.e0poe) =
    ArmCertWalk.outputOverlayEnabled (sourceRegs rho caller d)
  paramsHa : ∀ d : DataPart, spec.params.ha = ArmCert.Translate.Model.hostHA (sourceRegs rho caller d)
  paramsHd : ∀ d : DataPart, spec.params.hd = ArmCert.Translate.Model.hostHD (sourceRegs rho caller d)
  paramsPie : ∀ d : DataPart, spec.params.pie = ArmCert.Translate.Model.hostPIE (sourceRegs rho caller d)
  paramsWxn : ∀ d : DataPart, spec.params.wxn =
    ArmFull.Functions._get_SCTLR_EL2_Type_WXN ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.SCTLR_EL2)
  paramsMtx : ∀ d : DataPart, spec.params.mtx =
    (if (sourceRegs rho caller d).FeatureImpl[191]! = true then
      Sail.BitVec.extractLsb ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) 60 60
    else 0#1)
  /-- normalizedTxsz, distinct from raw T0SZ. -/
  normalizedTxsz : ∀ d : DataPart, spec.params.txsz =
    ArmCertWalk.normalizeTxsz (sourceRegs rho caller d)
      (ArmFull.Functions._get_TCR_EL2_Type_T0SZ ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2))
  guardTbi : ∀ d : DataPart, (ArmCertWalk.translateGuardView spec.params).tbi =
    (ArmCert.Translate.Model.currentHostGuardView (sourceRegs rho caller d)).tbi
  guardTbid : ∀ d : DataPart, (ArmCertWalk.translateGuardView spec.params).tbid =
    (ArmCert.Translate.Model.currentHostGuardView (sourceRegs rho caller d)).tbid
  guardNfd : ∀ d : DataPart, (ArmCertWalk.translateGuardView spec.params).nfd =
    (ArmCert.Translate.Model.currentHostGuardView (sourceRegs rho caller d)).nfd
  guardE0pd : ∀ d : DataPart, (ArmCertWalk.translateGuardView spec.params).e0pd =
    (ArmCert.Translate.Model.currentHostGuardView (sourceRegs rho caller d)).e0pd
  /-- Sail AArch64_S1TTWParamsEL20 (Fn/M0188) sets haft := 0#1 unless FEAT_HAFT is implemented;
  the source declares FEAT_HAFT (feature 189) false at TRM grade (HAFDBS = 0b0010 on both cores). -/
  paramsHaft : spec.params.haft = 0#1
  /-- All 34 configuration-determined params fields equal Sail's EL2&0 params (provider
  `hostNative` = Sail `AArch64_S1TTWParamsEL20` under HostRegimeAt, normalized txsz). The six fields
  Sail leaves `undefined` for EL2&0 (dc dct nv1 t0sz t1sz uwxn, oracle-chosen), and mair2/pir/pire0,
  which Sail also draws from the oracle when FEAT_AIE / FEAT_S1PIE are absent (D258), are semantics,
  not configuration, and stay universally quantified. Pinning them would make this predicate
  unsatisfiable (different oracles give different values). -/
  paramsSail : ∀ (d : DataPart) (state : ArmCert.Translate.Model.State) (sail : ArmFull.S1TTWParams) next,
    state.regs = sourceRegs rho caller d →
    ArmCert.Translate.Model.hostNative state = .ok sail next →
    spec.params = ArmCertWalk.normalizeWalkParams state.regs
      { sail with dc := spec.params.dc, dct := spec.params.dct, nv1 := spec.params.nv1,
                  t0sz := spec.params.t0sz, t1sz := spec.params.t1sz, uwxn := spec.params.uwxn,
                  mair2 := spec.params.mair2, pir := spec.params.pir, pire0 := spec.params.pire0 }
  /-- Reference-control fields mirroring Sail params / source registers (uwxn: Sail-undefined in
  EL2&0, free; nv1/el2Enabled: kernel-irrelevant in EL2&0, also projected). -/
  controlsSail : ∀ (d : DataPart) (state : ArmCert.Translate.Model.State) (sail : ArmFull.S1TTWParams) next,
    state.regs = sourceRegs rho caller d →
    ArmCert.Translate.Model.hostNative state = .ok sail next →
    spec.controls.haft = (sail.haft == 1#1) ∧ spec.controls.pnch = (sail.pnch == 1#1) ∧
    spec.controls.aie = (sail.aie == 1#1) ∧ spec.controls.mtx = (sail.mtx == 1#1) ∧
    spec.controls.cmow = (sail.cmow == 1#1) ∧ spec.controls.wxn = (sail.wxn == 1#1) ∧
    spec.controls.epan = (sail.epan == 1#1) ∧ spec.controls.mair = sail.mair
  featXS : spec.controls.featXS = FeatureSource.value rho.val.features 166
  mte2 : spec.controls.mte2 = FeatureSource.value rho.val.features 134
  paBits : spec.controls.paBits = 40
  el2Enabled : spec.controls.el2Enabled = true
  por : ∀ d : DataPart, spec.controls.por =
    (sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.POR_EL2
  porE0 : ∀ d : DataPart, spec.controls.porE0 =
    (sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.POR_EL0
  pan : spec.controls.pan = (caller.caller.pstate.PAN == 1#1)
  nv1 : ∀ d : DataPart, spec.controls.nv1 =
    ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2).getLsbD 43
  /-- The separate raw-fault proposition at the RAW T0SZ (structure update keeps it distinct). -/
  rawFault : ∀ d : DataPart, ArmCertWalk.sourceTxszFault (sourceRegs rho caller d)
    { spec.params with
        txsz := (ArmFull.Functions._get_TCR_EL2_Type_T0SZ
          ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2)) } = false

/-- The guard of Sail's haft assignment is false in the canonical source. -/
theorem featHaft_source (rho : AdmissibleSourceCompletion) :
    FeatureSource.value rho.val.features 189 = false :=
  FeatureSource.value_declared _ 189 false _ rfl

/-! ## Checked irrelevance of controls.el2Enabled and controls.nv1 (dfc1 F2 disposition)

The spec consumers read these two fields only through `S1LogicalReference.nv1Mode`, which is
false in the EL2&0 regime fixed by `SourceSpec.regime`. -/

theorem nv1Mode_el20 (c : S1LogicalReference.Controls) (h : c.regime = S1LogicalReference.Regime.el20) :
    S1LogicalReference.nv1Mode c = false := by
  unfold S1LogicalReference.nv1Mode
  rw [h]
  rfl

/-- Leaf permissions depend on controls only through the source-projected fields in EL2&0. -/
theorem leafPermissions_congr (c1 c2 : S1LogicalReference.Controls)
    (r1 : c1.regime = S1LogicalReference.Regime.el20) (r2 : c2.regime = S1LogicalReference.Regime.el20)
    (ha : c1.ha = c2.ha) (hd : c1.hd = c2.hd) (pie : c1.pie = c2.pie) (pir : c1.pir = c2.pir)
    (pire0 : c1.pire0 = c2.pire0) (overlay : (c1.poe || c1.e0poe) = (c2.poe || c2.e0poe)) :
    S1LogicalReference.leafPermissions c1 = S1LogicalReference.leafPermissions c2 := by
  funext table d
  have n1 := nv1Mode_el20 c1 r1
  have n2 := nv1Mode_el20 c2 r2
  simp only [S1LogicalReference.leafPermissions, S1LogicalReference.classicPermissions,
    S1LogicalReference.indirectPermissions, n1, n2, ha, hd, pie, pir, pire0, overlay]

/-- PermissionImage is invariant under any controls change outside the projected fields. -/
theorem permissionImage_congr (rows : List ArmCert.Translate.Model.PermissionRow) (params : ArmFull.S1TTWParams)
    (regs : ArmFull.Regs) (mem : ArmCert.Translate.Model.Mem) (c1 c2 : S1LogicalReference.Controls)
    (same : S1LogicalReference.leafPermissions c1 = S1LogicalReference.leafPermissions c2) :
    ArmCert.Translate.Model.PermissionImage rows params regs c1 mem ↔
      ArmCert.Translate.Model.PermissionImage rows params regs c2 mem := by
  unfold ArmCert.Translate.Model.PermissionImage ArmCertWalk.descriptorPermissionView
  rw [same]

/-! ## Kernel-checked params irrelevance (fail closed)

`mixParams p q` takes every field from an ARBITRARY `q` except the fields the consumers read.
Each consumer is definitionally equal at `p` and `mixParams p q`; if a consumer read any other
params field this `rfl` would not typecheck. -/

def mixParams (p q : ArmFull.S1TTWParams) : ArmFull.S1TTWParams :=
  { q with ha := p.ha, hd := p.hd, pie := p.pie, wxn := p.wxn, haft := p.haft }

theorem noUpdateRows_params (p q : ArmFull.S1TTWParams) (acc : ArmFull.AccessDescriptor)
    (rows : List ArmCert.Translate.Model.ImageRow) :
    ArmCertWalk.NoUpdateRows p acc rows = ArmCertWalk.NoUpdateRows (mixParams p q) acc rows := rfl

theorem permissionImage_params (rows : List ArmCert.Translate.Model.PermissionRow) (p q : ArmFull.S1TTWParams)
    (regs : ArmFull.Regs) (c : S1LogicalReference.Controls) (mem : ArmCert.Translate.Model.Mem) :
    ArmCert.Translate.Model.PermissionImage rows p regs c mem ↔
      ArmCert.Translate.Model.PermissionImage rows (mixParams p q) regs c mem := Iff.rfl

theorem topologyImageAt_params {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain) (q : ArmFull.S1TTWParams)
    (state : ArmCert.Translate.Model.State) :
    ArmCert.Translate.Model.TopologyImageAt spec state ↔
      ArmCert.Translate.Model.TopologyImageAt { spec with params := mixParams spec.params q } state := Iff.rfl

theorem legalPAMax_source (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) :
    ArmCertWalk.LegalPAMax (sourcePhysical rho caller).paMax := by
  change ArmCertWalk.LegalPAMax 40
  unfold ArmCertWalk.LegalPAMax
  decide

/-- The Sail pre-fetch register update (exactly five writes): canonical-module constructor. -/
def beforeFetchRegs (r : ArmFull.Regs) : ArmFull.Regs :=
  { r with
        ShouldAdvanceSS := true, ShouldAdvanceIT := false,
        bank_BitVec_32 := r.bank_BitVec_32.set ArmFull.Bank_BitVec_32._EDSCR
          (ArmFull.Functions._update_EDSCR_Type_PipeAdv
            (Sail.BitVec.updateSubrange (r.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) 30 29
              (Sail.BitVec.slice (r.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDCCSR_EL0) 29 2)) 1#1),
        bank_BitVec_64 := r.bank_BitVec_64.set ArmFull.Bank_BitVec_64.MDCCSR_EL0
          (Sail.BitVec.updateSubrange (r.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDCCSR_EL0) 30 29
            (Sail.BitVec.slice
              (ArmFull.Functions._update_EDSCR_Type_PipeAdv
                (Sail.BitVec.updateSubrange (r.bank_BitVec_32 ArmFull.Bank_BitVec_32._EDSCR) 30 29
                  (Sail.BitVec.slice (r.bank_BitVec_64 ArmFull.Bank_BitVec_64.MDCCSR_EL0) 29 2)) 1#1) 29 2)),
        bank_Int := r.bank_Int.set ArmFull.Bank_Int.SEE (-1) }

/-- The register file after beforeFetchState is the pre-fetch update of the entry registers. -/
theorem beforeFetch_regs (e : ArmBridge.Draft.NativeState) :
    (ArmBridge.CruxGenGuarded.beforeFetchState e).regs = beforeFetchRegs e.regs := rfl

#check "CURRENT_DECL GB10.beforeFetch_profile_frame"
/-- NONCONFIG_UPDATE frame: beforeFetchState leaves every profile coordinate unchanged except the five it writes
(debug/pipeline model state: EDSCR, MDCCSR_EL0, SEE, ShouldAdvanceSS/IT). -/
theorem beforeFetch_profile_frame (e : ArmBridge.Draft.NativeState) (c : ProfileCoordinate)
    (h32 : c.val ≠ .bank_BitVec_32 ._EDSCR) (h64 : c.val ≠ .bank_BitVec_64 .MDCCSR_EL0)
    (hint : c.val ≠ .bank_Int .SEE) (hss : c.val ≠ .ShouldAdvanceSS) (hit : c.val ≠ .ShouldAdvanceIT) :
    RawCoordinate.read (ArmBridge.CruxGenGuarded.beforeFetchState e).regs c.val = RawCoordinate.read e.regs c.val := by
  rw [beforeFetch_regs]
  unfold beforeFetchRegs
  rcases c with ⟨c, notData⟩
  cases c
  all_goals first
    | rfl
    | (exact absurd rfl hss)
    | (exact absurd rfl hit)
    | (rename_i key
       show Sail.ConcurrencyInterfaceV1.RegMap.set _ _ _ key = _
       exact Sail.ConcurrencyInterfaceV1.RegMap.set_ne _ _ (fun same => by subst same; exact h32 rfl))
    | (rename_i key
       show Sail.ConcurrencyInterfaceV1.RegMap.set _ _ _ key = _
       exact Sail.ConcurrencyInterfaceV1.RegMap.set_ne _ _ (fun same => by subst same; exact h64 rfl))
    | (rename_i key
       show Sail.ConcurrencyInterfaceV1.RegMap.set _ _ _ key = _
       exact Sail.ConcurrencyInterfaceV1.RegMap.set_ne _ _ (fun same => by subst same; exact hint rfl))

end ReleaseProfile.GB10

#print axioms ReleaseProfile.GB10.legalPAMax_source
#print axioms ReleaseProfile.GB10.featHaft_source
#print axioms ReleaseProfile.GB10.nv1Mode_el20
#print axioms ReleaseProfile.GB10.leafPermissions_congr
#print axioms ReleaseProfile.GB10.permissionImage_congr
#print axioms ReleaseProfile.GB10.noUpdateRows_params
#print axioms ReleaseProfile.GB10.permissionImage_params
#print axioms ReleaseProfile.GB10.topologyImageAt_params
#print axioms ReleaseProfile.GB10.beforeFetch_regs
#print axioms ReleaseProfile.GB10.beforeFetch_profile_frame
