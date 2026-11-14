import ReleaseProfile.GB10.SourceSpec

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-!
# Positive-C2 building block: a spec whose configuration is the source's

`sourcePhysical` reduces to the concrete GB10 physical configuration (PA 40, IPS 0b010 from the
D253 literals, FEAT_LPA/FEAT_LPA2 false). A base topology spec with that physical configuration
keeps its tables/layout/proof fields while every configuration field is replaced by the source
projection; see `sourceSpecOf` (later steps).
-/

namespace ReleaseProfile.GB10

open ReleaseProfile.MachineSource

theorem sourceIPS (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) :
    ArmFull.Functions._get_TCR_EL2_Type_IPS (controlWord rho.val caller.caller .TCR_EL2) = 2#3 := by
  have b0 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨32, by decide⟩ false _ rfl rfl
  have b1 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨33, by decide⟩ true _ rfl rfl
  have b2 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨34, by decide⟩ false _ rfl rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_TCR_EL2_Type_IPS, Sail.BitVec.extractLsb] at hj ⊢
  have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases this with rfl | rfl | rfl
  · simpa [BitVec.getLsbD_eq_getElem] using b0
  · simpa [BitVec.getLsbD_eq_getElem] using b1
  · simpa [BitVec.getLsbD_eq_getElem] using b2

#check "CURRENT_DECL GB10.sourcePhysical_eq"
theorem sourcePhysical_eq (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) :
    sourcePhysical rho caller = ⟨40, 2#3, false, false⟩ := by
  unfold sourcePhysical
  rw [sourceIPS rho caller]
  congr 1 <;> exact FeatureSource.value_declared _ _ false _ rfl

theorem sourceT0SZ (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) :
    ArmFull.Functions._get_TCR_EL2_Type_T0SZ (controlWord rho.val caller.caller .TCR_EL2) = 16#6 := by
  have b0 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨0, by decide⟩ false _ rfl rfl
  have b1 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨1, by decide⟩ false _ rfl rfl
  have b2 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨2, by decide⟩ false _ rfl rfl
  have b3 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨3, by decide⟩ false _ rfl rfl
  have b4 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨4, by decide⟩ true _ rfl rfl
  have b5 := rho.property.construction.control64 caller.caller .TCR_EL2 ⟨5, by decide⟩ false _ rfl rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ArmFull.Functions._get_TCR_EL2_Type_T0SZ, Sail.BitVec.extractLsb] at hj ⊢
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [BitVec.getLsbD_eq_getElem] using b0
  · simpa [BitVec.getLsbD_eq_getElem] using b1
  · simpa [BitVec.getLsbD_eq_getElem] using b2
  · simpa [BitVec.getLsbD_eq_getElem] using b3
  · simpa [BitVec.getLsbD_eq_getElem] using b4
  · simpa [BitVec.getLsbD_eq_getElem] using b5

/-- With txsz = 16 (D253 raw T0SZ), normalization is the identity. -/
theorem normalizeWalkParams_16 (regs : ArmFull.Regs) (p : ArmFull.S1TTWParams) (h : p.txsz = 16#6) :
    ArmCertWalk.normalizeWalkParams regs p = p := by
  unfold ArmCertWalk.normalizeWalkParams
  rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; unfold ArmCertWalk.currentMaxTxsz; split <;> decide)]

theorem normalizeTxsz_16 (regs : ArmFull.Regs) : ArmCertWalk.normalizeTxsz regs 16#6 = 16#6 := by
  have h1 : ¬ (((16#6 : BitVec 6).toNat : Int) < 16) := by decide
  have h2 : ¬ (((16#6 : BitVec 6).toNat : Int) > ArmCertWalk.currentMaxTxsz regs) := by
    unfold ArmCertWalk.currentMaxTxsz; split <;> decide
  unfold ArmCertWalk.normalizeTxsz
  simp only [h1, h2]
  rfl

theorem sourceRegs_feature (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (d : DataPart)
    (i : Nat) (h : i < 259) (v : Bool) (a : AuthorityRef) (rec : FeatureSource.declared ⟨i, h⟩ = some (v, a)) :
    (sourceRegs rho caller d).FeatureImpl[i] = v := by
  show (Vector.ofFn (sourceFeature rho caller))[i] = v
  rw [Vector.getElem_ofFn]
  exact FeatureSource.value_declared _ _ v a rec

/-- With FEAT_S1POE absent (D258), no stage-1 permission overlay is enabled. -/
theorem overlay_source (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (d : DataPart) :
    ArmCertWalk.outputOverlayEnabled (sourceRegs rho caller d) = false := by
  have h210 := sourceRegs_feature rho caller d 210 (by decide) false _ rfl
  unfold ArmCertWalk.outputOverlayEnabled ArmCertWalk.privilegedOverlayEnabled
    ArmCertWalk.e0OverlayEnabled
  simp only [h210, ite_true, Bool.or_self]

/-! ## Field lemmas for the provider's Sail EL2&0 params (`hostNative` = Sail AArch64_S1TTWParamsEL20)
Stated over an abstract state so the 2262-line native record stays small. -/

theorem nativeParams_ha (st : ArmCert.Translate.Model.State) (p : ArmFull.S1TTWParams) (s' : ArmCert.Translate.Model.State)
    (hn : ArmCert.Translate.Model.hostNative st = .ok p s') :
    p.ha = ArmCert.Translate.Model.hostHA st.regs := by
  simp only [ArmCert.Translate.Model.hostNative, ArmCertWalk.HostLowerSource.native, EStateM.Result.ok.injEq] at hn
  obtain ⟨rfl, -⟩ := hn
  simp only [ArmCert.Translate.Model.hostHA, dite_eq_ite]

theorem nativeParams_hd (st : ArmCert.Translate.Model.State) (p : ArmFull.S1TTWParams) (s' : ArmCert.Translate.Model.State)
    (hn : ArmCert.Translate.Model.hostNative st = .ok p s') :
    p.hd = ArmCert.Translate.Model.hostHD st.regs := by
  simp only [ArmCert.Translate.Model.hostNative, ArmCertWalk.HostLowerSource.native, EStateM.Result.ok.injEq] at hn
  obtain ⟨rfl, -⟩ := hn
  simp only [ArmCert.Translate.Model.hostHD, dite_eq_ite]

theorem nativeParams_pie (st : ArmCert.Translate.Model.State) (p : ArmFull.S1TTWParams) (s' : ArmCert.Translate.Model.State)
    (hn : ArmCert.Translate.Model.hostNative st = .ok p s')
    (h209 : st.regs.FeatureImpl[209] = false) (h242 : st.regs.FeatureImpl[242] = false) :
    p.pie = 0#1 := by
  simp only [ArmCert.Translate.Model.hostNative, ArmCertWalk.HostLowerSource.native, EStateM.Result.ok.injEq] at hn
  obtain ⟨rfl, -⟩ := hn
  simp only [h209, h242, Bool.false_eq_true, false_and, and_false,
    ite_false, dite_false, ↓reduceIte, ↓reduceDIte]
  decide

theorem nativeParams_txsz (st : ArmCert.Translate.Model.State) (p : ArmFull.S1TTWParams) (s' : ArmCert.Translate.Model.State)
    (hn : ArmCert.Translate.Model.hostNative st = .ok p s') :
    p.txsz = ArmFull.Functions._get_TCR_EL2_Type_T0SZ (st.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) := by
  simp only [ArmCert.Translate.Model.hostNative, ArmCertWalk.HostLowerSource.native, EStateM.Result.ok.injEq] at hn
  obtain ⟨rfl, -⟩ := hn
  rfl

theorem nativeParams_wxn (st : ArmCert.Translate.Model.State) (p : ArmFull.S1TTWParams) (s' : ArmCert.Translate.Model.State)
    (hn : ArmCert.Translate.Model.hostNative st = .ok p s') :
    p.wxn = ArmFull.Functions._get_SCTLR_EL2_Type_WXN (st.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.SCTLR_EL2) := by
  simp only [ArmCert.Translate.Model.hostNative, ArmCertWalk.HostLowerSource.native, EStateM.Result.ok.injEq] at hn
  obtain ⟨rfl, -⟩ := hn
  rfl

theorem nativeParams_mtx (st : ArmCert.Translate.Model.State) (p : ArmFull.S1TTWParams) (s' : ArmCert.Translate.Model.State)
    (hn : ArmCert.Translate.Model.hostNative st = .ok p s') :
    p.mtx = (if st.regs.FeatureImpl[191] = true then
      Sail.BitVec.extractLsb (st.regs.bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) 60 60 else 0#1) := by
  simp only [ArmCert.Translate.Model.hostNative, ArmCertWalk.HostLowerSource.native, EStateM.Result.ok.injEq] at hn
  obtain ⟨rfl, -⟩ := hn
  simp only [dite_eq_ite]

theorem nativeParams_guards (st : ArmCert.Translate.Model.State) (p : ArmFull.S1TTWParams) (s' : ArmCert.Translate.Model.State)
    (hn : ArmCert.Translate.Model.hostNative st = .ok p s') :
    ArmCertWalk.translateGuardView p = ArmCert.Translate.Model.currentHostGuardView st.regs := by
  simp only [ArmCert.Translate.Model.hostNative, ArmCertWalk.HostLowerSource.native, EStateM.Result.ok.injEq] at hn
  obtain ⟨rfl, -⟩ := hn
  simp only [ArmCertWalk.translateGuardView, ArmCert.Translate.Model.currentHostGuardView, dite_eq_ite,
    ArmFull.Functions._get_TCR_EL2_Type_TBID0, ArmFull.Functions._get_TCR_EL2_Type_NFD0,
    ArmFull.Functions._get_TCR_EL2_Type_E0PD0]
  congr 1
  by_cases h81 : st.regs.FeatureImpl[81] = true <;> simp [h81]

theorem nativeParams_haft (st : ArmCert.Translate.Model.State) (p : ArmFull.S1TTWParams) (s' : ArmCert.Translate.Model.State)
    (hn : ArmCert.Translate.Model.hostNative st = .ok p s')
    (h189 : st.regs.FeatureImpl[189] = false) :
    p.haft = 0#1 := by
  simp only [ArmCert.Translate.Model.hostNative, ArmCertWalk.HostLowerSource.native, EStateM.Result.ok.injEq] at hn
  obtain ⟨rfl, -⟩ := hn
  simp only [h189, Bool.false_eq_true, false_and, and_false,
    ite_false, dite_false, ↓reduceIte, ↓reduceDIte]

/-- Sail's EL2&0 params, with the six oracle-chosen fields overwritten, depend only on the state's
configuration words and feature vector (not on data, memory or oracle). -/
theorem nativeParams_congr (st st' : ArmCert.Translate.Model.State) (p p' : ArmFull.S1TTWParams)
    (s1 s2 : ArmCert.Translate.Model.State)
    (hn : ArmCert.Translate.Model.hostNative st = .ok p s1) (hn' : ArmCert.Translate.Model.hostNative st' = .ok p' s2)
    (h64 : ∀ k, isEntryData64 k = false → st.regs.bank_BitVec_64 k = st'.regs.bank_BitVec_64 k)
    (hF : st.regs.FeatureImpl = st'.regs.FeatureImpl) (h242 : st'.regs.FeatureImpl[242] = false)
    (o : ArmFull.S1TTWParams) :
    ({ p with dc := o.dc, dct := o.dct, nv1 := o.nv1, t0sz := o.t0sz, t1sz := o.t1sz, uwxn := o.uwxn, mair2 := o.mair2, pir := o.pir, pire0 := o.pire0 } : ArmFull.S1TTWParams) =
      { p' with dc := o.dc, dct := o.dct, nv1 := o.nv1, t0sz := o.t0sz, t1sz := o.t1sz, uwxn := o.uwxn, mair2 := o.mair2, pir := o.pir, pire0 := o.pire0 } := by
  simp only [ArmCert.Translate.Model.hostNative, ArmCertWalk.HostLowerSource.native, EStateM.Result.ok.injEq] at hn hn'
  obtain ⟨rfl, -⟩ := hn
  obtain ⟨rfl, -⟩ := hn'
  have z : ((0#1 : BitVec 1) = 1#1) = False := by decide
  simp only [hF, h242, z, Bool.false_eq_true, false_and, ↓reduceIte, ↓reduceDIte]
  simp (disch := decide) only [h64]

#check "CURRENT_DECL GB10.sourceSpec_exists"
/-- SourceSpec is satisfiable (compiled guard against a vacuous hypothesis): a base spec with the
source physical configuration keeps its tables/layout/proof fields while params/controls become the
source projections. -/
theorem sourceSpec_exists (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    {domain : ArmCert.Translate.Model.QueryDomain} (base : ArmCert.Translate.Model.TopologyImageSpec domain)
    (hphys : base.physicalConfig = ⟨40, 2#3, false, false⟩) (d : DataPart)
    (st : ArmCert.Translate.Model.State) (hst : st.regs = sourceRegs rho caller d) :
    ∃ spec : ArmCert.Translate.Model.TopologyImageSpec domain, SourceSpec rho caller spec ∧
      spec.layout = base.layout ∧ spec.logicalRows = base.logicalRows ∧ spec.imageRows = base.imageRows := by
  obtain ⟨regs, cs, co, mem, tags, cc, so, ev⟩ := st
  simp only at hst
  subst hst
  obtain ⟨sail, s', h0⟩ : ∃ p s', ArmCert.Translate.Model.hostNative ⟨sourceRegs rho caller d, cs, co, mem, tags, cc, so, ev⟩ = .ok p s' :=
    ⟨_, _, rfl⟩
  have h209 := sourceRegs_feature rho caller d 209 (by decide) false _ rfl
  have h242 := sourceRegs_feature rho caller d 242 (by decide) false _ rfl
  have h189 := sourceRegs_feature rho caller d 189 (by decide) false _ rfl
  have sailT : sail.txsz = 16#6 := by rw [nativeParams_txsz _ _ _ h0]; exact sourceT0SZ rho caller
  have hp : ∀ x, ArmCert.Translate.Model.hostPIE (sourceRegs rho caller x) = 0#1 := by
    intro x
    unfold ArmCert.Translate.Model.hostPIE
    rw [sourceRegs_feature rho caller x 209 (by decide) false _ rfl]
    rfl
  let fixed : ArmFull.S1TTWParams :=
    { sail with dc := base.params.dc, dct := base.params.dct, nv1 := base.params.nv1,
                t0sz := base.params.t0sz, t1sz := base.params.t1sz, uwxn := base.params.uwxn,
                mair2 := base.params.mair2, pir := base.params.pir, pire0 := base.params.pire0 }
  have hnorm : ArmCertWalk.normalizeWalkParams (sourceRegs rho caller d) fixed = fixed :=
    normalizeWalkParams_16 _ fixed sailT
  let controls : S1LogicalReference.Controls :=
    { regime := .el20, paBits := 40,
      ha := (ArmCert.Translate.Model.hostHA (sourceRegs rho caller d) == 1#1),
      hd := (ArmCert.Translate.Model.hostHD (sourceRegs rho caller d) == 1#1),
      haft := (sail.haft == 1#1), pie := (ArmCert.Translate.Model.hostPIE (sourceRegs rho caller d) == 1#1),
      hpd := ((if (sourceRegs rho caller d).FeatureImpl[48]! = true then
                Sail.BitVec.extractLsb ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) 41 41
              else 0#1) == 1#1),
      nv1 := ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.HCR_EL2).getLsbD 43, el2Enabled := true,
      pnch := (sail.pnch == 1#1), aie := (sail.aie == 1#1), mtx := (sail.mtx == 1#1),
      featXS := FeatureSource.value rho.val.features 166, mte2 := FeatureSource.value rho.val.features 134,
      mair := sail.mair, mair2 := base.controls.mair2,
      pir := ArmFull.Functions.Mk_S1PIRType ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.PIR_EL2),
      pire0 := ArmFull.Functions.Mk_S1PIRType ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.PIRE0_EL2),
      poe := false, e0poe := false,
      por := (sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.POR_EL2,
      porE0 := (sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.POR_EL0,
      cmow := (sail.cmow == 1#1), wxn := (sail.wxn == 1#1), uwxn := base.controls.uwxn,
      pan := (caller.caller.pstate.PAN == 1#1), epan := (sail.epan == 1#1) }
  -- the Sail params of any other state carrying the source registers agree outside the oracle fields
  have other : ∀ (dd : DataPart) (state : ArmCert.Translate.Model.State) (sail' : ArmFull.S1TTWParams) next,
      state.regs = sourceRegs rho caller dd → ArmCert.Translate.Model.hostNative state = .ok sail' next →
      ({ sail' with dc := base.params.dc, dct := base.params.dct, nv1 := base.params.nv1, t0sz := base.params.t0sz, t1sz := base.params.t1sz, uwxn := base.params.uwxn, mair2 := base.params.mair2, pir := base.params.pir, pire0 := base.params.pire0 } : ArmFull.S1TTWParams) = fixed ∧
        sail'.txsz = 16#6 := by
    intro dd state sail' next hregs hns
    refine ⟨?_, ?_⟩
    · exact nativeParams_congr state (⟨sourceRegs rho caller d, cs, co, mem, tags, cc, so, ev⟩ : ArmCert.Translate.Model.State) sail' sail next s' hns h0
        (fun k hk => by rw [hregs]; exact (sourceBank64_ne rho caller dd k hk).trans (sourceBank64_ne rho caller d k hk).symm)
        (by rw [hregs]; rfl) h242 base.params
    · rw [nativeParams_txsz _ _ _ hns, hregs]
      exact sourceT0SZ rho caller
  refine ⟨{ base with params := fixed, controls := controls }, ?_, rfl, rfl, rfl⟩
  constructor
  case physical => exact hphys.trans (sourcePhysical_eq rho caller).symm
  case regime => rfl
  case ha => intro dd; rfl
  case hd => intro dd; rfl
  case pie => intro dd; rfl
  case hpd => intro dd; rfl
  case pir => intro dd _; rfl
  case pire0 => intro dd _; rfl
  case overlay => intro dd; exact (overlay_source rho caller dd).symm
  case paramsHa => intro dd; show sail.ha = _; rw [nativeParams_ha _ _ _ h0]; rfl
  case paramsHd => intro dd; show sail.hd = _; rw [nativeParams_hd _ _ _ h0]; rfl
  case paramsPie => intro dd; show sail.pie = _; rw [nativeParams_pie _ _ _ h0 h209 h242, hp]
  case paramsWxn => intro dd; show sail.wxn = _; rw [nativeParams_wxn _ _ _ h0]; rfl
  case paramsMtx => intro dd; show sail.mtx = _; rw [nativeParams_mtx _ _ _ h0]; rfl
  case normalizedTxsz =>
    intro dd
    show sail.txsz = _
    rw [sailT, show ArmFull.Functions._get_TCR_EL2_Type_T0SZ
        ((sourceRegs rho caller dd).bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) = 16#6 from sourceT0SZ rho caller,
      normalizeTxsz_16]
  case guardTbi => intro dd; show (ArmCertWalk.translateGuardView sail).tbi = _; rw [nativeParams_guards _ _ _ h0]; rfl
  case guardTbid => intro dd; show (ArmCertWalk.translateGuardView sail).tbid = _; rw [nativeParams_guards _ _ _ h0]; rfl
  case guardNfd => intro dd; show (ArmCertWalk.translateGuardView sail).nfd = _; rw [nativeParams_guards _ _ _ h0]; rfl
  case guardE0pd => intro dd; show (ArmCertWalk.translateGuardView sail).e0pd = _; rw [nativeParams_guards _ _ _ h0]; rfl
  case paramsHaft => show sail.haft = 0#1; rw [nativeParams_haft _ _ _ h0 h189]
  case paramsSail =>
    intro dd state sail' next hregs hns
    obtain ⟨heq, ht⟩ := other dd state sail' next hregs hns
    exact heq.symm.trans (normalizeWalkParams_16 _ _ (by exact ht)).symm
  case controlsSail =>
    intro dd state sail' next hregs hns
    obtain ⟨heq, -⟩ := other dd state sail' next hregs hns
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (sail.haft == 1#1) = _; rw [show sail.haft = sail'.haft from (congrArg (·.haft) heq).symm]
    · show (sail.pnch == 1#1) = _; rw [show sail.pnch = sail'.pnch from (congrArg (·.pnch) heq).symm]
    · show (sail.aie == 1#1) = _; rw [show sail.aie = sail'.aie from (congrArg (·.aie) heq).symm]
    · show (sail.mtx == 1#1) = _; rw [show sail.mtx = sail'.mtx from (congrArg (·.mtx) heq).symm]
    · show (sail.cmow == 1#1) = _; rw [show sail.cmow = sail'.cmow from (congrArg (·.cmow) heq).symm]
    · show (sail.wxn == 1#1) = _; rw [show sail.wxn = sail'.wxn from (congrArg (·.wxn) heq).symm]
    · show (sail.epan == 1#1) = _; rw [show sail.epan = sail'.epan from (congrArg (·.epan) heq).symm]
    · show sail.mair = _; exact (congrArg (·.mair) heq).symm
  case featXS => rfl
  case mte2 => rfl
  case paBits => rfl
  case el2Enabled => rfl
  case por => intro dd; rfl
  case porE0 => intro dd; rfl
  case pan => rfl
  case nv1 => intro dd; rfl
  case rawFault =>
    intro dd
    show (if (((ArmFull.Functions._get_TCR_EL2_Type_T0SZ
        ((sourceRegs rho caller dd).bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2)).toNat : Int) < 16) then _ else false) = false
    rw [show ArmFull.Functions._get_TCR_EL2_Type_T0SZ
        ((sourceRegs rho caller dd).bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) = 16#6 from sourceT0SZ rho caller]
    rfl

#check "CURRENT_DECL GB10.gb10Physical"
/-- The GB10 physical configuration (equal to `sourcePhysical` at every completion, `sourcePhysical_eq`). -/
def gb10Physical : ArmCertWalk.PhysicalConfig := ⟨40, 2#3, false, false⟩

#check "CURRENT_DECL GB10.OracleChoice"
/-- Values Sail draws from the oracle in EL2&0 (dc dct nv1 t0sz t1sz uwxn, and mair2/pir/pire0 with
FEAT_AIE/FEAT_S1PIE absent) plus the two reference-control mirrors left free by SourceSpec.
Semantics choices, not configuration. -/
structure OracleChoice where
  dc : BitVec 1
  dct : BitVec 1
  nv1 : BitVec 1
  t0sz : BitVec 3
  t1sz : BitVec 3
  uwxn : BitVec 1
  mair2 : ArmFull.MAIRType
  pir : ArmFull.S1PIRType
  pire0 : ArmFull.S1PIRType
  controlsMair2 : BitVec 64
  controlsUwxn : Bool

#check "CURRENT_DECL GB10.TopologyTables"
/-- Tables-only topology data at the GB10 physical configuration: no params, controls or physical
binder. The only way to obtain a spec from it is `sourceSpec_of_tables` (source-pinned). -/
structure TopologyTables (domain : ArmCert.Translate.Model.QueryDomain) where
  layout : S1LogicalReference.Layout
  logicalRows : List ArmCert.Translate.Model.LogicalRow
  imageRows : List ArmCert.Translate.Model.ImageRow
  available : S1LogicalReference.Available (ArmCert.Translate.Model.logicalObserve logicalRows)
    (fun p => S2TableRAM.OrdinaryRAM p.address)
  identity : ∀ logical physical view, ArmCert.Translate.Model.logicalObserve logicalRows logical physical view →
    logical = physical.address.toNat ∧ physical.paspace = .PAS_NonSecure
  represented : ∀ logical physical view, ArmCert.Translate.Model.logicalObserve logicalRows logical physical view →
    ∃ leaf, ArmCert.Translate.Model.rowsObserve imageRows physical.address.toNat leaf view
  aligned : ArmCert.Translate.Model.ImageAligned (ArmCert.Translate.Model.rowsObserve imageRows)
  rootBound : ∀ q : ArmCert.Translate.Model.AccessQuery, domain q →
    S1LogicalReference.entryAddress layout.root q.va layout.start
      (S1LogicalReference.rootBits layout.start layout.inputBits) <
      2 ^ (ArmCertWalk.effectiveBits gb10Physical).toNat
  paths : ∀ q : ArmCert.Translate.Model.AccessQuery, domain q →
    ∃ level logical physical view,
      S1LogicalReference.Path (ArmCert.Translate.Model.logicalObserve logicalRows)
        (ArmCertWalk.effectiveBits gb10Physical).toNat q.va
        layout.start (S1LogicalReference.rootBits layout.start layout.inputBits) layout.root
        (.leaf level logical physical view) ∧
      ArmCert.Translate.Model.rowsObserve imageRows physical.address.toNat true view

/-- Internal base spec of tables + oracle choice; params/controls are overwritten by `sourceSpec_exists`. -/
private def TopologyTables.baseSpec {domain : ArmCert.Translate.Model.QueryDomain} (t : TopologyTables domain)
    (o : OracleChoice) : ArmCert.Translate.Model.TopologyImageSpec domain where
  params := { (default : ArmFull.S1TTWParams) with dc := o.dc, dct := o.dct, nv1 := o.nv1, t0sz := o.t0sz, t1sz := o.t1sz, uwxn := o.uwxn, mair2 := o.mair2, pir := o.pir, pire0 := o.pire0 }
  physicalConfig := gb10Physical
  controls := { (default : S1LogicalReference.Controls) with mair2 := o.controlsMair2, uwxn := o.controlsUwxn }
  layout := t.layout
  logicalRows := t.logicalRows
  imageRows := t.imageRows
  available := t.available
  identity := t.identity
  represented := t.represented
  aligned := t.aligned
  rootBound := t.rootBound
  paths := t.paths

#check "CURRENT_DECL GB10.sourceSpec_of_tables"
/-- A source-pinned spec with exactly the given tables (and the oracle choice in the Sail-undefined fields). -/
theorem sourceSpec_of_tables (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    {domain : ArmCert.Translate.Model.QueryDomain} (t : TopologyTables domain) (o : OracleChoice) (d : DataPart)
    (st : ArmCert.Translate.Model.State) (hst : st.regs = sourceRegs rho caller d) :
    ∃ spec : ArmCert.Translate.Model.TopologyImageSpec domain, SourceSpec rho caller spec ∧
      spec.layout = t.layout ∧ spec.logicalRows = t.logicalRows ∧ spec.imageRows = t.imageRows :=
  sourceSpec_exists rho caller (t.baseSpec o) rfl d st hst

/-- Every non-root 64-bit word of the source register file is the canonical control word. -/
theorem sourceRegs_bank64 (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (d : DataPart)
    (key : ArmFull.Bank_BitVec_64) (h : isEntryData64 key = false := by decide) :
    (sourceRegs rho caller d).bank_BitVec_64 key = controlWord rho.val caller.caller key :=
  (sourceBank64_ne rho caller d key h).trans (controlWord_eq rho.val caller.caller key h).symm

private theorem tcr_bit (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (d : DataPart)
    (i : Fin 64) (v : Bool) (a : AuthorityRef) (rec : controlDeclared .TCR_EL2 i.val = some (v, a)) :
    ((sourceRegs rho caller d).bank_BitVec_64 .TCR_EL2).getLsbD i.val = v := by
  rw [sourceRegs_bank64 rho caller d .TCR_EL2]
  exact rho.property.construction.control64 caller.caller .TCR_EL2 i v a rfl rec

#check "CURRENT_DECL GB10.sourceSpec_walkLiterals"
/-- Walk-relevant params/controls of any source-pinned spec, as literals from the declared bits
(D257 HA/HD/HPD0/NFD0/E0PD0/MTX0, ControlRows TBI0/TBID0, D253 T0SZ; FEAT_S1PIE absent). For spec transport. -/
theorem sourceSpec_walkLiterals (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    {domain : ArmCert.Translate.Model.QueryDomain} {spec : ArmCert.Translate.Model.TopologyImageSpec domain}
    (sspec : SourceSpec rho caller spec) (d : DataPart) :
    spec.params.ha = 1#1 ∧ spec.params.hd = 1#1 ∧ spec.params.pie = 0#1 ∧ spec.params.tbi = 1#1 ∧
      spec.params.tbid = 0#1 ∧ spec.params.nfd = 0#1 ∧ spec.params.e0pd = 0#1 ∧ spec.params.mtx = 0#1 ∧
      spec.params.txsz = 16#6 ∧ spec.controls.pie = false ∧ spec.controls.hpd = false := by
  have f47 := sourceRegs_feature rho caller d 47 (by decide) true _ rfl
  have f48 := sourceRegs_feature rho caller d 48 (by decide) true _ rfl
  have f81 := sourceRegs_feature rho caller d 81 (by decide) true _ rfl
  have f98 := sourceRegs_feature rho caller d 98 (by decide) true _ rfl
  have f127 := sourceRegs_feature rho caller d 127 (by decide) true _ rfl
  have f209 := sourceRegs_feature rho caller d 209 (by decide) false _ rfl
  have ha : spec.params.ha = 1#1 := by
    rw [sspec.paramsHa d]
    unfold ArmCert.Translate.Model.hostHA
    rw [f47]
    simp only [↓reduceIte]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [Sail.BitVec.slice, BitVec.getLsbD_extractLsb'] at hj ⊢
    have : j = 0 := by omega
    subst this
    simpa [BitVec.getLsbD_eq_getElem] using tcr_bit rho caller d ⟨39, by decide⟩ true _ rfl
  have hd : spec.params.hd = 1#1 := by
    rw [sspec.paramsHd d]
    unfold ArmCert.Translate.Model.hostHD
    rw [f47]
    simp only [↓reduceIte]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [Sail.BitVec.slice, BitVec.getLsbD_extractLsb'] at hj ⊢
    have : j = 0 := by omega
    subst this
    simpa [BitVec.getLsbD_eq_getElem] using tcr_bit rho caller d ⟨40, by decide⟩ true _ rfl
  have pie : spec.params.pie = 0#1 := by
    rw [sspec.paramsPie d]
    unfold ArmCert.Translate.Model.hostPIE
    rw [f209]
    rfl
  have tbi : spec.params.tbi = 1#1 := by
    have g := sspec.guardTbi d
    simp only [ArmCertWalk.translateGuardView, ArmCert.Translate.Model.currentHostGuardView] at g
    rw [g]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [ArmFull.Functions._get_TCR_EL2_Type_TBI0, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb] at hj ⊢
    have : j = 0 := by omega
    subst this
    simpa [BitVec.getLsbD_eq_getElem] using tcr_bit rho caller d ⟨37, by decide⟩ true _ rfl
  have tbid : spec.params.tbid = 0#1 := by
    have g := sspec.guardTbid d
    simp only [ArmCertWalk.translateGuardView, ArmCert.Translate.Model.currentHostGuardView, f98, ↓reduceIte] at g
    rw [g]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [ArmFull.Functions._get_TCR_EL2_Type_TBID0, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb] at hj ⊢
    have : j = 0 := by omega
    subst this
    simpa [BitVec.getLsbD_eq_getElem] using tcr_bit rho caller d ⟨51, by decide⟩ false _ rfl
  have nfd : spec.params.nfd = 0#1 := by
    have g := sspec.guardNfd d
    simp only [ArmCertWalk.translateGuardView, ArmCert.Translate.Model.currentHostGuardView, f81, ↓reduceIte] at g
    rw [g]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [ArmFull.Functions._get_TCR_EL2_Type_NFD0, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb] at hj ⊢
    have : j = 0 := by omega
    subst this
    simpa [BitVec.getLsbD_eq_getElem] using tcr_bit rho caller d ⟨53, by decide⟩ false _ rfl
  have e0pd : spec.params.e0pd = 0#1 := by
    have g := sspec.guardE0pd d
    simp only [ArmCertWalk.translateGuardView, ArmCert.Translate.Model.currentHostGuardView, f127, ↓reduceIte] at g
    rw [g]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [ArmFull.Functions._get_TCR_EL2_Type_E0PD0, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb] at hj ⊢
    have : j = 0 := by omega
    subst this
    simpa [BitVec.getLsbD_eq_getElem] using tcr_bit rho caller d ⟨55, by decide⟩ false _ rfl
  have mtx : spec.params.mtx = 0#1 := by
    rw [sspec.paramsMtx d]
    split
    · apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb] at hj ⊢
      have : j = 0 := by omega
      subst this
      simpa [BitVec.getLsbD_eq_getElem] using tcr_bit rho caller d ⟨60, by decide⟩ false _ rfl
    · rfl
  have txsz : spec.params.txsz = 16#6 := by
    rw [sspec.normalizedTxsz d, sourceRegs_bank64 rho caller d .TCR_EL2, sourceT0SZ rho caller]
    exact normalizeTxsz_16 _
  have cpie : spec.controls.pie = false := by
    rw [sspec.pie d, ← sspec.paramsPie d, pie]
    rfl
  have hpd : spec.controls.hpd = false := by
    rw [sspec.hpd d]
    rw [getElem!_pos (sourceRegs rho caller d).FeatureImpl 48 (by decide), f48]
    simp only [↓reduceIte]
    have b : Sail.BitVec.extractLsb ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.TCR_EL2) 41 41 = 0#1 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb] at hj ⊢
      have : j = 0 := by omega
      subst this
      simpa [BitVec.getLsbD_eq_getElem] using tcr_bit rho caller d ⟨41, by decide⟩ false _ rfl
    rw [b]
    rfl
  exact ⟨ha, hd, pie, tbi, tbid, nfd, e0pd, mtx, txsz, cpie, hpd⟩

end ReleaseProfile.GB10

#print axioms ReleaseProfile.GB10.sourceIPS
#print axioms ReleaseProfile.GB10.sourcePhysical_eq
#print axioms ReleaseProfile.GB10.sourceT0SZ
#print axioms ReleaseProfile.GB10.normalizeWalkParams_16
#print axioms ReleaseProfile.GB10.normalizeTxsz_16
#print axioms ReleaseProfile.GB10.overlay_source
#print axioms ReleaseProfile.GB10.nativeParams_ha
#print axioms ReleaseProfile.GB10.nativeParams_hd
#print axioms ReleaseProfile.GB10.nativeParams_pie
#print axioms ReleaseProfile.GB10.nativeParams_txsz
#print axioms ReleaseProfile.GB10.nativeParams_wxn
#print axioms ReleaseProfile.GB10.nativeParams_mtx
#print axioms ReleaseProfile.GB10.nativeParams_guards
#print axioms ReleaseProfile.GB10.nativeParams_haft
#print axioms ReleaseProfile.GB10.nativeParams_congr
#print axioms ReleaseProfile.GB10.sourceSpec_exists
#print axioms ReleaseProfile.GB10.sourceSpec_of_tables
#print axioms ReleaseProfile.GB10.sourceSpec_walkLiterals
