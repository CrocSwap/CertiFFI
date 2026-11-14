import XlateSecp.World
import ReleaseProfile.GB10.SpecWitness
import TranslateSpan.CheckedTopology
import ReleaseProfile.GB10.TablesBuilder
import ReleaseProfile.GB10.WorldSemantics

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Secp raw = the canonical producer

`CheckedTopology.Raw` is a configuration sink with a private constructor; its sole producer is
`TranslateSpan.CheckedTopology.canonicalRaw` (canonical params/controls from the source registers, `sourcePhysical`,
program-data tables). `canonicalRaw_source`: every checked spec of a canonical raw is `SourceSpec` (adapted from
`sourceSpec_exists`). `R sem rho caller c pcount` = the canonical raw at card `c`'s World entry data and tables.
-/

namespace XlateSecp.Raw

open ReleaseProfile.MachineSource ReleaseProfile.GB10 TranslateSpan TranslateSpan.CheckedTopology ArmCert.Translate.Model

theorem canonicalSail_ok (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (d : DataPart) : ∃ s', hostNative (sourceState sem rho caller d) = .ok (canonicalSail sem rho caller d) s' :=
  okValue_spec _ _

theorem sourceSpec_congr {rho : AdmissibleSourceCompletion} {caller : AdmissibleCaller rho}
    {d1 d2 : QueryDomain} {s1 : TopologyImageSpec d1} {s2 : TopologyImageSpec d2}
    (hp : s2.params = s1.params) (hc : s2.controls = s1.controls)
    (hph : s2.physicalConfig = s1.physicalConfig)
    (h : SourceSpec rho caller s1) : SourceSpec rho caller s2 := by
  cases h
  constructor <;> simp only [hp, hc, hph] <;> assumption

/-- Every checked spec of a canonical raw is source-pinned. -/
theorem canonicalRaw_source (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (d : DataPart) (o : OracleChoice) (t : Tables) (addrs : List (BitVec 64))
    (h : check (canonicalRaw sem rho caller d o t) addrs 4 = true) :
    SourceSpec rho caller (spec (canonicalRaw sem rho caller d o t) addrs 4 h) := by
  obtain ⟨s', h0⟩ := canonicalSail_ok sem rho caller d
  generalize hsail : canonicalSail sem rho caller d = sail at h0
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
    { sail with dc := o.dc, dct := o.dct, nv1 := o.nv1,
                t0sz := o.t0sz, t1sz := o.t1sz, uwxn := o.uwxn,
                mair2 := o.mair2, pir := o.pir, pire0 := o.pire0 }
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
      mair := sail.mair, mair2 := o.controlsMair2,
      pir := ArmFull.Functions.Mk_S1PIRType ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.PIR_EL2),
      pire0 := ArmFull.Functions.Mk_S1PIRType ((sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.PIRE0_EL2),
      poe := false, e0poe := false,
      por := (sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.POR_EL2,
      porE0 := (sourceRegs rho caller d).bank_BitVec_64 ArmFull.Bank_BitVec_64.POR_EL0,
      cmow := (sail.cmow == 1#1), wxn := (sail.wxn == 1#1), uwxn := o.controlsUwxn,
      pan := (caller.caller.pstate.PAN == 1#1), epan := (sail.epan == 1#1) }
  -- the Sail params of any other state carrying the source registers agree outside the oracle fields
  have other : ∀ (dd : DataPart) (state : ArmCert.Translate.Model.State) (sail' : ArmFull.S1TTWParams) next,
      state.regs = sourceRegs rho caller dd → ArmCert.Translate.Model.hostNative state = .ok sail' next →
      ({ sail' with dc := o.dc, dct := o.dct, nv1 := o.nv1, t0sz := o.t0sz, t1sz := o.t1sz, uwxn := o.uwxn, mair2 := o.mair2, pir := o.pir, pire0 := o.pire0 } : ArmFull.S1TTWParams) = fixed ∧
        sail'.txsz = 16#6 := by
    intro dd state sail' next hregs hns
    refine ⟨?_, ?_⟩
    · exact nativeParams_congr state (sourceState sem rho caller d) sail' sail next s' hns h0
        (fun k hk => by rw [hregs]; exact (sourceBank64_ne rho caller dd k hk).trans (sourceBank64_ne rho caller d k hk).symm)
        (by rw [hregs]; rfl) h242 (canonicalParams sem rho caller d o)
    · rw [nativeParams_txsz _ _ _ hns, hregs]
      exact sourceT0SZ rho caller
  have hpar : (spec (canonicalRaw sem rho caller d o t) addrs 4 h).params = fixed := by
    show canonicalParams sem rho caller d o = fixed
    unfold canonicalParams; rw [hsail]
  have hcon : (spec (canonicalRaw sem rho caller d o t) addrs 4 h).controls = controls := by
    show canonicalControls sem rho caller d o = controls
    unfold canonicalControls; rw [hsail]
  refine sourceSpec_congr (s1 := { spec (canonicalRaw sem rho caller d o t) addrs 4 h with params := fixed, controls := controls })
    hpar hcon rfl ?_
  constructor
  case physical => rfl
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

/-- Oracle choices in the Sail-undefined EL2&0 fields (semantics, not configuration; as HeapWorldData.oracle). -/
def oracle : OracleChoice where
  dc := 0#1
  dct := 0#1
  nv1 := 0#1
  t0sz := 0#3
  t1sz := 0#3
  uwxn := 0#1
  mair2 := 0
  pir := 0
  pire0 := 0
  controlsMair2 := 0#64
  controlsUwxn := false

/-- The canonical secp raw at card `c`'s World entry (data read back from the entry registers, the C1/C2 residual form),
the World tables and ANY oracle choice `o` for the Sail-undefined EL2&0 fields. -/
noncomputable abbrev Ro (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) (o : OracleChoice) : CheckedTopology.Raw :=
  canonicalRaw sem rho caller (dataOf (World.entry sem rho caller c pcount).regs) o World.tables

/-- The instance used by the C2 roots: `o := oracle`. -/
noncomputable abbrev R (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) : CheckedTopology.Raw :=
  Ro sem rho caller c pcount oracle

theorem Ro_source (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) (o : OracleChoice) (addrs : List (BitVec 64))
    (h : check (Ro sem rho caller c pcount o) addrs 4 = true) :
    SourceSpec rho caller (spec (Ro sem rho caller c pcount o) addrs 4 h) :=
  canonicalRaw_source sem rho caller _ o World.tables addrs h

theorem R_source (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) (addrs : List (BitVec 64)) (h : check (R sem rho caller c pcount) addrs 4 = true) :
    SourceSpec rho caller (spec (R sem rho caller c pcount) addrs 4 h) :=
  Ro_source sem rho caller c pcount oracle addrs h

/-- The topology check of the World tables at the GB10 physical configuration (no params/controls). -/
def checkTables (addrs : List (BitVec 64)) : Bool :=
  StaticData.checkTopology 1030 gb10Physical World.layout World.logicalRows World.imageRows addrs 4

theorem Ro_check_eq (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) (o : OracleChoice) (addrs : List (BitVec 64)) :
    check (Ro sem rho caller c pcount o) addrs 4 = checkTables addrs := by
  have hp : sourcePhysical rho caller = gb10Physical := sourcePhysical_eq rho caller
  show StaticData.checkTopology 1030 (sourcePhysical rho caller) _ _ _ addrs 4 = _
  rw [hp]
  rfl

theorem Ro_layout (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) (o : OracleChoice) : (Ro sem rho caller c pcount o).layout = World.layout := rfl

theorem Ro_imageRows (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : World.Card) (pcount : BitVec 88) (o : OracleChoice) : (Ro sem rho caller c pcount o).imageRows = World.imageRows := rfl

/-! PROJECT evidence: `spec` reads its raw only through the raw's fields. -/
theorem spec_params (raw : CheckedTopology.Raw) (a : List (BitVec 64)) (f : Nat) (h : check raw a f = true) :
    (spec raw a f h).params = raw.params := rfl
theorem spec_controls (raw : CheckedTopology.Raw) (a : List (BitVec 64)) (f : Nat) (h : check raw a f = true) :
    (spec raw a f h).controls = raw.controls := rfl
theorem spec_physical (raw : CheckedTopology.Raw) (a : List (BitVec 64)) (f : Nat) (h : check raw a f = true) :
    (spec raw a f h).physicalConfig = raw.physicalConfig := rfl
theorem spec_tables (raw : CheckedTopology.Raw) (a : List (BitVec 64)) (f : Nat) (h : check raw a f = true) :
    (spec raw a f h).layout = raw.layout ∧ (spec raw a f h).logicalRows = raw.logicalRows ∧
      (spec raw a f h).imageRows = raw.imageRows := ⟨rfl, rfl, rfl⟩

end XlateSecp.Raw

#print axioms XlateSecp.Raw.canonicalRaw_source
#print axioms XlateSecp.Raw.Ro_check_eq
#print axioms XlateSecp.Raw.Ro_source
