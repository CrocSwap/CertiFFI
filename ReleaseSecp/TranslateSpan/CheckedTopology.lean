-- A raw deployment topology contains data only. The finite checker derives
-- the existing certificate fields, which are erased in executable checks.
import TranslateSpan.StaticData
import ReleaseProfile.GB10.SpecWitness
import ReleaseProfile.GB10.ModelEntry
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.CheckedTopology

/-- Topology tables: program data (layout and descriptor rows), no configuration. -/
structure Tables where
  layout : S1LogicalReference.Layout
  logicalRows : List LogicalRow
  imageRows : List ImageRow

/-- A raw deployment topology. CONFIGURATION SINK: the constructor is private;
the only producer is `canonicalRaw` below (canonical source projections + tables). -/
structure Raw where
  private mk ::
  params : S1TTWParams
  physicalConfig : PhysicalConfig
  controls : S1LogicalReference.Controls
  layout : S1LogicalReference.Layout
  logicalRows : List LogicalRow
  imageRows : List ImageRow

def check (raw : Raw) (addresses : List (BitVec 64)) (fuel : Nat) : Bool :=
  StaticData.checkTopology 1030 raw.physicalConfig raw.layout raw.logicalRows raw.imageRows addresses fuel

/-- The checked spec: a pure PROJECT of the raw's fields; the proof fields come from the row/query checks only
(no configuration-valued helper is applied). -/
def spec (raw : Raw) (addresses : List (BitVec 64)) (fuel : Nat)
    (checked : check raw addresses fuel = true) :
    TopologyImageSpec (fun q => q.va ∈ addresses) where
  params := raw.params
  physicalConfig := raw.physicalConfig
  controls := raw.controls
  layout := raw.layout
  logicalRows := raw.logicalRows
  imageRows := raw.imageRows
  available := by
    have c := checked
    simp only [check, StaticData.checkTopology, Bool.and_eq_true] at c
    rintro logical physical view ⟨row, member, rfl, rfl, rfl⟩
    obtain ⟨a, b, d, _⟩ := logical_row_facts c.1.2 member
    exact ⟨a, b, d⟩
  identity := by
    have c := checked
    simp only [check, StaticData.checkTopology, Bool.and_eq_true] at c
    rintro logical physical view ⟨row, member, rfl, rfl, rfl⟩
    obtain ⟨_, _, _, d, e, _⟩ := logical_row_facts c.1.2 member
    exact ⟨d, e⟩
  represented := by
    have c := checked
    simp only [check, StaticData.checkTopology, Bool.and_eq_true] at c
    rintro logical physical view ⟨row, member, rfl, rfl, rfl⟩
    obtain ⟨_, _, _, _, _, image, imageMember, slot, view⟩ := logical_row_facts c.1.2 member
    exact ⟨image.leaf, image, imageMember, slot.symm, rfl, view.symm⟩
  aligned := by
    have c := checked
    simp only [check, StaticData.checkTopology, Bool.and_eq_true] at c
    have rowsOK := c.1.2
    rintro slot leaf view ⟨image, member, rfl, _, _⟩
    simp only [checkSpecRows, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at rowsOK
    exact rowsOK.2 image member
  rootBound := by
    intro q member
    have c := checked
    simp only [check, StaticData.checkTopology, Bool.and_eq_true] at c
    have each := List.all_eq_true.mp c.2 (StaticData.canonical q.va) (List.mem_map.mpr ⟨q.va, member, rfl⟩)
    simp only [checkSpecQuery, Bool.and_eq_true, decide_eq_true_eq] at each
    exact each.1
  paths := by
    intro q member
    have c := checked
    simp only [check, StaticData.checkTopology, Bool.and_eq_true] at c
    have each := List.all_eq_true.mp c.2 (StaticData.canonical q.va) (List.mem_map.mpr ⟨q.va, member, rfl⟩)
    simp only [checkSpecQuery, Bool.and_eq_true] at each
    obtain ⟨_, walked⟩ := each
    split at walked
    · rename_i leafLevel logical physical view found
      exact ⟨leafLevel, logical, physical, view,
        walkPath_sound _ _ _ _ _ _ _ _ _ _ _ found, leaf_image_row_sound _ _ _ walked⟩
    · simp at walked

/-! ## The canonical (sole) Raw producer: source projections + program-data tables -/

section canonical
open ReleaseProfile.MachineSource ReleaseProfile.GB10

/-- The source-register model state (memory irrelevant to the params read). -/
def sourceState (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (d : DataPart) : ArmCert.Translate.Model.State :=
  makeModelEntry sem rho caller ⟨d, ∅⟩

theorem sourceState_ok (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (d : DataPart) : ∃ p s', ArmCert.Translate.Model.hostNative (sourceState sem rho caller d) = .ok p s' :=
  ⟨_, _, rfl⟩

/-- Generic, configuration-free: the value of a result known to be `.ok` (motive is a type variable). -/
def okValue {ε σ α : Type} : (r : EStateM.Result ε σ α) → (∃ a s, r = .ok a s) → α
  | .ok a _, _ => a
  | .error _ _, h => absurd h (by rintro ⟨a, s, h⟩; cases h)

theorem okValue_spec {ε σ α : Type} (r : EStateM.Result ε σ α) (h : ∃ a s, r = .ok a s) :
    ∃ s, r = .ok (okValue r h) s := by
  cases r with
  | ok a s => exact ⟨s, rfl⟩
  | error e s => exact absurd h (by rintro ⟨a, s', h'⟩; cases h')

/-- Sail AArch64_S1TTWParamsEL20 at the source-register state (`hostNative`), via the generic `okValue`
(`sourceState_ok` discharges the error case; no fallback value). -/
noncomputable def canonicalSail (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (d : DataPart) : S1TTWParams :=
  okValue (ArmCert.Translate.Model.hostNative (sourceState sem rho caller d)) (sourceState_ok sem rho caller d)

/-- Canonical params: Sail's EL2&0 params with the Sail-undefined (oracle) fields from the oracle choice. -/
noncomputable def canonicalParams (sem : ModelSemantics) (rho : AdmissibleSourceCompletion)
    (caller : AdmissibleCaller rho) (d : DataPart) (o : OracleChoice) : S1TTWParams :=
  let sail := canonicalSail sem rho caller d
  { sail with dc := o.dc, dct := o.dct, nv1 := o.nv1, t0sz := o.t0sz, t1sz := o.t1sz,
              uwxn := o.uwxn, mair2 := o.mair2, pir := o.pir, pire0 := o.pire0 }

/-- Canonical reference controls: source projections (`sourceSpec_exists` record). -/
noncomputable def canonicalControls (sem : ModelSemantics) (rho : AdmissibleSourceCompletion)
    (caller : AdmissibleCaller rho) (d : DataPart) (o : OracleChoice) : S1LogicalReference.Controls :=
  let sail := canonicalSail sem rho caller d
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

/-- **The sole Raw producer** (SOURCE rule): canonical params/controls, `sourcePhysical`, program-data tables. -/
noncomputable def canonicalRaw (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (d : DataPart) (o : OracleChoice) (t : Tables) : Raw :=
  Raw.mk (canonicalParams sem rho caller d o) (sourcePhysical rho caller) (canonicalControls sem rho caller d o)
    t.layout t.logicalRows t.imageRows

end canonical

#print axioms check
#print axioms spec
#print axioms canonicalRaw
end TranslateSpan.CheckedTopology
