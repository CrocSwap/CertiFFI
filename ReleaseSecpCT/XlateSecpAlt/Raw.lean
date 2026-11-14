import XlateSecpAlt.World
import ReleaseProfile.GB10.SpecWitness
import TranslateSpan.CheckedTopology
import ReleaseProfile.GB10.TablesBuilder
import ReleaseProfile.GB10.WorldSemantics
import XlateSecp.Raw

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Secp raw = the canonical producer

`CheckedTopology.Raw` is a configuration sink with a private constructor; its sole producer is
`TranslateSpan.CheckedTopology.canonicalRaw` (canonical params/controls from the source registers, `sourcePhysical`,
program-data tables). `XlateSecp.Raw.canonicalRaw_source`: every checked spec of a canonical raw is `SourceSpec` (adapted from
`sourceSpec_exists`). `R sem rho caller c pcount` = the canonical raw at card `c`'s World entry data and tables.
-/

namespace XlateSecpAlt.Raw

open ReleaseProfile.MachineSource ReleaseProfile.GB10 TranslateSpan TranslateSpan.CheckedTopology ArmCert.Translate.Model

/-- The canonical secp raw at card `c`'s World entry (data read back from the entry registers, the C1/C2 residual form),
the World tables and ANY XlateSecp.Raw.oracle choice `o` for the Sail-undefined EL2&0 fields. -/
noncomputable abbrev Ro (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) (o : OracleChoice) : CheckedTopology.Raw :=
  canonicalRaw sem rho caller (dataOf (XlateSecpAlt.World.entry sem rho caller c pcount).regs) o XlateSecp.World.tables

/-- The instance used by the C2 roots: `o := XlateSecp.Raw.oracle`. -/
noncomputable abbrev R (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) : CheckedTopology.Raw :=
  Ro sem rho caller c pcount XlateSecp.Raw.oracle

theorem Ro_source (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) (o : OracleChoice) (addrs : List (BitVec 64))
    (h : check (Ro sem rho caller c pcount o) addrs 4 = true) :
    SourceSpec rho caller (spec (Ro sem rho caller c pcount o) addrs 4 h) :=
  XlateSecp.Raw.canonicalRaw_source sem rho caller _ o XlateSecp.World.tables addrs h

theorem R_source (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) (addrs : List (BitVec 64)) (h : check (R sem rho caller c pcount) addrs 4 = true) :
    SourceSpec rho caller (spec (R sem rho caller c pcount) addrs 4 h) :=
  Ro_source sem rho caller c pcount XlateSecp.Raw.oracle addrs h

theorem Ro_check_eq (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) (o : OracleChoice) (addrs : List (BitVec 64)) :
    check (Ro sem rho caller c pcount o) addrs 4 = XlateSecp.Raw.checkTables addrs := by
  have hp : sourcePhysical rho caller = gb10Physical := sourcePhysical_eq rho caller
  show StaticData.checkTopology 1030 (sourcePhysical rho caller) _ _ _ addrs 4 = _
  rw [hp]
  rfl

theorem Ro_layout (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) (o : OracleChoice) : (Ro sem rho caller c pcount o).layout = XlateSecp.World.layout := rfl

theorem Ro_imageRows (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (c : XlateSecp.World.Card) (pcount : BitVec 88) (o : OracleChoice) : (Ro sem rho caller c pcount o).imageRows = XlateSecp.World.imageRows := rfl

/-! PROJECT evidence: `spec` reads its raw only through the raw's fields. -/
end XlateSecpAlt.Raw

#print axioms XlateSecpAlt.Raw.Ro_check_eq
#print axioms XlateSecpAlt.Raw.Ro_source
