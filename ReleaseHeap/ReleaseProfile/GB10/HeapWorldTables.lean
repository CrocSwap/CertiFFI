import ReleaseProfile.GB10.TablesBuilder

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

/-!
# Heap C2 world: page-table data

Clean, release-named regeneration of the ControlRows shim-frame page tables (ArmCertTranslateModel.DryRunShim
values: descriptors, logical/image rows, root 0x80000000, base 0x400000, queries). Program/table data
only: no params, controls, attribute configuration or register file. The tables are `GB10.TopologyTables`
built from the decidable row/query checks at `gb10Physical`; the world spec is
`GB10.sourceSpec_of_tables` (source-pinned). Row `prior`/`attributes` are literal data (the classic
table-permission walk with all-zero table bits; normal WB attributes at MAIR index 0), to be checked
against the source spec/config by the card's own row atoms.
-/

namespace ReleaseProfile.GB10.HeapWorldTables

open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10

def viewOf (raw : BitVec 64) : S1DescriptorPIE.View 64 := S1DescriptorPIE.view false true true raw

def logicalRows : List LogicalRow := [
  ⟨2147483648, { paspace := .PAS_NonSecure, address := 0x80000000#56 }, viewOf 0x80001003#64⟩,
  ⟨2147487744, { paspace := .PAS_NonSecure, address := 0x80001000#56 }, viewOf 0x80002003#64⟩,
  ⟨2147491840, { paspace := .PAS_NonSecure, address := 0x80002000#56 }, viewOf 0x80003003#64⟩,
  ⟨2147491856, { paspace := .PAS_NonSecure, address := 0x80002010#56 }, viewOf 0x80004003#64⟩,
  ⟨2147500032, { paspace := .PAS_NonSecure, address := 0x80004000#56 }, viewOf 0x600000801007c3#64⟩,
  ⟨2147500160, { paspace := .PAS_NonSecure, address := 0x80004080#56 }, viewOf 0x200000801107c3#64⟩,
  ⟨2147500288, { paspace := .PAS_NonSecure, address := 0x80004100#56 }, viewOf 0x68000080120743#64⟩,
  ⟨2147496320, { paspace := .PAS_NonSecure, address := 0x80003180#56 }, viewOf 0x68000080130743#64⟩,
  ⟨2147496328, { paspace := .PAS_NonSecure, address := 0x80003188#56 }, viewOf 0x68000080131743#64⟩,
  ⟨2147500024, { paspace := .PAS_NonSecure, address := 0x80003ff8#56 }, viewOf 0x680000801ff743#64⟩,
  ⟨2147491848, { paspace := .PAS_NonSecure, address := 0x80002008#56 }, viewOf 0x80005003#64⟩,
  ⟨2147504128, { paspace := .PAS_NonSecure, address := 0x80005000#56 }, viewOf 0x68000080200743#64⟩
]

def imageRows : List ImageRow := [
  ⟨2147483648, false, 0x80001003#64, viewOf 0x80001003#64⟩,
  ⟨2147487744, false, 0x80002003#64, viewOf 0x80002003#64⟩,
  ⟨2147491840, false, 0x80003003#64, viewOf 0x80003003#64⟩,
  ⟨2147491848, false, 0x80005003#64, viewOf 0x80005003#64⟩,
  ⟨2147491856, false, 0x80004003#64, viewOf 0x80004003#64⟩,
  ⟨2147496320, true, 0x68000080130743#64, viewOf 0x68000080130743#64⟩,
  ⟨2147496328, true, 0x68000080131743#64, viewOf 0x68000080131743#64⟩,
  ⟨2147500024, true, 0x680000801ff743#64, viewOf 0x680000801ff743#64⟩,
  ⟨2147500032, true, 0x600000801007c3#64, viewOf 0x600000801007c3#64⟩,
  ⟨2147500160, true, 0x200000801107c3#64, viewOf 0x200000801107c3#64⟩,
  ⟨2147500288, true, 0x68000080120743#64, viewOf 0x68000080120743#64⟩,
  ⟨2147504128, true, 0x68000080200743#64, viewOf 0x68000080200743#64⟩
]

def root : BitVec 48 := 0x80000000#48

def base : Nat := 4194304

/-- SYNTHETIC: rows pass the decidable spec-row checks. -/
theorem dry_spec_rows : checkSpecRows logicalRows imageRows = true := by decide

/-- SYNTHETIC: reference walk of VA 0x400000 reaches the level-3 leaf at slot 0x80004000. -/
theorem dry_walk_0 : walkPath logicalRows 40 0x400000#64 4 0 9 root =
    some (.leaf 3 2147500032 { paspace := .PAS_NonSecure, address := 0x80004000#56 } (viewOf 0x600000801007c3#64)) := by
  rfl

/-- SYNTHETIC: reference walk of VA 0x410278 reaches the level-3 leaf at slot 0x80004080. -/
theorem dry_walk_1 : walkPath logicalRows 40 0x410278#64 4 0 9 root =
    some (.leaf 3 2147500160 { paspace := .PAS_NonSecure, address := 0x80004080#56 } (viewOf 0x200000801107c3#64)) := by
  rfl

/-- SYNTHETIC: reference walk of VA 0x420000 reaches the level-3 leaf at slot 0x80004100. -/
theorem dry_walk_2 : walkPath logicalRows 40 0x420000#64 4 0 9 root =
    some (.leaf 3 2147500288 { paspace := .PAS_NonSecure, address := 0x80004100#56 } (viewOf 0x68000080120743#64)) := by
  rfl

/-- SYNTHETIC: reference walk of VA 0x30000 reaches the level-3 leaf at slot 0x80003180. -/
theorem dry_walk_3 : walkPath logicalRows 40 0x30000#64 4 0 9 root =
    some (.leaf 3 2147496320 { paspace := .PAS_NonSecure, address := 0x80003180#56 } (viewOf 0x68000080130743#64)) := by
  rfl

/-- SYNTHETIC: reference walk of VA 0x31000 reaches the level-3 leaf at slot 0x80003188. -/
theorem dry_walk_4 : walkPath logicalRows 40 0x31000#64 4 0 9 root =
    some (.leaf 3 2147496328 { paspace := .PAS_NonSecure, address := 0x80003188#56 } (viewOf 0x68000080131743#64)) := by
  rfl

/-- SYNTHETIC: reference walk of VA 0x1ff000 reaches the level-3 leaf at slot 0x80003ff8. -/
theorem dry_walk_5 : walkPath logicalRows 40 0x1ff000#64 4 0 9 root =
    some (.leaf 3 2147500024 { paspace := .PAS_NonSecure, address := 0x80003ff8#56 } (viewOf 0x680000801ff743#64)) := by
  rfl

/-- SYNTHETIC: reference walk of VA 0x200000 (shim frame) reaches the level-3 leaf at slot 0x80005000. -/
theorem dry_walk_6 : walkPath logicalRows 40 0x200000#64 4 0 9 root =
    some (.leaf 3 2147504128 { paspace := .PAS_NonSecure, address := 0x80005000#56 } (viewOf 0x68000080200743#64)) := by
  rfl

/-- Native permission witness read off the descriptor bits and the walked table prior. -/
def witnessOf (tbl : S1LogicalReference.TablePermissions) (raw : BitVec 64) : ArmFull.Permissions :=
  let base : ArmFull.Permissions := default
  { base with
    ap_table := tbl.ap
    pxn_table := BitVec.ofBool tbl.pxn
    uxn_table := BitVec.ofBool tbl.uxn
    ap := ((raw.extractLsb' 6 2).setWidth 3) <<< 1
    pxn := BitVec.ofBool (raw.getLsbD 53)
    uxn := BitVec.ofBool (raw.getLsbD 54) }

/-- Table-walk prior of every query (all table descriptors carry zero AP/PXN/UXN table bits). -/
def tablePrior : S1LogicalReference.TablePermissions := ⟨0#2, false, false⟩

/-- Normal inner/outer write-back attributes (MAIR index 0 = 0xff), untagged, XS = 0. -/
def wbAttributes : AttributeBody :=
  { kind := .normal { attrs := 3#2, hints := some 3#2, transient := some false }
      { attrs := 3#2, hints := some 3#2, transient := some false }
    tags := .MemTag_Untagged, noTagAccess := false, xs := 0#1 }

/-- Page-table layout: start level 0, 48-bit input, root at 0x80000000. -/
def layout : S1LogicalReference.Layout := ⟨0, 48, root⟩

def fetchAcc : AccessDescriptor := { (default : AccessDescriptor) with acctype := .AccessType_IFETCH, el := 0#2, ss := .SS_NonSecure }
def fetchQuery : AccessQuery := ⟨0x410278#64, ⟨fetchAcc, true⟩, 4⟩
def fetchRow : PermissionRow :=
  { slot := 2147500160, raw := 0x200000801107c3#64, prior := tablePrior,
    attributes := wbAttributes,
    access := fetchAcc, witness := witnessOf tablePrior 0x200000801107c3#64 }

def dataReadAcc : AccessDescriptor := { (default : AccessDescriptor) with acctype := .AccessType_GPR, el := 0#2, ss := .SS_NonSecure, read := true, write := false }
def dataReadQuery : AccessQuery := ⟨0x420548#64, ⟨dataReadAcc, true⟩, 8⟩
def dataReadRow : PermissionRow :=
  { slot := 2147500288, raw := 0x68000080120743#64, prior := tablePrior,
    attributes := wbAttributes,
    access := dataReadAcc, witness := witnessOf tablePrior 0x68000080120743#64 }

def inputReadAcc : AccessDescriptor := { (default : AccessDescriptor) with acctype := .AccessType_GPR, el := 0#2, ss := .SS_NonSecure, read := true, write := false }
def inputReadQuery : AccessQuery := ⟨0x30000#64, ⟨inputReadAcc, true⟩, 1⟩
def inputReadRow : PermissionRow :=
  { slot := 2147496320, raw := 0x68000080130743#64, prior := tablePrior,
    attributes := wbAttributes,
    access := inputReadAcc, witness := witnessOf tablePrior 0x68000080130743#64 }

def outputWriteAcc : AccessDescriptor := { (default : AccessDescriptor) with acctype := .AccessType_GPR, el := 0#2, ss := .SS_NonSecure, read := false, write := true }
def outputWriteQuery : AccessQuery := ⟨0x31000#64, ⟨outputWriteAcc, true⟩, 1⟩
def outputWriteRow : PermissionRow :=
  { slot := 2147496328, raw := 0x68000080131743#64, prior := tablePrior,
    attributes := wbAttributes,
    access := outputWriteAcc, witness := witnessOf tablePrior 0x68000080131743#64 }

def stackWriteAcc : AccessDescriptor := { (default : AccessDescriptor) with acctype := .AccessType_GPR, el := 0#2, ss := .SS_NonSecure, read := false, write := true }
def stackWriteQuery : AccessQuery := ⟨0x1ff000#64, ⟨stackWriteAcc, true⟩, 8⟩
def stackWriteRow : PermissionRow :=
  { slot := 2147500024, raw := 0x680000801ff743#64, prior := tablePrior,
    attributes := wbAttributes,
    access := stackWriteAcc, witness := witnessOf tablePrior 0x680000801ff743#64 }

def stackReadAcc : AccessDescriptor := { (default : AccessDescriptor) with acctype := .AccessType_GPR, el := 0#2, ss := .SS_NonSecure, read := true, write := false }
def stackReadQuery : AccessQuery := ⟨0x1fffc0#64, ⟨stackReadAcc, true⟩, 16⟩
def stackReadRow : PermissionRow :=
  { slot := 2147500024, raw := 0x680000801ff743#64, prior := tablePrior,
    attributes := wbAttributes,
    access := stackReadAcc, witness := witnessOf tablePrior 0x680000801ff743#64 }

def shimFrameWriteAcc : AccessDescriptor := { (default : AccessDescriptor) with acctype := .AccessType_GPR, el := 0#2, ss := .SS_NonSecure, read := false, write := true }
def shimFrameWriteQuery : AccessQuery := ⟨0x200000#64, ⟨shimFrameWriteAcc, true⟩, 16⟩
def shimFrameWriteRow : PermissionRow :=
  { slot := 2147504128, raw := 0x68000080200743#64, prior := tablePrior,
    attributes := wbAttributes,
    access := shimFrameWriteAcc, witness := witnessOf tablePrior 0x68000080200743#64 }

def shimFrameReadAcc : AccessDescriptor := { (default : AccessDescriptor) with acctype := .AccessType_GPR, el := 0#2, ss := .SS_NonSecure, read := true, write := false }
def shimFrameReadQuery : AccessQuery := ⟨0x200000#64, ⟨shimFrameReadAcc, true⟩, 16⟩
def shimFrameReadRow : PermissionRow :=
  { slot := 2147504128, raw := 0x68000080200743#64, prior := tablePrior,
    attributes := wbAttributes,
    access := shimFrameReadAcc, witness := witnessOf tablePrior 0x68000080200743#64 }

def queries : List AccessQuery := [fetchQuery, dataReadQuery, inputReadQuery, outputWriteQuery, stackWriteQuery, stackReadQuery,
  shimFrameWriteQuery, shimFrameReadQuery]
def permissionRows : List PermissionRow := [fetchRow, dataReadRow, inputReadRow, outputWriteRow, stackWriteRow, stackReadRow,
  shimFrameWriteRow, shimFrameReadRow]


theorem tables_queries : queries.all (checkSpecQuery gb10Physical layout logicalRows imageRows 4) = true := by
  decide

/-- The world's tables (page-keyed domain), tables only. -/
noncomputable def tables : TopologyTables (fun q => ∃ q0 ∈ queries, SamePage q0.va q.va) :=
  TablesBuilder.tablesOfChecksPage layout logicalRows imageRows queries 4 dry_spec_rows tables_queries

/-- E34 (static spec check): the logical-row keys of the reviewed tables are pairwise distinct;
kernel-decided over the concrete rows. -/
theorem logicalRows_nodup : (tables.logicalRows.map (·.logical)).Nodup := by
  decide +kernel

end ReleaseProfile.GB10.HeapWorldTables

#print axioms ReleaseProfile.GB10.HeapWorldTables.tables
#print axioms ReleaseProfile.GB10.HeapWorldTables.logicalRows_nodup
