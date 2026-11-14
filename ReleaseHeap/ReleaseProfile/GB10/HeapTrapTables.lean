import ReleaseProfile.GB10.HeapWorldTables

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

/-!
# Heap trap-world page tables

The normal world tables (`HeapWorldTables`) plus VA page 0 (leaf slot 0x80003000, output PA 0x80300000),
as in the ControlRows trap variants: on trap paths T0/T1 a caller buffer pin is 0, so the shim consumer map's
data accesses land on page 0. Image rows stay sorted by slot. Program/table data only.
-/

namespace ReleaseProfile.GB10.HeapTrapTables

open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10

def zeroLogical : LogicalRow :=
  ⟨2147495936, { paspace := .PAS_NonSecure, address := 0x80003000#56 }, HeapWorldTables.viewOf 0x68000080300743#64⟩

def logicalRows : List LogicalRow := HeapWorldTables.logicalRows ++ [zeroLogical]

def imageRows : List ImageRow := [
  ⟨2147483648, false, 0x80001003#64, HeapWorldTables.viewOf 0x80001003#64⟩,
  ⟨2147487744, false, 0x80002003#64, HeapWorldTables.viewOf 0x80002003#64⟩,
  ⟨2147491840, false, 0x80003003#64, HeapWorldTables.viewOf 0x80003003#64⟩,
  ⟨2147491848, false, 0x80005003#64, HeapWorldTables.viewOf 0x80005003#64⟩,
  ⟨2147491856, false, 0x80004003#64, HeapWorldTables.viewOf 0x80004003#64⟩,
  ⟨2147495936, true, 0x68000080300743#64, HeapWorldTables.viewOf 0x68000080300743#64⟩,
  ⟨2147496320, true, 0x68000080130743#64, HeapWorldTables.viewOf 0x68000080130743#64⟩,
  ⟨2147496328, true, 0x68000080131743#64, HeapWorldTables.viewOf 0x68000080131743#64⟩,
  ⟨2147500024, true, 0x680000801ff743#64, HeapWorldTables.viewOf 0x680000801ff743#64⟩,
  ⟨2147500032, true, 0x600000801007c3#64, HeapWorldTables.viewOf 0x600000801007c3#64⟩,
  ⟨2147500160, true, 0x200000801107c3#64, HeapWorldTables.viewOf 0x200000801107c3#64⟩,
  ⟨2147500288, true, 0x68000080120743#64, HeapWorldTables.viewOf 0x68000080120743#64⟩,
  ⟨2147504128, true, 0x68000080200743#64, HeapWorldTables.viewOf 0x68000080200743#64⟩
]

theorem spec_rows : checkSpecRows logicalRows imageRows = true := by decide

/-- Reference walk of VA 0 reaches the level-3 leaf at slot 0x80003000. -/
theorem walk_zero : walkPath logicalRows 40 0x0#64 4 0 9 HeapWorldTables.root =
    some (.leaf 3 2147495936 { paspace := .PAS_NonSecure, address := 0x80003000#56 } (HeapWorldTables.viewOf 0x68000080300743#64)) := by
  rfl

def zeroReadAcc : AccessDescriptor := { (default : AccessDescriptor) with acctype := .AccessType_GPR, el := 0#2, ss := .SS_NonSecure, read := true, write := false }
def zeroReadQuery : AccessQuery := ⟨0x0#64, ⟨zeroReadAcc, true⟩, 8⟩
def zeroReadRow : PermissionRow :=
  { slot := 2147495936, raw := 0x68000080300743#64, prior := HeapWorldTables.tablePrior, attributes := HeapWorldTables.wbAttributes,
    access := zeroReadAcc, witness := HeapWorldTables.witnessOf HeapWorldTables.tablePrior 0x68000080300743#64 }

def zeroWriteAcc : AccessDescriptor := { (default : AccessDescriptor) with acctype := .AccessType_GPR, el := 0#2, ss := .SS_NonSecure, read := false, write := true }
def zeroWriteQuery : AccessQuery := ⟨0x0#64, ⟨zeroWriteAcc, true⟩, 8⟩
def zeroWriteRow : PermissionRow :=
  { slot := 2147495936, raw := 0x68000080300743#64, prior := HeapWorldTables.tablePrior, attributes := HeapWorldTables.wbAttributes,
    access := zeroWriteAcc, witness := HeapWorldTables.witnessOf HeapWorldTables.tablePrior 0x68000080300743#64 }

def queries : List AccessQuery := HeapWorldTables.queries ++ [zeroReadQuery, zeroWriteQuery]
def permissionRows : List PermissionRow := HeapWorldTables.permissionRows ++ [zeroReadRow, zeroWriteRow]

theorem tables_queries : queries.all (checkSpecQuery gb10Physical HeapWorldTables.layout logicalRows imageRows 4) = true := by
  decide

/-- The trap worlds' tables (page-keyed domain), tables only. -/
noncomputable def tables : TopologyTables (fun q => ∃ q0 ∈ queries, SamePage q0.va q.va) :=
  TablesBuilder.tablesOfChecksPage HeapWorldTables.layout logicalRows imageRows queries 4 spec_rows tables_queries

/-- E34 (static spec check): the logical-row keys of the reviewed tables are pairwise distinct;
kernel-decided over the concrete rows. -/
theorem logicalRows_nodup : (tables.logicalRows.map (·.logical)).Nodup := by
  decide +kernel

end ReleaseProfile.GB10.HeapTrapTables

#print axioms ReleaseProfile.GB10.HeapTrapTables.tables
#print axioms ReleaseProfile.GB10.HeapTrapTables.logicalRows_nodup
