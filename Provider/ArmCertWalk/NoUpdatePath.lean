-- shape, option B ("no hardware update fires on the declared tables"), derived from
-- CURRENT declared data: the raw-exact image (ImageRow.check reads all eight actual bytes)
-- and a decidable per-row no-update check on the declared raw words. Fails closed.
import ArmCertWalk.LeafSwapTotal
import ArmCertTranslateModel.CheckImage
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

/-- Every declared row's exact raw word is present in memory (LE, E3). -/
def RawImageAt (rows : List ImageRow) (mem : Mem) : Prop :=
  ∀ row ∈ rows, S1ByteMemory.DescAt mem row.slot row.raw

/-- No hardware AF/dirty update can fire on a declared row: EVERY row is fixed by the
table AF update (a row's role tag is not tied to the walk's use), and rows tagged leaf
(the walk's leaf use is tagged `true`) are fixed by the leaf AF/dirty update for `acc`. -/
def RowNoUpdate (params : S1TTWParams) (acc : AccessDescriptor) (row : ImageRow) : Bool :=
  decide (S1TableUpdate.word params row.raw = row.raw) &&
    (!row.leaf || decide (leafUpdateWord params acc row.raw = row.raw))

def NoUpdateRows (params : S1TTWParams) (acc : AccessDescriptor) (rows : List ImageRow) : Bool :=
  rows.all (RowNoUpdate params acc)

theorem raw_image_of_check (rows : List ImageRow) (pie ha hd : Bool) (mem : Mem)
    (checked : checkImage rows pie ha hd mem = true) : RawImageAt rows mem := by
  intro row member
  have each := List.all_eq_true.mp checked row member
  exact (ImageRow.check_sound row pie ha hd mem each).1

theorem table_no_update {params : S1TTWParams} {acc : AccessDescriptor} {rows : List ImageRow}
    (none : NoUpdateRows params acc rows = true) {row : ImageRow} (member : row ∈ rows) :
    S1TableUpdate.word params row.raw = row.raw := by
  have each := List.all_eq_true.mp none row member
  simp only [RowNoUpdate, Bool.and_eq_true, decide_eq_true_eq] at each
  exact each.1

theorem leaf_no_update {params : S1TTWParams} {acc : AccessDescriptor} {rows : List ImageRow}
    (none : NoUpdateRows params acc rows = true) {row : ImageRow} (member : row ∈ rows)
    (leaf : row.leaf = true) : leafUpdateWord params acc row.raw = row.raw := by
  have each := List.all_eq_true.mp none row member
  simp only [RowNoUpdate, Bool.and_eq_true, decide_eq_true_eq, leaf, Bool.not_true, Bool.false_or] at each
  exact each.2

theorem history_nil_mem {params : S1TTWParams} {footprint : Footprint} {before after : Mem}
    (history : StoreHistory params footprint before [] after) : after = before := by
  cases history
  rfl

/-- The no-update check depends only on haft/ha/hd/pie. -/
theorem noUpdate_congr {p q : S1TTWParams} (haft : p.haft = q.haft) (ha : p.ha = q.ha) (hd : p.hd = q.hd)
    (pie : p.pie = q.pie) (acc : AccessDescriptor) (rows : List ImageRow) :
    NoUpdateRows p acc rows = NoUpdateRows q acc rows := by
  have rowEq : RowNoUpdate p acc = RowNoUpdate q acc := by
    funext row
    unfold RowNoUpdate leafUpdateWord leafDirtyEnabled S1TableUpdate.word
    rw [haft, ha, hd, pie]
  simp only [NoUpdateRows, rowEq]

/-- The descriptor actually present at a declared row's slot IS its raw word. -/
theorem raw_at_slot {rows : List ImageRow} {mem : Mem} (raw : RawImageAt rows mem)
    {row : ImageRow} (member : row ∈ rows) {d : BitVec 64}
    (present : S1ByteMemory.DescAt mem row.slot d) : d = row.raw :=
  S1ByteMemory.descriptor_unique mem row.slot d row.raw present (raw row member)

#print axioms raw_image_of_check
#print axioms raw_at_slot
end ArmCertWalk
