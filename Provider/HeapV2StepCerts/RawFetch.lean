-- Memory: RawImageAt across the actual FETCH. The fetch's translation updates no row when
-- NoUpdateRows holds for its (read-only, IFETCH) descriptor; that is the same Boolean as for any read
-- (DataShape false) descriptor, since leaf AF/dirty updates read `acc` only through `acc.write`.
import ArmCertWalk.NativeFetchPreservingEvents
import ArmCertTranslateModel.ClosedTable
import Bridge.CruxGenGuarded.EntryActualFetch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
namespace HeapV2StepCerts.RawFetch
open ArmCertWalk ArmBridge.Draft

/-- NoUpdateRows depends on the descriptor only through `write`. -/
theorem noUpd_write_eq (params : S1TTWParams) (rows : List ImageRow) (a b : AccessDescriptor)
    (ha : a.write = false) (hb : b.write = false) : NoUpdateRows params a rows = NoUpdateRows params b rows := by
  unfold NoUpdateRows RowNoUpdate leafUpdateWord leafDirtyEnabled
  simp only [ha, hb, Bool.and_false, Bool.false_and]

/-- A read DataShape descriptor exists (so a ∀-DataShape NoUpdateRows field covers reads). -/
theorem dataShape_read : ∃ acc : AccessDescriptor, DataShape false acc := by
  refine ⟨{ (default : AccessDescriptor) with acctype := AccessType.AccessType_GPR, el := EL0, ss := SecurityState.SS_NonSecure, read := true, write := false, tagaccess := false, transactional := false, nonfault := false, contiguous := false, firstfault := false, «first» := false, ls64 := false }, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ChainInv v3's DataShape NoUpdateRows field gives NoUpdateRows for any read descriptor (e.g. IFETCH). -/
theorem noUpd_read {params : S1TTWParams} {rows : List ImageRow}
    (noUpd : ∀ w acc, DataShape w acc → NoUpdateRows params acc rows = true)
    (acc : AccessDescriptor) (hw : acc.write = false) : NoUpdateRows params acc rows = true := by
  obtain ⟨r, hr⟩ := dataShape_read
  rw [noUpd_write_eq params rows acc r hw hr.write]
  exact noUpd false r hr

/-- hostHAFT is untouched by beforeFetchState and the fetch prelude. -/
theorem haft_fetchPre (x : NativeState) :
    hostHAFT (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState x)).regs = hostHAFT x.regs := rfl

/-- **RawImageAt across the fetch**, from native_fetch_current_preserving_events' no-update conjunct. -/
theorem raw_fetch {rows : List ImageRow} {params : S1TTWParams} {x : NativeState} {translated final : ArmCertWalk.State}
    {acc : AccessDescriptor} {P : Prop}
    (raw : RawImageAt rows x.mem)
    (noUpd : NoUpdateRows {params with haft := hostHAFT x.regs} acc rows = true)
    (cond : RawImageAt rows (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState x)).mem →
      NoUpdateRows {params with haft := hostHAFT (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState x)).regs} acc rows = true →
      P ∧ translated.mem = (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState x)).mem)
    (finalMem : final.mem = translated.mem) : RawImageAt rows final.mem := by
  have h := (cond raw (by rw [haft_fetchPre]; exact noUpd)).2
  rw [finalMem, h]
  exact raw

/-- **RawImageAt across a class step** that writes only bytes separated from the table footprint
(memory tails export WritesOnly written / Separated (rowsFootprint rows).byte written; non-memory
classes and loads leave memory unchanged: written := fun _ => False). -/
theorem raw_writes {rows : List ImageRow} {written : Nat → Prop} {m m' : Mem}
    (raw : RawImageAt rows m)
    (wo : WritesOnly written (fun x => m[x]?) (fun x => m'[x]?))
    (sep : Separated (rowsFootprint rows).byte written) : RawImageAt rows m' := by
  intro row member i hi
  have hin : (rowsFootprint rows).byte (row.slot + i) :=
    ⟨row.slot, List.mem_map.2 ⟨row, member, rfl⟩, by omega, by simp [rowsFootprint]; omega⟩
  rw [show m'[row.slot + i]? = m[row.slot + i]? from wo _ (sep _ hin)]
  exact raw row member i hi

/-- Memory unchanged (fixed classes, loads). -/
theorem raw_mem_eq {rows : List ImageRow} {m m' : Mem} (raw : RawImageAt rows m) (h : m' = m) : RawImageAt rows m' :=
  h ▸ raw

#print axioms raw_writes
#print axioms noUpd_read
#print axioms raw_fetch
end HeapV2StepCerts.RawFetch
