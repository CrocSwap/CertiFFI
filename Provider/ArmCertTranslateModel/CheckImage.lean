import ArmCertTranslateModel.Image

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- A finite current-byte witness. `raw` is an initialization/checking witness;
    it is not frozen into the observation that later updates must preserve. -/
structure ImageRow where
  slot : Nat
  leaf : Bool
  raw : BitVec 64
  expected : S1DescriptorPIE.View 64

/-- All eight actual bytes, source observer and role-specific AF readiness are
    checked. This is an image check only; topology/permissions/attributes and
    current controls belong to the separate generalized structural contract. -/
def ImageRow.check (row : ImageRow) (pie ha hd : Bool) (mem : Mem) : Bool :=
  (List.range 8).all (fun i => decide (mem[row.slot + i]? = some (row.raw.extractLsb' (8 * i) 8))) &&
  decide (S1DescriptorPIE.view pie ha hd row.raw = row.expected) &&
  (!row.leaf || row.raw.getLsbD 10 || ha) && decide (row.slot % 8 = 0)

def checkImage (rows : List ImageRow) (pie ha hd : Bool) (mem : Mem) : Bool :=
  rows.all (fun row => row.check pie ha hd mem)

def rowsObserve (rows : List ImageRow) : RoleObservation :=
  fun slot leaf view => ∃ row ∈ rows, slot = row.slot ∧ leaf = row.leaf ∧ view = row.expected

def rowsFootprint (rows : List ImageRow) : Footprint :=
  ⟨rows.map ImageRow.slot, 8⟩

theorem ImageRow.check_sound (row : ImageRow) (pie ha hd : Bool) (mem : Mem)
    (h : row.check pie ha hd mem = true) :
    S1ByteMemory.DescAt mem row.slot row.raw ∧
      S1DescriptorPIE.view pie ha hd row.raw = row.expected ∧
      RoleReady ha row.leaf row.raw ∧ row.slot % 8 = 0 := by
  simp only [ImageRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hb, hv⟩, hr⟩, hal⟩ := h
  refine ⟨?_, hv, ?_, hal⟩
  · intro i hi
    have he := (List.all_eq_true.mp hb) i (List.mem_range.mpr hi)
    exact of_decide_eq_true he
  · intro hl
    simp only [hl, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hr
    exact hr

theorem checkImage_realizes (rows : List ImageRow) (pie ha hd : Bool) (mem : Mem)
    (h : checkImage rows pie ha hd mem = true) : ImageRealizes (rowsObserve rows) pie ha hd mem := by
  intro slot leaf view ⟨row, hrow, hslot, hleaf, hview⟩
  subst slot; subst leaf; subst view
  have hc := (List.all_eq_true.mp h) row hrow
  obtain ⟨hb, hv, hr, _⟩ := row.check_sound pie ha hd mem hc
  exact ⟨row.raw, hb, hv, hr⟩

theorem checkImage_aligned (rows : List ImageRow) (pie ha hd : Bool) (mem : Mem)
    (h : checkImage rows pie ha hd mem = true) : ImageAligned (rowsObserve rows) := by
  intro slot leaf view ⟨row, hrow, hslot, _, _⟩
  rw [hslot]
  exact (row.check_sound pie ha hd mem ((List.all_eq_true.mp h) row hrow)).2.2.2

theorem rows_covered (rows : List ImageRow) : ImageCovers (rowsObserve rows) (rowsFootprint rows) := by
  intro slot leaf view ⟨row, hrow, hslot, _, _⟩
  rw [hslot]
  exact List.mem_map.mpr ⟨row, hrow, rfl⟩

/-- A finite initialization checker establishes the source-byte image facts.
    It neither assumes nor concludes future translation success. -/
theorem checkImage_sound (rows : List ImageRow) (pie ha hd : Bool) (mem : Mem)
    (h : checkImage rows pie ha hd mem = true) :
    ImageRealizes (rowsObserve rows) pie ha hd mem ∧
      ImageAligned (rowsObserve rows) ∧ ImageCovers (rowsObserve rows) (rowsFootprint rows) :=
  ⟨checkImage_realizes rows pie ha hd mem h, checkImage_aligned rows pie ha hd mem h, rows_covered rows⟩

#print axioms checkImage_sound
end ArmCert.Translate.Model
