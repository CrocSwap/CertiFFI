import ArmCertTranslateModel.StoreHistory

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- An actual descriptor store overwrites eight PRESENT bytes. It preserves
    the native partial memory's domain even at the changed AF/dirty bytes.
    Values may change; no read/table separation or byte default is used. -/
theorem StoreStep.byte_presence {params : S1TTWParams} {footprint : Footprint}
    {operation : TableUpdate} {before after : Mem}
    (step : StoreStep params footprint operation before after) (address : Nat) :
    (after[address]?).isSome = (before[address]?).isSome := by
  have storedAt (atAddress : Nat) :
      after[atAddress]? = (S1ByteMemory.store before operation.slot
        (S2Endian.encode params.ee operation.after))[atAddress]? :=
    congrArg (fun memory : Mem => memory[atAddress]?) step.stored
  by_cases low : address < operation.slot
  · exact congrArg Option.isSome ((storedAt address).trans
      (S1ByteMemory.lookup_outside _ _ _ address (Or.inl low)))
  by_cases high : operation.slot + 8 ≤ address
  · exact congrArg Option.isSome ((storedAt address).trans
      (S1ByteMemory.lookup_outside _ _ _ address (Or.inr high)))
  obtain ⟨i, location⟩ := Nat.exists_eq_add_of_le (show operation.slot ≤ address by omega)
  have inside : i < 8 := by omega
  have newByte := (storedAt (operation.slot + i)).trans (S1ByteMemory.lookup_inside _ _ _ i inside)
  have afterSome : (after[operation.slot + i]?).isSome = true := congrArg Option.isSome newByte
  have beforeSome : (before[operation.slot + i]?).isSome = true :=
    congrArg Option.isSome (step.present i inside)
  have present := afterSome.trans beforeSome.symm
  simpa only [location] using present

/-- Derive native byte availability on the SAME actual final memory from a
    PAST ordered hardware-store history, including reads that alias tables. -/
theorem StoreHistory.byte_presence {params : S1TTWParams} {footprint : Footprint}
    {before after : Mem} {operations : List TableUpdate}
    (history : StoreHistory params footprint before operations after) (address : Nat) :
    (after[address]?).isSome = (before[address]?).isSome := by
  induction history with
  | nil => rfl
  | cons step tail ih => exact ih.trans (step.byte_presence address)

theorem StoreHistory.some_after {params : S1TTWParams} {footprint : Footprint}
    {before after : Mem} {operations : List TableUpdate}
    (history : StoreHistory params footprint before operations after) (address : Nat)
    (value : BitVec 8) (present : before[address]? = some value) :
    ∃ current : BitVec 8, after[address]? = some current := by
  have available := history.byte_presence address
  rw [present] at available
  cases actual : after[address]? with
  | none => simp only [actual, Option.isSome_none, Option.isSome_some, Bool.false_eq_true] at available
  | some current => exact ⟨current, rfl⟩

#print axioms StoreStep.byte_presence
#print axioms StoreHistory.byte_presence
#print axioms StoreHistory.some_after
end ArmCert.Translate.Model
