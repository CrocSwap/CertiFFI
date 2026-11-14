import Walk.S1StablePath
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1ResourcePath
abbrev Memory := S1ByteMemory.Memory

def view (wp : S1TTWParams) (d : BitVec 64) :=
  S1DescriptorPIE.view (wp.pie == 1#1) (wp.ha == 1#1) (wp.hd == 1#1) d

def nextSlot (va : BitVec 64) (level : Int) (d : BitVec 64) : FullAddress :=
  S2NextEntryFrame.address (level + 1) va
    {address := S1NextTable10Facts.base d, paspace := .PAS_NonSecure}

theorem next_of_shape (va d : BitVec 64) (current next : TTWState)
    (hs : S1NextTable10Facts.Shape current d next) :
    S1TablePrefix10.address next va = nextSlot va current.level d := by
  rcases hs with ⟨_, hl, hb, hp, _⟩
  have hfull : next.baseaddress =
      {paspace := .PAS_NonSecure, address := S1NextTable10Facts.base d} := by
    cases he : next.baseaddress with
    | mk pas addr =>
      simp only [he] at hb hp
      simp only [he, hb, hp]
  simp only [S1TablePrefix10.address, nextSlot, hl, hfull]

theorem next_stable (va : BitVec 64) (level : Int) (x y : BitVec 64)
    (h : S1Descriptor.stable x = S1Descriptor.stable y) :
    nextSlot va level x = nextSlot va level y := by
  unfold nextSlot
  rw [S1StablePath.table_base_eq x y h]

theorem decoded_eq_encode (ee : BitVec 1) (raw : BitVec 64) :
    S2FetchFrame.decoded ee raw = S2Endian.encode ee raw := by
  by_cases h : ee = 1#1 <;> simp [S2FetchFrame.decoded, S2Endian.encode, h]

theorem observed_stable (wp : S1TTWParams) (raw d : BitVec 64)
    (h : S1TableUpdate10.observe wp raw = view wp d) :
    S1Descriptor.stable (S2FetchFrame.decoded wp.ee raw) = S1Descriptor.stable d := by
  have hv := congrArg (fun v : S1DescriptorPIE.View 64 => v.stable) h
  simpa only [S1TableUpdate10.observe, S1HardwareSwap.observe, view,
    S1DescriptorPIE.view, decoded_eq_encode] using hv

/- A local, finite descriptor encoding/resource witness, not a source execution
   or successful-callee premise. Exact reference semantics and C14 are separate. -/
inductive Slots (wp : S1TTWParams) (va : BitVec 64) (mem : Memory) :
    Nat → Int → FullAddress → Prop where
  | terminal {level slot d}
      (bounds : 0 ≤ level ∧ level ≤ 3)
      (ram : S2TableRAM.OrdinaryRAM slot.address)
      (aligned : slot.address.toNat % 8 = 0)
      (observed : S1MemoryObservation.Observed (S1TableUpdate10.observe wp) mem
        slot.address.toNat (view wp d))
      (stop : S1DecodeFacts.classify d level ≠ .DescriptorType_Table) :
      Slots wp va mem 1 level slot
  | tableFault {level slot d}
      (bounds : 0 ≤ level ∧ level ≤ 3)
      (ram : S2TableRAM.OrdinaryRAM slot.address)
      (aligned : slot.address.toNat % 8 = 0)
      (observed : S1MemoryObservation.Observed (S1TableUpdate10.observe wp) mem
        slot.address.toNat (view wp d))
      (table : S1DecodeFacts.classify d level = .DescriptorType_Table)
      (range : S1TablePrefix10.outOfRange wp (nextSlot va level d) = true) :
      Slots wp va mem 1 level slot
  | table {n level slot d}
      (bounds : 0 ≤ level ∧ level ≤ 3)
      (ram : S2TableRAM.OrdinaryRAM slot.address)
      (aligned : slot.address.toNat % 8 = 0)
      (observed : S1MemoryObservation.Observed (S1TableUpdate10.observe wp) mem
        slot.address.toNat (view wp d))
      (table : S1DecodeFacts.classify d level = .DescriptorType_Table)
      (range : S1TablePrefix10.outOfRange wp (nextSlot va level d) = false)
      (rest : Slots wp va mem n (level + 1) (nextSlot va level d)) :
      Slots wp va mem (n + 1) level slot

inductive Branch (wp : S1TTWParams) (va : BitVec 64) (mem : Memory) :
    Nat → Int → BitVec 64 → Prop where
  | terminal {level d} (stop : S1DecodeFacts.classify d level ≠ .DescriptorType_Table) :
      Branch wp va mem 1 level d
  | tableFault {level d} (table : S1DecodeFacts.classify d level = .DescriptorType_Table)
      (range : S1TablePrefix10.outOfRange wp (nextSlot va level d) = true) :
      Branch wp va mem 1 level d
  | table {n level d} (table : S1DecodeFacts.classify d level = .DescriptorType_Table)
      (range : S1TablePrefix10.outOfRange wp (nextSlot va level d) = false)
      (rest : Slots wp va mem n (level + 1) (nextSlot va level d)) :
      Branch wp va mem (n + 1) level d

theorem unroll {wp : S1TTWParams} {va : BitVec 64} {mem : Memory}
    {n : Nat} {level : Int} {slot : FullAddress} (h : Slots wp va mem n level slot) :
    ∃ d : BitVec 64, (0 ≤ level ∧ level ≤ 3) ∧
      S2TableRAM.OrdinaryRAM slot.address ∧ slot.address.toNat % 8 = 0 ∧
      S1MemoryObservation.Observed (S1TableUpdate10.observe wp) mem slot.address.toNat (view wp d) ∧
      Branch wp va mem n level d := by
  cases h with
  | terminal bounds ram aligned observed stop => exact ⟨_, bounds, ram, aligned, observed, .terminal stop⟩
  | tableFault bounds ram aligned observed table range => exact ⟨_, bounds, ram, aligned, observed, .tableFault table range⟩
  | table bounds ram aligned observed table range rest => exact ⟨_, bounds, ram, aligned, observed, .table table range rest⟩

theorem length_bound {wp : S1TTWParams} {va : BitVec 64} {mem : Memory}
    {n : Nat} {level : Int} {slot : FullAddress} (h : Slots wp va mem n level slot) :
    0 < n ∧ n ≤ (4 - level).toNat := by
  induction h with
  | terminal bounds _ _ _ _ => omega
  | tableFault bounds _ _ _ _ _ => omega
  | table bounds _ _ _ _ _ _ ih => omega

theorem transport {wp : S1TTWParams} {va : BitVec 64} {mem mem' : Memory}
    {n : Nat} {level : Int} {slot : FullAddress} (h : Slots wp va mem n level slot)
    (heq : S1MemoryObservation.Equivalent (S1TableUpdate10.observe wp) mem mem') :
    Slots wp va mem' n level slot := by
  induction h with
  | terminal bounds ram aligned observed stop =>
    exact .terminal bounds ram aligned ((heq _ aligned _).mp observed) stop
  | tableFault bounds ram aligned observed table range =>
    exact .tableFault bounds ram aligned ((heq _ aligned _).mp observed) table range
  | table bounds ram aligned observed table range rest ih =>
    exact .table bounds ram aligned ((heq _ aligned _).mp observed) table range ih
#print axioms length_bound
#print axioms transport
end S1ResourcePath
