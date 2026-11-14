import Walk.S1LogicalDescriptor
import Pilot.S1DescriptorPIE
open Sail ArmFull
namespace S1LogicalReference

/- Logical entry addresses can be IPAs while physical slots are PAs. VM0
   uses the identity reader; VM1 must supply its independent S2 encoding. -/
abbrev Observation := Nat → FullAddress → S1DescriptorPIE.View 64 → Prop

def entryIndex (va : BitVec 64) (level bits : Nat) : Nat :=
  va.toNat / 2 ^ (12 + 9 * (3 - level)) % 2 ^ bits

def entryAddress (base : BitVec 48) (va : BitVec 64) (level bits : Nat) : Nat :=
  base.toNat + 8 * entryIndex va level bits

def childBase (view : S1DescriptorPIE.View 64) : BitVec 48 :=
  (view.stable.extractLsb' 12 36).setWidth 48 <<< 12

def rootBits (start inputBits : Nat) : Nat := inputBits - (12 + 9 * (3 - start))

structure Layout where
  start : Nat
  inputBits : Nat
  root : BitVec 48
  deriving DecidableEq, BEq, Repr, Inhabited

inductive PathEnd where
  | translationFault (level : Nat)
  | addressSizeFault (level : Nat)
  | leaf (level logicalSlot : Nat) (physicalSlot : FullAddress) (view : S1DescriptorPIE.View 64)

/- Presence/topology certificate only: no raw-walk success or source-map
   agreement premise. Missing observations cannot construct a translation
   fault. Raw AF/descriptor bytes remain inputs to the richer interpreter. -/
inductive Path (observe : Observation) (paBits : Nat) (va : BitVec 64) :
    Nat → Nat → BitVec 48 → PathEnd → Prop where
  | invalid (level bits : Nat) (base : BitVec 48) (physical : FullAddress)
      (view : S1DescriptorPIE.View 64) (hl : level ≤ 3)
      (aligned : entryAddress base va level bits % 8 = 0)
      (present : observe (entryAddress base va level bits) physical view)
      (kind : descriptorKind level view.stable = .ok .invalid) :
      Path observe paBits va level bits base (.translationFault level)
  | leaf (level bits : Nat) (base : BitVec 48) (physical : FullAddress)
      (view : S1DescriptorPIE.View 64) (hl : level ≤ 3)
      (aligned : entryAddress base va level bits % 8 = 0)
      (present : observe (entryAddress base va level bits) physical view)
      (kind : descriptorKind level view.stable = .ok .leaf) :
      Path observe paBits va level bits base
        (.leaf level (entryAddress base va level bits) physical view)
  | range (level bits : Nat) (base : BitVec 48) (physical : FullAddress)
      (view : S1DescriptorPIE.View 64) (hl : level < 3)
      (aligned : entryAddress base va level bits % 8 = 0)
      (present : observe (entryAddress base va level bits) physical view)
      (kind : descriptorKind level view.stable = .ok .table)
      (outOfRange : 2 ^ paBits ≤ entryAddress (childBase view) va (level + 1) 9) :
      Path observe paBits va level bits base (.addressSizeFault level)
  | table (level bits : Nat) (base : BitVec 48) (physical : FullAddress)
      (view : S1DescriptorPIE.View 64) (result : PathEnd) (hl : level < 3)
      (aligned : entryAddress base va level bits % 8 = 0)
      (present : observe (entryAddress base va level bits) physical view)
      (kind : descriptorKind level view.stable = .ok .table)
      (inRange : entryAddress (childBase view) va (level + 1) 9 < 2 ^ paBits)
      (next : Path observe paBits va (level + 1) 9 (childBase view) result) :
      Path observe paBits va level bits base result

def Available (observe : Observation) (ram : FullAddress → Prop) : Prop :=
  ∀ logical physical view, observe logical physical view →
    logical % 8 = 0 ∧ physical.address.toNat % 8 = 0 ∧ ram physical

def byte (ee : Bool) (d : BitVec 64) (i : Nat) : BitVec 8 :=
  d.extractLsb' (8 * (if ee then 7 - i else i)) 8

def BytesAt (ee : Bool) (mem : Nat → Option (BitVec 8)) (physical : FullAddress)
    (d : BitVec 64) : Prop :=
  ∀ i < 8, mem (physical.address.toNat + i) = some (byte ee d i)

def Realizes (observe : Observation) (ee : Bool) (pie ha hd : Bool)
    (mem : Nat → Option (BitVec 8)) : Prop :=
  ∀ logical physical view, observe logical physical view →
    ∃ d, BytesAt ee mem physical d ∧ S1DescriptorPIE.view pie ha hd d = view

def Covers (observe : Observation) (tableBytes : Nat → Prop) : Prop :=
  ∀ logical physical view, observe logical physical view →
    ∀ i < 8, tableBytes (physical.address.toNat + i)

def PhysicalObserved (ee pie ha hd : Bool) (mem : Nat → Option (BitVec 8))
    (physical : FullAddress) (view : S1DescriptorPIE.View 64) : Prop :=
  ∃ d, BytesAt ee mem physical d ∧ S1DescriptorPIE.view pie ha hd d = view

def MemoryEquivalent (ee pie ha hd : Bool) (before after : Nat → Option (BitVec 8)) : Prop :=
  ∀ physical, physical.address.toNat % 8 = 0 → ∀ view,
    PhysicalObserved ee pie ha hd before physical view ↔ PhysicalObserved ee pie ha hd after physical view

theorem realizes_transport (observe : Observation) (ee pie ha hd : Bool)
    (before after : Nat → Option (BitVec 8)) (ram : FullAddress → Prop)
    (available : Available observe ram) (realizes : Realizes observe ee pie ha hd before)
    (he : MemoryEquivalent ee pie ha hd before after) : Realizes observe ee pie ha hd after := by
  intro logical physical view hp
  exact (he physical (available logical physical view hp).2.1 view).mp (realizes logical physical view hp)
#print axioms realizes_transport
end S1LogicalReference

