import Init

/-! Finite table footprints and byte frames. No architecture or execution
assumption occurs here. Physical byte addresses are used so aliases cannot
escape the separation condition. -/
namespace ArmCert.Translate

abbrev Memory (Byte : Type u) := Nat → Option Byte

/-- Descriptor starts, each covering `width` physical bytes. -/
structure Footprint where
  slots : List Nat
  width : Nat
  deriving DecidableEq, Repr

def Footprint.byte (f : Footprint) (a : Nat) : Prop :=
  ∃ slot ∈ f.slots, slot ≤ a ∧ a < slot + f.width

/-- Pointwise equality only on the table footprint. Program data may change. -/
def AgreeOn (table : Nat → Prop) (before after : Memory Byte) : Prop :=
  ∀ a, table a → after a = before a

/-- A physical write frame: bytes outside `writes` keep their actual value. -/
def WritesOnly (writes : Nat → Prop) (before after : Memory Byte) : Prop :=
  ∀ a, ¬ writes a → after a = before a

/-- Physical table bytes never alias a program write byte. -/
def Separated (table writes : Nat → Prop) : Prop :=
  ∀ a, table a → ¬ writes a

theorem AgreeOn.refl (table : Nat → Prop) (m : Memory Byte) : AgreeOn table m m :=
  fun _ _ => rfl

theorem AgreeOn.symm (h : AgreeOn table before after) : AgreeOn table after before :=
  fun a ha => (h a ha).symm

theorem AgreeOn.trans (h : AgreeOn table first second) (h' : AgreeOn table second third) :
    AgreeOn table first third :=
  fun a ha => (h' a ha).trans (h a ha)

theorem WritesOnly.refl (writes : Nat → Prop) (m : Memory Byte) : WritesOnly writes m m :=
  fun _ _ => rfl

theorem WritesOnly.trans (h : WritesOnly writes first second)
    (h' : WritesOnly writes second third) : WritesOnly writes first third :=
  fun a ha => (h' a ha).trans (h a ha)

theorem WritesOnly.mono (h : WritesOnly small before after)
    (hsub : ∀ a, small a → large a) : WritesOnly large before after := by
  intro a ha
  exact h a (fun hs => ha (hsub a hs))

/-- The generic program-write preservation fact uses actual physical separation. -/
theorem table_unchanged (hframe : WritesOnly writes before after)
    (hsep : Separated table writes) : AgreeOn table before after :=
  fun a ha => hframe a (hsep a ha)

/-- A descriptor's whole byte window belongs to the footprint, including its leaf. -/
theorem Footprint.covers (f : Footprint) (slot : Nat) (hs : slot ∈ f.slots)
    (i : Fin f.width) : f.byte (slot + i.val) :=
  ⟨slot, hs, by omega, by have := i.isLt; omega⟩

/-- No assumptions about word byte order are needed for a byte-window frame. -/
def window (width : Nat) (m : Memory Byte) (slot : Nat) : Fin width → Option Byte :=
  fun i => m (slot + i.val)

theorem window_eq (f : Footprint) (slot : Nat) (hs : slot ∈ f.slots)
    (h : AgreeOn f.byte before after) :
    window f.width after slot = window f.width before slot := by
  funext i
  exact h _ (f.covers slot hs i)

/-- A view update inside tables followed by a program write still frames all
    bytes outside the union of their write regions. -/
theorem WritesOnly.comp_union (h : WritesOnly left first second)
    (h' : WritesOnly right second third) :
    WritesOnly (fun a => left a ∨ right a) first third := by
  intro a ha
  exact (h' a (fun hr => ha (Or.inr hr))).trans (h a (fun hl => ha (Or.inl hl)))

#print axioms table_unchanged
#print axioms window_eq
#print axioms WritesOnly.comp_union
end ArmCert.Translate
