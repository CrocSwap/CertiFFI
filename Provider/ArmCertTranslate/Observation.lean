import ArmCertTranslate.Footprint

/-! Local descriptor observations are independent of a walker. An encoding can
be instantiated with the existing architecture's bytes and permission observer;
this module contains no descriptor decoding or translation algorithm. -/
namespace ArmCert.Translate

/-- The observer must include every raw-bit readiness condition needed by its
    consumer. In particular, an observer that hides AF does not alone establish
    AF=1 when hardware AF updates are disabled. -/
structure DescriptorEncoding (width : Nat) (Raw : Type u) (Byte : Type v) (View : Type w) where
  bytes : Raw → Fin width → Byte
  view : Raw → View

variable {width : Nat} {Raw : Type u} {Byte : Type v} {View : Type w}
variable {enc : DescriptorEncoding width Raw Byte View}

def EncodedAt (enc : DescriptorEncoding width Raw Byte View)
    (m : Memory Byte) (slot : Nat) (raw : Raw) : Prop :=
  window width m slot = fun i => some (enc.bytes raw i)

def Observed (enc : DescriptorEncoding width Raw Byte View)
    (m : Memory Byte) (slot : Nat) (view : View) : Prop :=
  ∃ raw, EncodedAt enc m slot raw ∧ enc.view raw = view

/-- Equality is required only at the finite table slots, not every aligned word
    of RAM: a program is free to change its non-table data. -/
def EquivalentOn (enc : DescriptorEncoding width Raw Byte View) (slots : List Nat)
    (before after : Memory Byte) : Prop :=
  ∀ slot ∈ slots, ∀ view, Observed enc before slot view ↔ Observed enc after slot view

/-- `observe` is a structural slot/view relation, shared by arbitrary many VAs.
    A single slot can consequently serve multiple paths without a special case. -/
def Realizes (enc : DescriptorEncoding width Raw Byte View)
    (observe : Nat → View → Prop) (m : Memory Byte) : Prop :=
  ∀ slot view, observe slot view → Observed enc m slot view

def Covered (observe : Nat → View → Prop) (slots : List Nat) : Prop :=
  ∀ slot view, observe slot view → slot ∈ slots

theorem EquivalentOn.refl (enc : DescriptorEncoding width Raw Byte View)
    (slots : List Nat) (m : Memory Byte) : EquivalentOn enc slots m m :=
  fun _ _ _ => Iff.rfl

theorem EquivalentOn.symm (h : EquivalentOn enc slots before after) :
    EquivalentOn enc slots after before := fun slot hs view => (h slot hs view).symm

theorem EquivalentOn.trans (h : EquivalentOn enc slots first second)
    (h' : EquivalentOn enc slots second third) : EquivalentOn enc slots first third :=
  fun slot hs view => (h slot hs view).trans (h' slot hs view)

theorem EquivalentOn.of_agree (enc : DescriptorEncoding width Raw Byte View)
    (f : Footprint) (hw : f.width = width) (h : AgreeOn f.byte before after) :
    EquivalentOn enc f.slots before after := by
  intro slot hs view
  have heq : window width after slot = window width before slot := by
    subst width
    exact window_eq f slot hs h
  simp only [Observed, EncodedAt, heq]

theorem Realizes.transport (h : Realizes enc observe before)
    (hc : Covered observe slots) (heq : EquivalentOn enc slots before after) :
    Realizes enc observe after :=
  fun slot view ho => (heq slot (hc slot view ho) view).mp (h slot view ho)

/-- Programs preserve the structural realization by writing outside tables. -/
theorem Realizes.program_write (h : Realizes enc observe before)
    (f : Footprint) (hw : f.width = width) (hc : Covered observe f.slots)
    (hf : WritesOnly writes before after) (hs : Separated f.byte writes) :
    Realizes enc observe after :=
  h.transport hc (EquivalentOn.of_agree enc f hw (table_unchanged hf hs))

/-- A descriptor change is described by actual before/after encoded bytes and
    equal observed views. The architecture adapter must derive this relation
    from actual AF/dirty writes; it is not an execution-success assumption. -/
def DescriptorChange (enc : DescriptorEncoding width Raw Byte View)
    (before after : Memory Byte) (slot : Nat) : Prop :=
  window width after slot = window width before slot ∨
    ∃ old new, EncodedAt enc before slot old ∧ EncodedAt enc after slot new ∧
      enc.view old = enc.view new

/-- A decoder's bytes determine its observed view. Instantiated architecture
    encodings supply this via descriptor byte uniqueness. -/
def ViewDetermined (enc : DescriptorEncoding width Raw Byte View) : Prop :=
  ∀ raw raw', enc.bytes raw = enc.bytes raw' → enc.view raw = enc.view raw'

theorem EncodedAt.view_unique (hdet : ViewDetermined enc)
    (h : EncodedAt enc m slot raw) (h' : EncodedAt enc m slot raw') :
    enc.view raw = enc.view raw' := by
  apply hdet
  funext i
  exact Option.some.inj (congrFun (h.symm.trans h') i)

theorem DescriptorChange.observed_iff (hdet : ViewDetermined enc)
    (h : DescriptorChange enc before after slot) (v : View) :
    Observed enc before slot v ↔ Observed enc after slot v := by
  rcases h with heq | ⟨old, new, ho, hn, hv⟩
  · simp only [Observed, EncodedAt, heq]
  · constructor
    · rintro ⟨raw, hr, hrv⟩
      exact ⟨new, hn, hv.symm.trans ((hr.view_unique hdet ho).symm.trans hrv)⟩
    · rintro ⟨raw, hr, hrv⟩
      exact ⟨old, ho, hv.trans ((hr.view_unique hdet hn).symm.trans hrv)⟩

theorem EquivalentOn.of_changes (hdet : ViewDetermined enc)
    (h : ∀ slot ∈ slots, DescriptorChange enc before after slot) :
    EquivalentOn enc slots before after :=
  fun slot hs view => (h slot hs).observed_iff hdet view

#print axioms Realizes.program_write
#print axioms DescriptorChange.observed_iff
#print axioms EquivalentOn.of_changes
end ArmCert.Translate
