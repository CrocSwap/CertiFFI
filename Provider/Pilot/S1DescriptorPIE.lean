import Pilot.S1Descriptor
namespace S1DescriptorPIE
open Sail
variable {w : Nat}

/- The PIE selector is contained in stable bits. Its permissions must be
   decoded with PIR/PIRE0; the legacy AP write hint is inapplicable in PIE. -/
structure View (w : Nat) where
  stable : BitVec w
  legacyWritable : Option Bool
  /-- PIE faults inspect bit 7 when hardware dirty updates are not enabled. -/
  restrictedDirty : Option Bool
  deriving DecidableEq

def view (pie ha hd : Bool) (d : BitVec w) : View w :=
  ⟨S1Descriptor.stable d,
    if pie then none else some (S1Descriptor.writable ha hd d),
    if pie && !(ha && hd) then some (d.getLsbD 7) else none⟩

theorem af_view (pie ha hd : Bool) (d : BitVec w) :
    view pie ha hd (S1Descriptor.setAF d) = view pie ha hd d := by
  simp only [view, S1Descriptor.setAF_stable, S1Descriptor.setAF_writable,
    S1Descriptor.setAF_other d 7 (by decide)]

theorem dirty_view (pie : Bool) (d : BitVec w)
    (h : pie = false → d.getLsbD 51 = true) :
    view pie true true (S1Descriptor.setDirty d) = view pie true true d := by
  cases pie
  · simp [view, S1Descriptor.setDirty_stable, S1Descriptor.setDirty_writable d (h rfl)]
  · simp [view, S1Descriptor.setDirty_stable]

theorem hardware_view (pie ha hd af dirty : Bool) (d : BitVec w)
    (h : dirty = true → ha = true ∧ hd = true ∧
      (pie = false → d.getLsbD 51 = true)) :
    view pie ha hd (S1Descriptor.hardwareUpdate af dirty d) = view pie ha hd d := by
  cases af <;> cases dirty
  · rfl
  · obtain ⟨rfl, rfl, hd⟩ := h rfl
    exact dirty_view pie d hd
  · exact af_view pie ha hd d
  · obtain ⟨rfl, rfl, hd⟩ := h rfl
    have hd' : pie = false → (S1Descriptor.setAF d).getLsbD 51 = true := by
      intro hp
      rw [S1Descriptor.setAF_other d 51 (by decide)]
      exact hd hp
    exact (dirty_view pie (S1Descriptor.setAF d) hd').trans (af_view pie true true d)

#print axioms af_view
#print axioms dirty_view
#print axioms hardware_view
end S1DescriptorPIE
