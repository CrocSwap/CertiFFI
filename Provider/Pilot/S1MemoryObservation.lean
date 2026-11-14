import Pilot.S1ByteMemory
import Pilot.S1DescriptorPIE
namespace S1MemoryObservation
open Sail S1ByteMemory

def Observed {α : Type} (observe : BitVec 64 → α) (m : Memory) (a : Nat) (v : α) : Prop :=
  ∃ d, DescAt m a d ∧ observe d = v

def Equivalent {α : Type} (observe : BitVec 64 → α) (m m' : Memory) : Prop :=
  ∀ a, a % 8 = 0 → ∀ v, Observed observe m a v ↔ Observed observe m' a v

theorem store_equivalent {α : Type} (observe : BitVec 64 → α)
    (m : Memory) (a : Nat) (old new : BitVec 64)
    (halign : a % 8 = 0) (hold : DescAt m a old) (hview : observe old = observe new) :
    Equivalent observe m (store m a new) := by
  intro b hb v
  by_cases hab : a = b
  · subst b
    constructor
    · rintro ⟨d, hd, hv⟩
      have heq := descriptor_unique m a d old hd hold
      subst d
      exact ⟨new, stored_descriptor _ _ _, hview.symm.trans hv⟩
    · rintro ⟨d, hd, hv⟩
      have heq := descriptor_unique (store m a new) a d new hd (stored_descriptor _ _ _)
      subst d
      exact ⟨old, hold, hview.trans hv⟩
  · constructor
    · rintro ⟨d, hd, hv⟩
      exact ⟨d, (other_descriptor_iff m a b new d halign hb hab).mpr hd, hv⟩
    · rintro ⟨d, hd, hv⟩
      exact ⟨d, (other_descriptor_iff m a b new d halign hb hab).mp hd, hv⟩

/- PIE uses stable selector bits plus the separate PIR/PIRE0 context. This
   theorem does not identify the legacy write hint with PIE permissions. -/
theorem hardware_equivalent (pie ha hd af dirty : Bool)
    (m : Memory) (a : Nat) (d : BitVec 64)
    (halign : a % 8 = 0) (hold : DescAt m a d)
    (hdirty : dirty = true → ha = true ∧ hd = true ∧
      (pie = false → d.getLsbD 51 = true)) :
    Equivalent (S1DescriptorPIE.view pie ha hd) m
      (store m a (S1Descriptor.hardwareUpdate af dirty d)) := by
  apply store_equivalent _ _ _ _ _ halign hold
  exact (S1DescriptorPIE.hardware_view pie ha hd af dirty d hdirty).symm

theorem satisfiable (a : Nat) (d : BitVec 64) : ∃ m : Memory, DescAt m a d :=
  ⟨store ({} : Memory) a d, stored_descriptor _ _ _⟩

#print axioms store_equivalent
#print axioms hardware_equivalent
#print axioms satisfiable
end S1MemoryObservation
