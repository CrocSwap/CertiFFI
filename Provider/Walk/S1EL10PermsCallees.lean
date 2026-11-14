import Walk.S1EL2Enabled
import Walk.S1POEnabled10
import Walk.S1E0POEnabled10
import Walk.S1Normality
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S1EL10PermsCallees
open S1Normality
def Good (s : State) : EStateM.Result (Sail.Error exception) State Bool → Prop
  | .ok _ t => Frame s t
  | .error _ _ => False

theorem of_good (p : SailM Bool) (h : ∀ s, Good s (p s)) : Normal p := by
  intro s
  have hf := h s
  cases hr : p s with
  | error e t => simp only [hr, Good] at hf
  | ok b t => exact ⟨b, t, rfl, by simpa only [hr, Good] using hf⟩

theorem el2_frame (s : State) : Good s (S1EL2Enabled.native s) := by
  observe_simp [Good, Frame, S1EL2Enabled.native]
theorem poe_frame (s : State) : Good s (S1POEnabled10.native s) := by
  observe_simp [Good, Frame, S1POEnabled10.native]
theorem e0poe_frame (nv1 : BitVec 1) (s : State) :
    Good s (S1E0POEnabled10.native nv1 s) := by
  observe_simp [Good, Frame, S1E0POEnabled10.native]

theorem el2_normal : Normal (EL2Enabled ()) := by
  apply of_good
  intro s
  rw [S1EL2Enabled.complete]
  exact el2_frame s
theorem poe_normal : Normal (AArch64_S1POEnabled .Regime_EL10) := by
  apply of_good
  intro s
  rw [S1POEnabled10.complete]
  exact poe_frame s
theorem e0poe_normal (nv1 : BitVec 1) :
    Normal (AArch64_S1E0POEnabled .Regime_EL10 nv1) := by
  apply of_good
  intro s
  rw [S1E0POEnabled10.complete]
  exact e0poe_frame nv1 s

theorem int_normal (label : ChoiceLabel) : Normal (undefined_int_at label ()) := by
  intro s
  exact ⟨_, s, rfl, rfl, rfl, rfl⟩
#print axioms el2_normal
#print axioms poe_normal
#print axioms e0poe_normal
#print axioms int_normal
end S1EL10PermsCallees
