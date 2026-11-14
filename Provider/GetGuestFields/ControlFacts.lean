import GetGuestComposition.Params
import Walk.S1Normality
import Walk.S1TCREnabled
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace GetGuestFields.ControlFacts
open S1Normality

def FrameResult {α : Type} (s : State) :
    EStateM.Result (Sail.Error exception) State α → Prop
  | .ok _ t => Frame s t
  | .error _ _ => False

def TCRResult (s : State) : EStateM.Result (Sail.Error exception) State Bool → Prop
  | .ok b t => Frame s t ∧ (b = true → s.regs.FeatureImpl[178] = true)
  | .error _ _ => False

theorem tcr2 (s : State) : TCRResult s (GetGuestTCR2.native s) := by
  observe_simp [TCRResult, Frame, GetGuestTCR2.native]
  intro h _ _
  exact h

theorem sctlr2 (s : State) : FrameResult s (GetGuestSCTLR2.native s) := by
  observe_simp [FrameResult, Frame, GetGuestSCTLR2.native]

theorem unknown (label : ChoiceLabel) (s : State) :
    FrameResult s (S1ParamsUnknown.native label s) := by
  observe_simp [FrameResult, Frame, S1ParamsUnknown.native]

#print axioms tcr2
#print axioms sctlr2
#print axioms unknown
theorem total_of_frame {α : Type} (p : SailM α) (s : State)
    (h : FrameResult s (p s)) : ∃ a t, p s = .ok a t ∧ Frame s t := by
  cases hr : p s with
  | error e t => simp only [hr, FrameResult] at h
  | ok a t => exact ⟨a, t, rfl, by simpa only [hr, FrameResult] using h⟩

theorem tcr2_total (s : State) :
    ∃ b t, GetGuestTCR2.native s = .ok b t ∧ Frame s t ∧
      (b = true → s.regs.FeatureImpl[178] = true) := by
  have h := tcr2 s
  cases hr : GetGuestTCR2.native s with
  | error e t => simp only [hr, TCRResult] at h
  | ok b t => exact ⟨b, t, rfl, by simpa only [hr, TCRResult] using h⟩
#print axioms tcr2_total
end GetGuestFields.ControlFacts

