import GetGuestFields.Shape
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
namespace GetGuestFields.Dispatch
open S1Normality

/- The public Get draws an initial undefined record even when EL10 discards its
   value. Preserve that draw and occurrence history in the compositional native. -/
noncomputable def initialDraw : SailM S1TTWParams := do
  S1ParamsUnknown.native (← GetGuestReads.occurrence 1274)

noncomputable def native (_ss : SecurityState) (va : BitVec 64) : SailM S1TTWParams := do
  let _ ← initialDraw
  GetGuestComposition.native (AArch64_GetVARange va)

theorem complete (ss : SecurityState) (va : BitVec 64) :
    AArch64_GetS1TTWParams .Regime_EL10 ss va = native ss va := by
  simp only [AArch64_GetS1TTWParams, native, initialDraw,
    GetGuestReads.unknown_function_eq, GetGuestReads.occurrence_function_eq,
    GetGuestComposition.complete]

theorem prefix_normal : Normal initialDraw := by
  unfold initialDraw
  preserve_guest_fields

theorem normal (ss : SecurityState) (va : BitVec 64) :
    Normal (AArch64_GetS1TTWParams .Regime_EL10 ss va) := by
  rw [complete]
  unfold native
  apply bind_normal _ _ prefix_normal
  intro ignored
  exact GetGuestFields.Total.native _

def Granule (tcr : BitVec 64) : VARange → Prop
  | .VARange_LOWER => _get_TCR_EL1_Type_TG0 tcr = 0#2
  | .VARange_UPPER => _get_TCR_EL1_Type_TG1 tcr = 2#2

def txsz (tcr : BitVec 64) : VARange → BitVec 6
  | .VARange_LOWER => _get_TCR_EL1_Type_T0SZ tcr
  | .VARange_UPPER => _get_TCR_EL1_Type_T1SZ tcr

theorem range_shape (tcr tcr2 : BitVec 64) (s : State) (raw : Shape.Raw tcr tcr2 s)
    (vr : VARange) (htg : Granule tcr vr) :
    ∃ wp t, AArch64_S1TTWParamsEL10 vr s = .ok wp t ∧ Frame s t ∧
      active wp = Shape.expected (txsz tcr vr) (_get_TCR_EL1_Type_IPS tcr) := by
  cases vr with
  | VARange_LOWER => exact Shape.lower tcr tcr2 s raw htg
  | VARange_UPPER => exact Shape.upper tcr tcr2 s raw htg

theorem shape (tcr tcr2 : BitVec 64) (ss : SecurityState) (va : BitVec 64) (s : State)
    (raw : Shape.Raw tcr tcr2 s) (htg : Granule tcr (AArch64_GetVARange va)) :
    ∃ wp t, AArch64_GetS1TTWParams .Regime_EL10 ss va s = .ok wp t ∧ Frame s t ∧
      active wp = Shape.expected (txsz tcr (AArch64_GetVARange va))
        (_get_TCR_EL1_Type_IPS tcr) := by
  rcases prefix_normal s with ⟨ignored, t, hp, hf⟩
  rcases range_shape tcr tcr2 t (raw.frame hf) (AArch64_GetVARange va) htg with
    ⟨wp, u, hg, hfu, hv⟩
  refine ⟨wp, u, ?_, ⟨hfu.1.trans hf.1, hfu.2.1.trans hf.2.1, hfu.2.2.trans hf.2.2⟩, hv⟩
  rw [complete]
  unfold native
  rw [RegionFacts.bind_run hp, ← GetGuestComposition.complete]
  exact hg
#print axioms complete
#print axioms normal
#print axioms shape
end GetGuestFields.Dispatch
