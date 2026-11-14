import Walk.S1StageOA
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1WalkChecks
open S1Normality

def Good {α : Type} (s : State) : EStateM.Result (Sail.Error exception) State α → Prop
  | .ok _ t => Frame s t
  | .error _ _ => False

theorem of_good {α : Type} (p : SailM α) (h : ∀ s, Good s (p s)) : Normal p := by
  intro s
  have hf := h s
  cases hr : p s with
  | error e t => simp only [hr, Good] at hf
  | ok a t => exact ⟨a, t, rfl, by simpa only [hr, Good] using hf⟩

/- These are exact FINAL-model implementation-defined keys, not hardware
   feature-absence claims and not arbitrary unrecognized-key normality. -/
theorem impdef_contiguous :
    __IMPDEF_boolean "Translation fault on misprogrammed contiguous bit" =
      (pure false : SailM Bool) := rfl
theorem impdef_nt :
    __IMPDEF_boolean "BBM level 1 or 2 support nT bit causes Translation Fault" =
      (pure true : SailM Bool) := rfl
theorem impdef_af :
    __IMPDEF_boolean "Generate access flag fault on IC/DC operations" =
      (pure true : SailM Bool) := rfl

theorem contiguous_size (level : Int) (hLevel : 1 ≤ level ∧ level ≤ 3) (s : State) :
    ContiguousSize 0#1 .TGx_4KB level s = .ok 4 s := by
  have hc : level = 1 ∨ level = 2 ∨ level = 3 := by omega
  rcases hc with rfl | rfl | rfl <;>
    simp [ContiguousSize, ArmFull.assert, PreSail.assert, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]

theorem contiguous_normal (txsz : BitVec 6) (level : Int) (hLevel : 1 ≤ level ∧ level ≤ 3) :
    Normal (AArch64_ContiguousBitFaults 0#1 txsz .TGx_4KB level) := by
  unfold AArch64_ContiguousBitFaults
  apply bind_normal
  · intro s
    exact ⟨4, s, contiguous_size level hLevel s, rfl, rfl, rfl⟩
  · intro n
    apply ite_normal
    · intro; rw [impdef_contiguous]; exact pure_normal false
    · intro; exact pure_normal false

def amec (wp : S1TTWParams) (pas : PASpace) (regime : Regime) (d : BitVec 64) : Bool :=
  (((wp.emec +++ wp.amec) == 0b10#2) && ((regime == .Regime_EL2) || (regime == .Regime_EL20)) &&
    (pas == .PAS_Realm)) && (S1DecodeFacts.bit d 63 == 1#1)

theorem amec_normal (wp : S1TTWParams) (pas : PASpace) (regime : Regime) (d : BitVec 64)
    (hD128 : wp.d128 = 0#1) : Normal (AArch64_S1AMECFault wp pas regime d) := by
  intro s
  refine ⟨amec wp pas regime d, s, ?_, rfl, rfl, rfl⟩
  simp [AArch64_S1AMECFault, amec, S1DecodeFacts.bit, hD128, ArmFull.assert, PreSail.assert, Bind.bind, Pure.pure,
    EStateM.bind, EStateM.pure]

#print axioms impdef_contiguous
#print axioms contiguous_normal
#print axioms amec_normal
end S1WalkChecks
