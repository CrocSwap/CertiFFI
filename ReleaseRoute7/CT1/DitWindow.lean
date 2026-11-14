-- CT1 package, M1: generic DIT window. Proved once; consumers supply only the per-step DIT-preservation
-- conjunct their event steps already carry (fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT).
import CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
namespace CT1.DitWindow
open CertiFFI.Prog.Generic.ModelRunView ArmBridge.Draft

/-- Every step j ∈ [a, b) of the run from e preserves PSTATE.DIT. -/
def Preserves (real : Type) [Sail.SailReal real] (e : NativeState) (a b : Nat) : Prop :=
  ∀ j, a ≤ j → j < b → (stateAt real e (j + 1)).regs.PSTATE.DIT = (stateAt real e j).regs.PSTATE.DIT

/-- **wrap**: DIT = 1 at the window start and DIT-preserving steps give DIT = 1 on every state of [a, b]. -/
theorem wrap (real : Type) [Sail.SailReal real] (e : NativeState) (a b : Nat)
    (start : (stateAt real e a).regs.PSTATE.DIT = 1#1) (pres : Preserves real e a b) :
    ∀ j, a ≤ j → j ≤ b → (stateAt real e j).regs.PSTATE.DIT = 1#1 := by
  intro j lo hi
  induction j with
  | zero =>
    have : a = 0 := by omega
    subst this; exact start
  | succ n ih =>
    by_cases h : a ≤ n
    · rw [pres n h (by omega)]; exact ih h (by omega)
    · have : a = n + 1 := by omega
      subst this; exact start

/-- Caller-premise form (no DIT shim in the code, e.g. route 7): DIT = 1 at entry ⇒ DIT = 1 on the whole n-step run. -/
theorem of_entry (real : Type) [Sail.SailReal real] (e : NativeState) (n : Nat)
    (entry : e.regs.PSTATE.DIT = 1#1) (pres : Preserves real e 0 n) :
    ∀ j, j ≤ n → (stateAt real e j).regs.PSTATE.DIT = 1#1 :=
  fun j hj => wrap real e 0 n (by simpa [stateAt] using entry) pres j (Nat.zero_le j) hj

/-- Restore: DIT-preserving steps over [a, b] keep the DIT value of state a (used for the caller's DIT being returned
when the code itself does not touch DIT). -/
theorem keep (real : Type) [Sail.SailReal real] (e : NativeState) (a b : Nat) (pres : Preserves real e a b) :
    ∀ j, a ≤ j → j ≤ b → (stateAt real e j).regs.PSTATE.DIT = (stateAt real e a).regs.PSTATE.DIT := by
  intro j lo hi
  induction j with
  | zero => have : a = 0 := by omega
            subst this; rfl
  | succ n ih =>
    by_cases h : a ≤ n
    · rw [pres n h (by omega)]; exact ih h (by omega)
    · have : a = n + 1 := by omega
      subst this; rfl

end CT1.DitWindow
#print axioms CT1.DitWindow.wrap
#print axioms CT1.DitWindow.of_entry
#print axioms CT1.DitWindow.keep
