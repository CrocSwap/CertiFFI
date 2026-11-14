import ArmCertLoop.CopyExit
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.CopyNative
open ContractDraft

/-- Complete arbitrary-length memcpy loop and RET. The natural variant is the
actual full64 remaining counter. Body/exit callbacks are discharged by concrete
native instruction proofs; the exact instruction count is derived. -/
theorem finish (real : Type) [Sail.SailReal real] (c : Context) (entry : NativeState)
    (present : SourcePresent c.mapping c.s c.n entry) (i : Nat) (x : NativeState) (header : Header c entry i x) :
    ∃ fin, Uget.Chain.modelRun real (6 * (c.n - i) + 1) x = .ok () fin ∧
      Env c (Schedule.copySteps c.n) fin ∧ CopyPost c.mapping c.d c.s c.returnPC c.n entry fin := by
  suffices all : ∀ remaining i x, c.n - i = remaining → Header c entry i x →
      ∃ fin, Uget.Chain.modelRun real (6 * remaining + 1) x = .ok () fin ∧
        Env c (Schedule.copySteps c.n) fin ∧ CopyPost c.mapping c.d c.s c.returnPC c.n entry fin by
    exact all (c.n - i) i x rfl header
  intro remaining
  induction remaining using Nat.strongRecOn with
  | ind remaining ih =>
    intro i x rank header
    by_cases zero : remaining = 0
    · have last : i = c.n := by have bound := header.bound; omega
      subst i
      obtain ⟨fin, run, finalEnv, _, post⟩ := exit real c entry x header
      exact ⟨fin, by simpa only [zero, Nat.mul_zero, Nat.zero_add] using run, finalEnv, post⟩
    · have room : i < c.n := by have bound := header.bound; omega
      obtain ⟨byte, value⟩ := header_source c entry x i room present header
      obtain ⟨next, run, _, nextHeader⟩ := body real c entry x i room byte header value
      have lower : c.n - (i + 1) < remaining := by omega
      obtain ⟨fin, rest, finalEnv, post⟩ := ih (c.n - (i + 1)) lower (i + 1) next rfl nextHeader
      have cost : 6 + (6 * (c.n - (i + 1)) + 1) = 6 * remaining + 1 := by omega
      refine ⟨fin, ?_, finalEnv, post⟩
      rw [← cost]
      exact Aux.modelRun_append real 6 (6 * (c.n - (i + 1)) + 1) x next fin run rest

#print axioms finish
end ArmCertLoop.CopyNative
