import ArmCertLoop.Bytes

open Sail Sail.ConcurrencyInterfaceV1
open ArmBridge.Draft Uget.Chain

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

namespace ArmCertLoop.Aux
open ArmCertLoop.Bytes

def memoryView (x : NativeState) : ByteView := fun pa => x.mem[pa]?

/-! A consumer-facing conditional engine: exact-byte snapshot mathematics is
joined to successful actual Sail segments. Control/body/exit hypotheses are
internal proof interfaces, never admissible public card premises. Native
instruction owners and generated block proofs must derive these hypotheses. -/

theorem forward_copy_of_blocks (real : Type) [Sail.SailReal real]
    (src dst : Nat → Nat) (initial : ByteView) (n bodyCost exitCost : Nat)
    (Control : Nat → Nat → NativeState → Prop) (Post : NativeState → Prop)
    (present : ∀ i, i < n → ∃ b, initial (src i) = some b)
    (distinctDst : ∀ i, i < n → ∀ j, j < i → dst j ≠ dst i)
    (safeSource : ∀ i, i < n → ∀ j, i < j → j < n → src j ≠ dst i)
    (positiveBody : 0 < bodyCost)
    (body : ∀ i elapsed x b, i < n →
      CopyPrefix src dst initial (memoryView x) n i → Control i elapsed x →
      memoryView x (src i) = some b →
      ∃ y, modelRun real bodyCost x = .ok () y ∧
        SingleWrite (memoryView x) (memoryView y) (dst i) b ∧
        Control (i + 1) (elapsed + bodyCost) y)
    (exit : ∀ elapsed x,
      CopyPrefix src dst initial (memoryView x) n n → Control n elapsed x →
      ∃ y, modelRun real exitCost x = .ok () y ∧ memoryView y = memoryView x ∧ Post y)
    (entry : NativeState)
    (initBytes : CopyPrefix src dst initial (memoryView entry) n 0)
    (initControl : Control 0 0 entry) :
    ∃ ticks fin, ticks ≤ bodyCost * n + exitCost ∧
      modelRun real ticks entry = .ok () fin ∧
      CopyPrefix src dst initial (memoryView fin) n n ∧ Post fin := by
  let H : Nat → Nat → NativeState → Prop := fun r elapsed x =>
    r ≤ n ∧ CopyPrefix src dst initial (memoryView x) n (n - r) ∧ Control (n - r) elapsed x
  let E : Nat → NativeState → Prop := fun _ x =>
    CopyPrefix src dst initial (memoryView x) n n ∧ Post x
  have progress : ∀ r elapsed x, H r elapsed x →
      (∃ ticks y, ticks ≤ exitCost ∧ modelRun real ticks x = .ok () y ∧ E (elapsed + ticks) y) ∨
      (∃ r' ticks y, r' < r ∧ 0 < ticks ∧ ticks ≤ bodyCost ∧
        modelRun real ticks x = .ok () y ∧ H r' (elapsed + ticks) y) := by
    intro r elapsed x hx
    obtain ⟨bound, inv, ctrl⟩ := hx
    by_cases zero : r = 0
    · subst r
      simp only [Nat.sub_zero] at inv ctrl
      obtain ⟨y, run, sameMemory, post⟩ := exit elapsed x inv ctrl
      left
      refine ⟨exitCost, y, Nat.le_refl _, run, ?_, post⟩
      rw [sameMemory]
      exact inv
    · have room : n - r < n := by omega
      obtain ⟨b, original⟩ := present (n - r) room
      have value : memoryView x (src (n - r)) = some b :=
        (inv.unread (n - r) (Nat.le_refl _) room).trans original
      obtain ⟨y, run, write, nextControl⟩ := body (n - r) elapsed x b room inv ctrl value
      have nextBytes := copyPrefix_succ inv room value write
        (distinctDst (n - r) room) (safeSource (n - r) room)
      have index : n - (r - 1) = n - r + 1 := by omega
      right
      refine ⟨r - 1, bodyCost, y, by omega, positiveBody, Nat.le_refl _, run, ?_, ?_, ?_⟩
      · omega
      · rw [index]; exact nextBytes
      · rw [index]; exact nextControl
  have init : H n 0 entry := by
    exact ⟨Nat.le_refl _, by simpa only [Nat.sub_self] using initBytes,
      by simpa only [Nat.sub_self] using initControl⟩
  obtain ⟨ticks, fin, bound, run, result⟩ :=
    cutpoint_terminates real H E bodyCost exitCost progress n 0 entry init
  exact ⟨ticks, fin, bound, run, result⟩

#print axioms forward_copy_of_blocks

theorem backward_copy_of_blocks (real : Type) [Sail.SailReal real]
    (src dst : Nat → Nat) (initial : ByteView) (n bodyCost exitCost : Nat)
    (Control : Nat → Nat → NativeState → Prop) (Post : NativeState → Prop)
    (present : ∀ i, i < n → ∃ b, initial (src i) = some b)
    (distinctDst : ∀ i, i < n → ∀ j, i < j → j < n → dst j ≠ dst i)
    (safeSource : ∀ i, i < n → ∀ j, j < i → src j ≠ dst i)
    (positiveBody : 0 < bodyCost)
    (body : ∀ r elapsed x b, 0 < r → r ≤ n →
      CopySuffix src dst initial (memoryView x) n r → Control r elapsed x →
      memoryView x (src (r - 1)) = some b →
      ∃ y, modelRun real bodyCost x = .ok () y ∧
        SingleWrite (memoryView x) (memoryView y) (dst (r - 1)) b ∧
        Control (r - 1) (elapsed + bodyCost) y)
    (exit : ∀ elapsed x,
      CopySuffix src dst initial (memoryView x) n 0 → Control 0 elapsed x →
      ∃ y, modelRun real exitCost x = .ok () y ∧ memoryView y = memoryView x ∧ Post y)
    (entry : NativeState)
    (initBytes : CopySuffix src dst initial (memoryView entry) n n)
    (initControl : Control n 0 entry) :
    ∃ ticks fin, ticks ≤ bodyCost * n + exitCost ∧
      modelRun real ticks entry = .ok () fin ∧
      CopySuffix src dst initial (memoryView fin) n 0 ∧ Post fin := by
  let H : Nat → Nat → NativeState → Prop := fun r elapsed x =>
    r ≤ n ∧ CopySuffix src dst initial (memoryView x) n r ∧ Control r elapsed x
  let E : Nat → NativeState → Prop := fun _ x =>
    CopySuffix src dst initial (memoryView x) n 0 ∧ Post x
  have progress : ∀ r elapsed x, H r elapsed x →
      (∃ ticks y, ticks ≤ exitCost ∧ modelRun real ticks x = .ok () y ∧ E (elapsed + ticks) y) ∨
      (∃ r' ticks y, r' < r ∧ 0 < ticks ∧ ticks ≤ bodyCost ∧
        modelRun real ticks x = .ok () y ∧ H r' (elapsed + ticks) y) := by
    intro r elapsed x hx
    obtain ⟨bound, inv, ctrl⟩ := hx
    by_cases zero : r = 0
    · subst r
      obtain ⟨y, run, sameMemory, post⟩ := exit elapsed x inv ctrl
      left
      refine ⟨exitCost, y, Nat.le_refl _, run, ?_, post⟩
      rw [sameMemory]; exact inv
    · have positive : 0 < r := by omega
      obtain ⟨b, original⟩ := present (r - 1) (by omega)
      have value : memoryView x (src (r - 1)) = some b :=
        (inv.unread (r - 1) (by omega)).trans original
      obtain ⟨y, run, write, nextControl⟩ := body r elapsed x b positive bound inv ctrl value
      have nextBytes := copySuffix_pred inv positive value write
        (fun j hj hn => distinctDst (r - 1) (by omega) j (by omega) hn)
        (safeSource (r - 1) (by omega))
      right
      exact ⟨r - 1, bodyCost, y, by omega, positiveBody, Nat.le_refl _, run,
        by omega, nextBytes, nextControl⟩
  have init : H n 0 entry := ⟨Nat.le_refl _, initBytes, initControl⟩
  obtain ⟨ticks, fin, bound, run, result⟩ :=
    cutpoint_terminates real H E bodyCost exitCost progress n 0 entry init
  exact ⟨ticks, fin, bound, run, result⟩

theorem fill_of_blocks (real : Type) [Sail.SailReal real]
    (dst : Nat → Nat) (initial : ByteView) (byte : BitVec 8) (n bodyCost exitCost : Nat)
    (Control : Nat → Nat → NativeState → Prop) (Post : NativeState → Prop)
    (distinctDst : ∀ i, i < n → ∀ j, j < i → dst j ≠ dst i)
    (positiveBody : 0 < bodyCost)
    (body : ∀ i elapsed x, i < n →
      FillPrefix dst initial (memoryView x) byte n i → Control i elapsed x →
      ∃ y, modelRun real bodyCost x = .ok () y ∧
        SingleWrite (memoryView x) (memoryView y) (dst i) byte ∧
        Control (i + 1) (elapsed + bodyCost) y)
    (exit : ∀ elapsed x,
      FillPrefix dst initial (memoryView x) byte n n → Control n elapsed x →
      ∃ y, modelRun real exitCost x = .ok () y ∧ memoryView y = memoryView x ∧ Post y)
    (entry : NativeState)
    (initBytes : FillPrefix dst initial (memoryView entry) byte n 0)
    (initControl : Control 0 0 entry) :
    ∃ ticks fin, ticks ≤ bodyCost * n + exitCost ∧
      modelRun real ticks entry = .ok () fin ∧
      FillPrefix dst initial (memoryView fin) byte n n ∧ Post fin := by
  let H : Nat → Nat → NativeState → Prop := fun r elapsed x =>
    r ≤ n ∧ FillPrefix dst initial (memoryView x) byte n (n - r) ∧ Control (n - r) elapsed x
  let E : Nat → NativeState → Prop := fun _ x =>
    FillPrefix dst initial (memoryView x) byte n n ∧ Post x
  have progress : ∀ r elapsed x, H r elapsed x →
      (∃ ticks y, ticks ≤ exitCost ∧ modelRun real ticks x = .ok () y ∧ E (elapsed + ticks) y) ∨
      (∃ r' ticks y, r' < r ∧ 0 < ticks ∧ ticks ≤ bodyCost ∧
        modelRun real ticks x = .ok () y ∧ H r' (elapsed + ticks) y) := by
    intro r elapsed x hx
    obtain ⟨bound, inv, ctrl⟩ := hx
    by_cases zero : r = 0
    · subst r
      simp only [Nat.sub_zero] at inv ctrl
      obtain ⟨y, run, sameMemory, post⟩ := exit elapsed x inv ctrl
      left
      refine ⟨exitCost, y, Nat.le_refl _, run, ?_, post⟩
      rw [sameMemory]; exact inv
    · have room : n - r < n := by omega
      obtain ⟨y, run, write, nextControl⟩ := body (n - r) elapsed x room inv ctrl
      have nextBytes := fillPrefix_succ inv room write (distinctDst (n - r) room)
      have index : n - (r - 1) = n - r + 1 := by omega
      right
      refine ⟨r - 1, bodyCost, y, by omega, positiveBody, Nat.le_refl _, run, ?_, ?_, ?_⟩
      · omega
      · rw [index]; exact nextBytes
      · rw [index]; exact nextControl
  have init : H n 0 entry := by
    exact ⟨Nat.le_refl _, by simpa only [Nat.sub_self] using initBytes,
      by simpa only [Nat.sub_self] using initControl⟩
  obtain ⟨ticks, fin, bound, run, result⟩ :=
    cutpoint_terminates real H E bodyCost exitCost progress n 0 entry init
  exact ⟨ticks, fin, bound, run, result⟩

#print axioms backward_copy_of_blocks
#print axioms fill_of_blocks

end ArmCertLoop.Aux
