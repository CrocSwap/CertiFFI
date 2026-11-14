import NativeEntryBodyDispatch.LdrbWord
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.CruxCore
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace NativeEntryBodyDispatch.Ldrb
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 11 10) : BitVec 2) = 1#2 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h1 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 11 10) : BitVec 2) = 1#2 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h2 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 11 10) : BitVec 2) = 1#2 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h3 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 11 10) : BitVec 2) = 1#2 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h4 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 14 10) : BitVec 5) = 31#5) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h4b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 14 10) : BitVec 5) == 31#5) = false := by
  have := dispatch_h4 imm9 Rn Rt
  simpa using this

theorem dispatch_h5 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) = 0#6) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h5b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) == 0#6) = false := by
  have := dispatch_h5 imm9 Rn Rt
  simpa using this

theorem dispatch_h6 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) = 4#6) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h6b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) == 4#6) = false := by
  have := dispatch_h6 imm9 Rn Rt
  simpa using this

theorem dispatch_h7 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) = 8#6) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h7b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) == 8#6) = false := by
  have := dispatch_h7 imm9 Rn Rt
  simpa using this

theorem dispatch_h8 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) = 12#6) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h8b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) == 12#6) = false := by
  have := dispatch_h8 imm9 Rn Rt
  simpa using this

theorem dispatch_h9 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) = 16#6) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h9b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) == 16#6) = false := by
  have := dispatch_h9 imm9 Rn Rt
  simpa using this

theorem dispatch_h10 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) = 20#6) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h10b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) == 20#6) = false := by
  have := dispatch_h10 imm9 Rn Rt
  simpa using this

theorem dispatch_h11 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) = 24#6) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h11b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) == 24#6) = false := by
  have := dispatch_h11 imm9 Rn Rt
  simpa using this

theorem dispatch_h12 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) = 28#6) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h12b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) == 28#6) = false := by
  have := dispatch_h12 imm9 Rn Rt
  simpa using this

theorem dispatch_h13 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) = 31#6) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h13b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) == 31#6) = false := by
  have := dispatch_h13 imm9 Rn Rt
  simpa using this

theorem dispatch_h14 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) = 63#6) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h14b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 15 10) : BitVec 6) == 63#6) = false := by
  have := dispatch_h14 imm9 Rn Rt
  simpa using this

theorem dispatch_h15 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 21 21) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h16 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 21 21) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h17 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 22 21) : BitVec 2) = 2#2 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h18 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 22 21) : BitVec 2) = 2#2 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h19 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 22 22) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h20 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 22 22) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h21 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 25 25) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h22 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 27 25) : BitVec 3) = 4#3 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h23 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 27 27) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h24 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h25 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h26 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h27 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h28 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 28 26) : BitVec 3) = 6#3 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h29 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 28 26) : BitVec 3) = 6#3 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h30 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) = 137183#20) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h30b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) == 137183#20) = false := by
  have := dispatch_h30 imm9 Rn Rt
  simpa using this

theorem dispatch_h31 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) = 137215#20) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h31b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) == 137215#20) = false := by
  have := dispatch_h31 imm9 Rn Rt
  simpa using this

theorem dispatch_h32 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) = 141279#20) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h32b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) == 141279#20) = false := by
  have := dispatch_h32 imm9 Rn Rt
  simpa using this

theorem dispatch_h33 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) = 141311#20) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h33b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) == 141311#20) = false := by
  have := dispatch_h33 imm9 Rn Rt
  simpa using this

theorem dispatch_h34 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) = 145375#20) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h34b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) == 145375#20) = false := by
  have := dispatch_h34 imm9 Rn Rt
  simpa using this

theorem dispatch_h35 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) = 145407#20) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h35b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) == 145407#20) = false := by
  have := dispatch_h35 imm9 Rn Rt
  simpa using this

theorem dispatch_h36 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) = 213089#20) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h36b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) == 213089#20) = false := by
  have := dispatch_h36 imm9 Rn Rt
  simpa using this

theorem dispatch_h37 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) = 217185#20) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h37b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) == 217185#20) = false := by
  have := dispatch_h37 imm9 Rn Rt
  simpa using this

theorem dispatch_h38 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) = 417794#20) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h38b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) == 417794#20) = false := by
  have := dispatch_h38 imm9 Rn Rt
  simpa using this

theorem dispatch_h39 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) = 421890#20) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h39b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) == 421890#20) = false := by
  have := dispatch_h39 imm9 Rn Rt
  simpa using this

theorem dispatch_h40 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) = 929776#20) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h40b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 10) : BitVec 20) == 929776#20) = false := by
  have := dispatch_h40 imm9 Rn Rt
  simpa using this

theorem dispatch_h41 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) = 49152#18) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h41b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) == 49152#18) = false := by
  have := dispatch_h41 imm9 Rn Rt
  simpa using this

theorem dispatch_h42 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) = 49156#18) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h42b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) == 49156#18) = false := by
  have := dispatch_h42 imm9 Rn Rt
  simpa using this

theorem dispatch_h43 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) = 49160#18) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h43b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) == 49160#18) = false := by
  have := dispatch_h43 imm9 Rn Rt
  simpa using this

theorem dispatch_h44 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) = 50176#18) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h44b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) == 50176#18) = false := by
  have := dispatch_h44 imm9 Rn Rt
  simpa using this

theorem dispatch_h45 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) = 50180#18) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h45b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) == 50180#18) = false := by
  have := dispatch_h45 imm9 Rn Rt
  simpa using this

theorem dispatch_h46 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) = 50184#18) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h46b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) == 50184#18) = false := by
  have := dispatch_h46 imm9 Rn Rt
  simpa using this

theorem dispatch_h47 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) = 54284#18) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h47b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) == 54284#18) = false := by
  have := dispatch_h47 imm9 Rn Rt
  simpa using this

theorem dispatch_h48 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) = 54286#18) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h48b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) == 54286#18) = false := by
  have := dispatch_h48 imm9 Rn Rt
  simpa using this

theorem dispatch_h49 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) = 54796#18) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h49b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) == 54796#18) = false := by
  have := dispatch_h49 imm9 Rn Rt
  simpa using this

theorem dispatch_h50 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) = 54798#18) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h50b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 12) : BitVec 18) == 54798#18) = false := by
  have := dispatch_h50 imm9 Rn Rt
  simpa using this

theorem dispatch_h51 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 15) : BitVec 15) = 4350#15) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h51b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 15) : BitVec 15) == 4350#15) = false := by
  have := dispatch_h51 imm9 Rn Rt
  simpa using this

theorem dispatch_h52 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 15) : BitVec 15) = 4351#15) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h52b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 15) : BitVec 15) == 4351#15) = false := by
  have := dispatch_h52 imm9 Rn Rt
  simpa using this

theorem dispatch_h53 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) = 3072#14) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h53b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) == 3072#14) = false := by
  have := dispatch_h53 imm9 Rn Rt
  simpa using this

theorem dispatch_h54 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) = 3136#14) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h54b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) == 3136#14) = false := by
  have := dispatch_h54 imm9 Rn Rt
  simpa using this

theorem dispatch_h55 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) = 3328#14) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h55b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) == 3328#14) = false := by
  have := dispatch_h55 imm9 Rn Rt
  simpa using this

theorem dispatch_h56 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) = 3360#14) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h56b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) == 3360#14) = false := by
  have := dispatch_h56 imm9 Rn Rt
  simpa using this

theorem dispatch_h57 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) = 3392#14) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h57b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) == 3392#14) = false := by
  have := dispatch_h57 imm9 Rn Rt
  simpa using this

theorem dispatch_h58 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) = 3424#14) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h58b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 16) : BitVec 14) == 3424#14) = false := by
  have := dispatch_h58 imm9 Rn Rt
  simpa using this

theorem dispatch_h59 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h60 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h61 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h62 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h63 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h64 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h65 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h66 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h67 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h68 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h69 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h70 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h71 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h72 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h73 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h74 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h75 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h76 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h77 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h78 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h79 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h80 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 23) : BitVec 7) = 112#7 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h81 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 23) : BitVec 7) = 112#7 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h82 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h83 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h84 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h85 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h86 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h87 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h88 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h89 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h90 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h91 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h92 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h93 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h94 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h95 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h96 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h97 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 137183#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h97b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 137183#22) = false := by
  have := dispatch_h97 imm9 Rn Rt
  simpa using this

theorem dispatch_h98 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 137215#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h98b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 137215#22) = false := by
  have := dispatch_h98 imm9 Rn Rt
  simpa using this

theorem dispatch_h99 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 141279#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h99b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 141279#22) = false := by
  have := dispatch_h99 imm9 Rn Rt
  simpa using this

theorem dispatch_h100 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 141311#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h100b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 141311#22) = false := by
  have := dispatch_h100 imm9 Rn Rt
  simpa using this

theorem dispatch_h101 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 145375#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h101b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 145375#22) = false := by
  have := dispatch_h101 imm9 Rn Rt
  simpa using this

theorem dispatch_h102 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 145407#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h102b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 145407#22) = false := by
  have := dispatch_h102 imm9 Rn Rt
  simpa using this

theorem dispatch_h103 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 929776#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h103b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 929776#22) = false := by
  have := dispatch_h103 imm9 Rn Rt
  simpa using this

theorem dispatch_h104 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 1185759#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h104b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 1185759#22) = false := by
  have := dispatch_h104 imm9 Rn Rt
  simpa using this

theorem dispatch_h105 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 1185791#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h105b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 1185791#22) = false := by
  have := dispatch_h105 imm9 Rn Rt
  simpa using this

theorem dispatch_h106 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 1189855#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h106b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 1189855#22) = false := by
  have := dispatch_h106 imm9 Rn Rt
  simpa using this

theorem dispatch_h107 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 1189887#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h107b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 1189887#22) = false := by
  have := dispatch_h107 imm9 Rn Rt
  simpa using this

theorem dispatch_h108 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 1193951#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h108b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 1193951#22) = false := by
  have := dispatch_h108 imm9 Rn Rt
  simpa using this

theorem dispatch_h109 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 1193983#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h109b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 1193983#22) = false := by
  have := dispatch_h109 imm9 Rn Rt
  simpa using this

theorem dispatch_h110 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 1978352#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h110b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 1978352#22) = false := by
  have := dispatch_h110 imm9 Rn Rt
  simpa using this

theorem dispatch_h111 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 3557315#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h111b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 3557315#22) = false := by
  have := dispatch_h111 imm9 Rn Rt
  simpa using this

theorem dispatch_h112 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 3557319#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h112b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 3557319#22) = false := by
  have := dispatch_h112 imm9 Rn Rt
  simpa using this

theorem dispatch_h113 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 3569664#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h113b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 3569664#22) = false := by
  have := dispatch_h113 imm9 Rn Rt
  simpa using this

theorem dispatch_h114 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) = 4067316#22) := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h114b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 10) : BitVec 22) == 4067316#22) = false := by
  have := dispatch_h114 imm9 Rn Rt
  simpa using this

theorem dispatch_h115 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h116 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h117 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h118 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h119 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h120 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h121 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h122 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h123 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h124 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h125 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h126 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h127 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h128 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h129 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h130 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h131 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h132 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h133 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h134 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h135 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h136 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h137 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h138 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h139 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h140 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h141 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h142 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h143 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h144 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h145 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 31) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h146 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 31 31) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h147 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 0 5 = Rt := by
    unfold NativeEntryBodyDispatch.Ldrb.word BitVec.slice
    bv_field

theorem dispatch_h148 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 5 5 = Rn := by
    unfold NativeEntryBodyDispatch.Ldrb.word BitVec.slice
    bv_field

theorem dispatch_h149 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 10 2 = 1#2 := by
    unfold NativeEntryBodyDispatch.Ldrb.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h150 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 12 9 = imm9 := by
    unfold NativeEntryBodyDispatch.Ldrb.word BitVec.slice
    bv_field

theorem dispatch_h151 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 21 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h152 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 22 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h153 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 22 2 = 1#2 := by
    unfold NativeEntryBodyDispatch.Ldrb.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h154 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 23 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h155 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 30 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Ldrb.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h156 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ldrb.word 0#2 56#6 1#2 0#1 imm9 1#2 Rn Rt) 30 2 = 0#2 := by
    unfold NativeEntryBodyDispatch.Ldrb.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp


/- Internal actual-state selector for a SEGMENTED decode group (see generator note).
The canonical prelude/owner frame must derive this SEE bound. -/
theorem dispatch_at (pc : Int) (Rt : BitVec 5) (Rn : BitVec 5) (imm9 : BitVec 9) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 631) :
    (__DecodeA64 (real := real) pc (NativeEntryBodyDispatch.Ldrb.selected Rt Rn imm9) : SailM Unit) s =
      (do writeReg Register.SEE 631; decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2 : SailM Unit) s := by
  rw [NativeEntryBodyDispatch.Ldrb.selected]
  unfold __DecodeA64
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h4b, dispatch_h5, dispatch_h5b, dispatch_h6, dispatch_h6b, dispatch_h7, dispatch_h7b, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h56b, dispatch_h57, dispatch_h57b, dispatch_h58, dispatch_h58b, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h116, dispatch_h117, dispatch_h118, dispatch_h119, dispatch_h120, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, dispatch_h153, dispatch_h154, dispatch_h155, dispatch_h156, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h4b, dispatch_h5, dispatch_h5b, dispatch_h6, dispatch_h6b, dispatch_h7, dispatch_h7b, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h56b, dispatch_h57, dispatch_h57b, dispatch_h58, dispatch_h58b, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h116, dispatch_h117, dispatch_h118, dispatch_h119, dispatch_h120, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, dispatch_h153, dispatch_h154, dispatch_h155, dispatch_h156, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg0
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h4b, dispatch_h5, dispatch_h5b, dispatch_h6, dispatch_h6b, dispatch_h7, dispatch_h7b, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h56b, dispatch_h57, dispatch_h57b, dispatch_h58, dispatch_h58b, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h116, dispatch_h117, dispatch_h118, dispatch_h119, dispatch_h120, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, dispatch_h153, dispatch_h154, dispatch_h155, dispatch_h156, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg1
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h4b, dispatch_h5, dispatch_h5b, dispatch_h6, dispatch_h6b, dispatch_h7, dispatch_h7b, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h56b, dispatch_h57, dispatch_h57b, dispatch_h58, dispatch_h58b, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h116, dispatch_h117, dispatch_h118, dispatch_h119, dispatch_h120, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, dispatch_h153, dispatch_h154, dispatch_h155, dispatch_h156, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg2
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h4b, dispatch_h5, dispatch_h5b, dispatch_h6, dispatch_h6b, dispatch_h7, dispatch_h7b, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h56b, dispatch_h57, dispatch_h57b, dispatch_h58, dispatch_h58b, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h116, dispatch_h117, dispatch_h118, dispatch_h119, dispatch_h120, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, dispatch_h153, dispatch_h154, dispatch_h155, dispatch_h156, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg3
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h4b, dispatch_h5, dispatch_h5b, dispatch_h6, dispatch_h6b, dispatch_h7, dispatch_h7b, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h56b, dispatch_h57, dispatch_h57b, dispatch_h58, dispatch_h58b, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h116, dispatch_h117, dispatch_h118, dispatch_h119, dispatch_h120, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, dispatch_h153, dispatch_h154, dispatch_h155, dispatch_h156, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg4
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h4b, dispatch_h5, dispatch_h5b, dispatch_h6, dispatch_h6b, dispatch_h7, dispatch_h7b, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h56b, dispatch_h57, dispatch_h57b, dispatch_h58, dispatch_h58b, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h116, dispatch_h117, dispatch_h118, dispatch_h119, dispatch_h120, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, dispatch_h153, dispatch_h154, dispatch_h155, dispatch_h156, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg5
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h4b, dispatch_h5, dispatch_h5b, dispatch_h6, dispatch_h6b, dispatch_h7, dispatch_h7b, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h56b, dispatch_h57, dispatch_h57b, dispatch_h58, dispatch_h58b, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h116, dispatch_h117, dispatch_h118, dispatch_h119, dispatch_h120, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, dispatch_h153, dispatch_h154, dispatch_h155, dispatch_h156, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

  have h : (s.regs.bank_Int .SEE <b 631) = true := by simpa using see
  rw [ArmBridge.CruxCore.bind_app]
  have read : (readReg Register.SEE : SailM Int) s = .ok (s.regs.bank_Int .SEE) s := rfl
  rw [read]
  dsimp only []
  rw [if_pos h]
  simp only [bind_assoc, pure_bind, Bool.false_eq_true, ite_false, bind_pure_unit]

#print axioms dispatch_at
end NativeEntryBodyDispatch.Ldrb
