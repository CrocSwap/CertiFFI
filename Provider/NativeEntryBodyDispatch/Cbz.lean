import NativeEntryBodyDispatch.CbzWord
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.CruxCore
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace NativeEntryBodyDispatch.Cbz
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 25 25) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h1 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 27 25) : BitVec 3) = 2#3 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h2 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 27 27) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h3 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 28 25) : BitVec 4) = 10#4 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h4 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 28 25) : BitVec 4) = 10#4 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h5 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 28 25) : BitVec 4) = 10#4 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h6 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 28 25) : BitVec 4) = 10#4 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h7 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 28 26) : BitVec 3) = 5#3 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h8 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 28 26) : BitVec 3) = 5#3 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h9 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 30 24) : BitVec 7) = 52#7 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h10 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 30 24) : BitVec 7) = 52#7 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h11 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 30 24) : BitVec 7) = 52#7 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h12 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 30 24) : BitVec 7) = 52#7 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h13 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 5) : BitVec 27) = 111679616#27) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 19) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h13b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 5) : BitVec 27) == 111679616#27) = false := by
  have := dispatch_h13 imm19 Rt
  simpa using this

theorem dispatch_h14 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 5) : BitVec 27) = 111679617#27) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 19) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h14b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 5) : BitVec 27) == 111679617#27) = false := by
  have := dispatch_h14 imm19 Rt
  simpa using this

theorem dispatch_h15 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 5) : BitVec 27) = 111745411#27) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 19) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h15b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 5) : BitVec 27) == 111745411#27) = false := by
  have := dispatch_h15 imm19 Rt
  simpa using this

theorem dispatch_h16 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 5) : BitVec 27) = 111745419#27) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 19) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h16b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 5) : BitVec 27) == 111745419#27) = false := by
  have := dispatch_h16 imm19 Rt
  simpa using this

theorem dispatch_h17 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 8) : BitVec 24) = 13959972#24) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 16) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h17b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 8) : BitVec 24) == 13959972#24) = false := by
  have := dispatch_h17 imm19 Rt
  simpa using this

theorem dispatch_h18 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 10) : BitVec 22) = 3489992#22) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h18b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 10) : BitVec 22) == 3489992#22) = false := by
  have := dispatch_h18 imm19 Rt
  simpa using this

theorem dispatch_h19 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 10) : BitVec 22) = 3508160#22) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 15) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h19b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 10) : BitVec 22) == 3508160#22) = false := by
  have := dispatch_h19 imm19 Rt
  simpa using this

theorem dispatch_h20 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 10) : BitVec 22) = 3510208#22) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 15) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h20b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 10) : BitVec 22) == 3510208#22) = false := by
  have := dispatch_h20 imm19 Rt
  simpa using this

theorem dispatch_h21 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 10) : BitVec 22) = 3512256#22) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 15) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h21b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 10) : BitVec 22) == 3512256#22) = false := by
  have := dispatch_h21 imm19 Rt
  simpa using this

theorem dispatch_h22 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 11) : BitVec 21) = 1756129#21) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h22b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 11) : BitVec 21) == 1756129#21) = false := by
  have := dispatch_h22 imm19 Rt
  simpa using this

theorem dispatch_h23 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 11) : BitVec 21) = 1758177#21) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h23b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 11) : BitVec 21) == 1758177#21) = false := by
  have := dispatch_h23 imm19 Rt
  simpa using this

theorem dispatch_h24 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 12) : BitVec 20) = 872498#20) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h24b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 12) : BitVec 20) == 872498#20) = false := by
  have := dispatch_h24 imm19 Rt
  simpa using this

theorem dispatch_h25 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 12) : BitVec 20) = 872499#20) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h25b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 12) : BitVec 20) == 872499#20) = false := by
  have := dispatch_h25 imm19 Rt
  simpa using this

theorem dispatch_h26 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 19) : BitVec 13) = 6816#13) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h26b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 19) : BitVec 13) == 6816#13) = false := by
  have := dispatch_h26 imm19 Rt
  simpa using this

theorem dispatch_h27 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 19) : BitVec 13) = 6817#13) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h27b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 19) : BitVec 13) == 6817#13) = false := by
  have := dispatch_h27 imm19 Rt
  simpa using this

theorem dispatch_h28 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 19) : BitVec 13) = 6821#13) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h28b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 19) : BitVec 13) == 6821#13) = false := by
  have := dispatch_h28 imm19 Rt
  simpa using this

theorem dispatch_h29 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 19) : BitVec 13) = 6825#13) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h29b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 19) : BitVec 13) == 6825#13) = false := by
  have := dispatch_h29 imm19 Rt
  simpa using this

theorem dispatch_h30 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 20) : BitVec 12) = 3409#12) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h30b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 20) : BitVec 12) == 3409#12) = false := by
  have := dispatch_h30 imm19 Rt
  simpa using this

theorem dispatch_h31 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 20) : BitVec 12) = 3411#12) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h31b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 20) : BitVec 12) == 3411#12) = false := by
  have := dispatch_h31 imm19 Rt
  simpa using this

theorem dispatch_h32 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 20) : BitVec 12) = 3413#12) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h32b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 20) : BitVec 12) == 3413#12) = false := by
  have := dispatch_h32 imm19 Rt
  simpa using this

theorem dispatch_h33 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 20) : BitVec 12) = 3415#12) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h33b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 20) : BitVec 12) == 3415#12) = false := by
  have := dispatch_h33 imm19 Rt
  simpa using this

theorem dispatch_h34 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 21) : BitVec 11) = 1696#11) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h34b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 21) : BitVec 11) == 1696#11) = false := by
  have := dispatch_h34 imm19 Rt
  simpa using this

theorem dispatch_h35 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 21) : BitVec 11) = 1697#11) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h35b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 21) : BitVec 11) == 1697#11) = false := by
  have := dispatch_h35 imm19 Rt
  simpa using this

theorem dispatch_h36 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 21) : BitVec 11) = 1698#11) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h36b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 21) : BitVec 11) == 1698#11) = false := by
  have := dispatch_h36 imm19 Rt
  simpa using this

theorem dispatch_h37 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 21) : BitVec 11) = 1699#11) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h37b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 21) : BitVec 11) == 1699#11) = false := by
  have := dispatch_h37 imm19 Rt
  simpa using this

theorem dispatch_h38 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 21) : BitVec 11) = 1701#11) := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h38b (imm19 : BitVec 19) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 21) : BitVec 11) == 1701#11) = false := by
  have := dispatch_h38 imm19 Rt
  simpa using this

theorem dispatch_h39 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 24) : BitVec 8) = 180#8 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h40 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 25) : BitVec 7) = 90#7 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h41 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 26) : BitVec 6) = 45#6 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h42 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 26) : BitVec 6) = 45#6 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h43 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h44 (imm19 : BitVec 19) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Cbz.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h45 (imm19 : BitVec 19) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 0 5 = Rt := by
    unfold NativeEntryBodyDispatch.Cbz.word BitVec.slice
    bv_field

theorem dispatch_h46 (imm19 : BitVec 19) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 5 19 = imm19 := by
    unfold NativeEntryBodyDispatch.Cbz.word BitVec.slice
    bv_field

theorem dispatch_h47 (imm19 : BitVec 19) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 24 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Cbz.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h48 (imm19 : BitVec 19) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) 31 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.Cbz.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_hw49 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573563423#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw50 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573563455#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw51 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573563487#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw52 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573751839#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw53 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573751871#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw54 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573751903#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw55 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573751935#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw56 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573751967#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw57 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573751999#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw58 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573752031#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw59 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573752063#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw60 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573752351#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw61 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573752383#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw62 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573752415#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw63 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573752447#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw64 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573752479#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw65 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573752543#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw66 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573753119#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw67 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573756031#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw68 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3573756159#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw69 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3600745440#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw70 (imm19 : BitVec 19) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = 3602842592#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Cbz.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch (pc : Int) (imm19 : BitVec 19) (Rt : BitVec 5) :
    __DecodeA64 (real := real) pc (NativeEntryBodyDispatch.Cbz.word 1#1 26#6 0#1 imm19 Rt) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 118))
      if c = true then (do writeReg Register.SEE 118; decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_hw49, dispatch_hw50, dispatch_hw51, dispatch_hw52, dispatch_hw53, dispatch_hw54, dispatch_hw55, dispatch_hw56, dispatch_hw57, dispatch_hw58, dispatch_hw59, dispatch_hw60, dispatch_hw61, dispatch_hw62, dispatch_hw63, dispatch_hw64, dispatch_hw65, dispatch_hw66, dispatch_hw67, dispatch_hw68, dispatch_hw69, dispatch_hw70, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_BranchExcSys
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_hw49, dispatch_hw50, dispatch_hw51, dispatch_hw52, dispatch_hw53, dispatch_hw54, dispatch_hw55, dispatch_hw56, dispatch_hw57, dispatch_hw58, dispatch_hw59, dispatch_hw60, dispatch_hw61, dispatch_hw62, dispatch_hw63, dispatch_hw64, dispatch_hw65, dispatch_hw66, dispatch_hw67, dispatch_hw68, dispatch_hw69, dispatch_hw70, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch

/- Internal actual-state selector. The canonical prelude/owner frame must derive
this SEE bound; it is not a public entry premise or a discarded fallback. -/
theorem dispatch_at (pc : Int) (Rt : BitVec 5) (imm19 : BitVec 19) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 118) :
    (__DecodeA64 (real := real) pc (NativeEntryBodyDispatch.Cbz.selected Rt imm19) : SailM Unit) s =
      (do writeReg Register.SEE 118; decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 1#1 : SailM Unit) s := by
  rw [NativeEntryBodyDispatch.Cbz.selected, dispatch real pc imm19 Rt]
  have h : (s.regs.bank_Int .SEE <b 118) = true := by simpa using see
  have read : ((do let x ← readReg Register.SEE; pure (x <b 118)) : SailM Bool) s =
      .ok (s.regs.bank_Int .SEE <b 118) s := by rfl
  rw [ArmBridge.CruxCore.bind_app, read]
  dsimp only []
  rw [if_pos h]

#print axioms dispatch_at
end NativeEntryBodyDispatch.Cbz
