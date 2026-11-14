import NativeEntryBodyDispatch.RetWord
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.CruxCore
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace NativeEntryBodyDispatch.Ret
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 4 0) : BitVec 5) = 0#5 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h1 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 4 0) : BitVec 5) = 0#5 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h2 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 4 0) : BitVec 5) = 0#5 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h3 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 4 0) : BitVec 5) = 0#5 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h4 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 4 0) : BitVec 5) = 0#5 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h5 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 4 4) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h6 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 4 4) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h7 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 5 0) : BitVec 6) = 31#6) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h7b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 5 0) : BitVec 6) == 31#6) = false := by
  have := dispatch_h7 Rn
  simpa using this

theorem dispatch_h8 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 7 0) : BitVec 8) = 95#8) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h8b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 7 0) : BitVec 8) == 95#8) = false := by
  have := dispatch_h8 Rn
  simpa using this

theorem dispatch_h9 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 7 0) : BitVec 8) = 159#8) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h9b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 7 0) : BitVec 8) == 159#8) = false := by
  have := dispatch_h9 Rn
  simpa using this

theorem dispatch_h10 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 7 0) : BitVec 8) = 191#8) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h10b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 7 0) : BitVec 8) == 191#8) = false := by
  have := dispatch_h10 Rn
  simpa using this

theorem dispatch_h11 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 7 0) : BitVec 8) = 223#8) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h11b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 7 0) : BitVec 8) == 223#8) = false := by
  have := dispatch_h11 Rn
  simpa using this

theorem dispatch_h12 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 9 0) : BitVec 10) = 575#10) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h12b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 9 0) : BitVec 10) == 575#10) = false := by
  have := dispatch_h12 Rn
  simpa using this

theorem dispatch_h13 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 9 0) : BitVec 10) = 1023#10) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h13b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 9 0) : BitVec 10) == 1023#10) = false := by
  have := dispatch_h13 Rn
  simpa using this

theorem dispatch_h14 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 15 12) : BitVec 4) = 0#4 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h15 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 23 11) : BitVec 13) = 3040#13 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h16 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 23 11) : BitVec 13) = 3040#13 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h17 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 25 25) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h18 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 27 25) : BitVec 3) = 3#3 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h19 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 27 27) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h20 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 28 25) : BitVec 4) = 11#4 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h21 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 28 25) : BitVec 4) = 11#4 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h22 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 28 25) : BitVec 4) = 11#4 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h23 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 28 25) : BitVec 4) = 11#4 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h24 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 28 26) : BitVec 3) = 5#3 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h25 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 28 26) : BitVec 3) = 5#3 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h26 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 30 24) : BitVec 7) = 86#7 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h27 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 30 24) : BitVec 7) = 86#7 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h28 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 30 24) : BitVec 7) = 86#7 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h29 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 30 24) : BitVec 7) = 86#7 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h30 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 5) : BitVec 27) = 111679616#27) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h30b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 5) : BitVec 27) == 111679616#27) = false := by
  have := dispatch_h30 Rn
  simpa using this

theorem dispatch_h31 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 5) : BitVec 27) = 111679617#27) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h31b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 5) : BitVec 27) == 111679617#27) = false := by
  have := dispatch_h31 Rn
  simpa using this

theorem dispatch_h32 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 5) : BitVec 27) = 111745411#27) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h32b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 5) : BitVec 27) == 111745411#27) = false := by
  have := dispatch_h32 Rn
  simpa using this

theorem dispatch_h33 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 5) : BitVec 27) = 111745419#27) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h33b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 5) : BitVec 27) == 111745419#27) = false := by
  have := dispatch_h33 Rn
  simpa using this

theorem dispatch_h34 (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 8) : BitVec 24) = 13959972#24) := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h34b (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 8) : BitVec 24) == 13959972#24) = false := by
  have := dispatch_h34 Rn
  simpa using this

theorem dispatch_h35 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 10) : BitVec 22) = 3512256#22 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h36 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 10) : BitVec 22) = 3512256#22 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h37 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 10) : BitVec 22) = 3512256#22 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h38 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 10) : BitVec 22) = 3512256#22 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h39 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 11) : BitVec 21) = 1756128#21 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h40 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 11) : BitVec 21) = 1756128#21 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h41 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 12) : BitVec 20) = 878064#20 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h42 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 12) : BitVec 20) = 878064#20 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h43 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 19) : BitVec 13) = 6859#13 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h44 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 19) : BitVec 13) = 6859#13 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h45 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 19) : BitVec 13) = 6859#13 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h46 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 19) : BitVec 13) = 6859#13 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h47 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 20) : BitVec 12) = 3429#12 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h48 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 20) : BitVec 12) = 3429#12 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h49 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 20) : BitVec 12) = 3429#12 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h50 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 20) : BitVec 12) = 3429#12 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h51 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 21) : BitVec 11) = 1714#11 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h52 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 21) : BitVec 11) = 1714#11 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h53 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 21) : BitVec 11) = 1714#11 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h54 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 21) : BitVec 11) = 1714#11 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h55 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 21) : BitVec 11) = 1714#11 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h56 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 24) : BitVec 8) = 214#8 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h57 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 25) : BitVec 7) = 107#7 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h58 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 26) : BitVec 6) = 53#6 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h59 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 26) : BitVec 6) = 53#6 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h60 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h61 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Ret.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h62 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 0 2 = 0#2 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h63 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 0 4 = 0#4 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h64 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 0 5 = 0#5 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h65 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 5 5 = Rn := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    bv_field

theorem dispatch_h66 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 10 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h67 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 10 2 = 0#2 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h68 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 11 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h69 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 12 4 = 0#4 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h70 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 16 3 = 7#3 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h71 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 19 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h72 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 19 5 = 11#5 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h73 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 21 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h74 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 21 2 = 2#2 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h75 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 24 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h76 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) 31 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.Ret.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_hw77 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573563423#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw78 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573563455#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw79 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573563487#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw80 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573751839#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw81 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573751871#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw82 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573751903#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw83 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573751935#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw84 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573751967#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw85 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573751999#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw86 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573752031#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw87 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573752063#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw88 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573752351#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw89 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573752383#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw90 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573752415#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw91 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573752447#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw92 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573752479#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw93 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573752543#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw94 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573753119#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw95 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573756031#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw96 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3573756159#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw97 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3600745440#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw98 (Rn : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = 3602842592#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 21) h
    unfold NativeEntryBodyDispatch.Ret.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_acc10 (Rn : BitVec 5) :
    BitVec.access (NativeEntryBodyDispatch.Ret.word (107#7) (0#1) (0#1) (2#2) (496#9) (0#1) (0#1) Rn (0#5)) 10 = 0#1 := by
  simp only [BitVec.access]
  show BitVec.ofBool ((NativeEntryBodyDispatch.Ret.word (107#7) (0#1) (0#1) (2#2) (496#9) (0#1) (0#1) Rn (0#5)).getLsbD 10) = _
  unfold NativeEntryBodyDispatch.Ret.word
  simp only [BitVec.getLsbD_append]
  simp

theorem dispatch_bit10 (Rn : BitVec 5) :
    BitVec.setWidth 1 (BitVec.join1 [BitVec.access (NativeEntryBodyDispatch.Ret.word (107#7) (0#1) (0#1) (2#2) (496#9) (0#1) (0#1) Rn (0#5)) 10]) = 0#1 := by
  rw [dispatch_acc10]; decide

theorem dispatch_acc11 (Rn : BitVec 5) :
    BitVec.access (NativeEntryBodyDispatch.Ret.word (107#7) (0#1) (0#1) (2#2) (496#9) (0#1) (0#1) Rn (0#5)) 11 = 0#1 := by
  simp only [BitVec.access]
  show BitVec.ofBool ((NativeEntryBodyDispatch.Ret.word (107#7) (0#1) (0#1) (2#2) (496#9) (0#1) (0#1) Rn (0#5)).getLsbD 11) = _
  unfold NativeEntryBodyDispatch.Ret.word
  simp only [BitVec.getLsbD_append]
  simp

theorem dispatch_bit11 (Rn : BitVec 5) :
    BitVec.setWidth 1 (BitVec.join1 [BitVec.access (NativeEntryBodyDispatch.Ret.word (107#7) (0#1) (0#1) (2#2) (496#9) (0#1) (0#1) Rn (0#5)) 11]) = 0#1 := by
  rw [dispatch_acc11]; decide

theorem dispatch (pc : Int) (Rn : BitVec 5) :
    __DecodeA64 (real := real) pc (NativeEntryBodyDispatch.Ret.word 107#7 0#1 0#1 2#2 496#9 0#1 0#1 Rn 0#5) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 94))
      if c = true then (do writeReg Register.SEE 94; decode_ret_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 2#2 0#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_bit10, dispatch_bit11, bne_self_eq_false, Bool.false_or, Bool.or_false, dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h7b, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_hw77, dispatch_hw78, dispatch_hw79, dispatch_hw80, dispatch_hw81, dispatch_hw82, dispatch_hw83, dispatch_hw84, dispatch_hw85, dispatch_hw86, dispatch_hw87, dispatch_hw88, dispatch_hw89, dispatch_hw90, dispatch_hw91, dispatch_hw92, dispatch_hw93, dispatch_hw94, dispatch_hw95, dispatch_hw96, dispatch_hw97, dispatch_hw98, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_BranchExcSys
  simp (config := {decide := true}) only [dispatch_bit10, dispatch_bit11, bne_self_eq_false, Bool.false_or, Bool.or_false, dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h7b, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_hw77, dispatch_hw78, dispatch_hw79, dispatch_hw80, dispatch_hw81, dispatch_hw82, dispatch_hw83, dispatch_hw84, dispatch_hw85, dispatch_hw86, dispatch_hw87, dispatch_hw88, dispatch_hw89, dispatch_hw90, dispatch_hw91, dispatch_hw92, dispatch_hw93, dispatch_hw94, dispatch_hw95, dispatch_hw96, dispatch_hw97, dispatch_hw98, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch

/- Internal actual-state selector. The canonical prelude/owner frame must derive
this SEE bound; it is not a public entry premise or a discarded fallback. -/
theorem dispatch_at (pc : Int) (Rn : BitVec 5) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 94) :
    (__DecodeA64 (real := real) pc (NativeEntryBodyDispatch.Ret.selected Rn) : SailM Unit) s =
      (do writeReg Register.SEE 94; decode_ret_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 2#2 0#1 : SailM Unit) s := by
  rw [NativeEntryBodyDispatch.Ret.selected, dispatch real pc Rn]
  have h : (s.regs.bank_Int .SEE <b 94) = true := by simpa using see
  have read : ((do let x ← readReg Register.SEE; pure (x <b 94)) : SailM Bool) s =
      .ok (s.regs.bank_Int .SEE <b 94) s := by rfl
  rw [ArmBridge.CruxCore.bind_app, read]
  dsimp only []
  rw [if_pos h]

#print axioms dispatch_at
end NativeEntryBodyDispatch.Ret
