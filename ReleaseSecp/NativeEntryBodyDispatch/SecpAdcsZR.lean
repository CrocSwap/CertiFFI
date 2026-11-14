import NativeEntryBodyDispatch.SecpAdcsZRWord
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.CruxCore
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace NativeEntryBodyDispatch.SecpAdcsZR
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 4 0) : BitVec 5) = 31#5 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h1 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 4 4) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h2 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 11 10) : BitVec 2) = 0#2 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h3 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 11 10) : BitVec 2) = 0#2 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h4 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 11 10) : BitVec 2) = 0#2 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h5 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h6 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h7 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h8 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h9 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h10 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h11 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h12 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h13 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 13 10) : BitVec 4) = 0#4 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h14 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 14 10) : BitVec 5) = 0#5 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h15 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h16 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h17 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h18 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h19 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h20 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h21 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h22 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h23 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h24 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h25 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h26 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h27 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h28 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h29 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h30 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 12) : BitVec 4) = 0#4 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h31 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 12) : BitVec 4) = 0#4 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h32 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 15) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h33 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 15) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h34 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 21 21) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h35 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 21 21) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h36 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 25 25) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h37 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 27 25) : BitVec 3) = 5#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h38 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 27 27) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h39 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 28 25) : BitVec 4) = 13#4 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h40 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 28 25) : BitVec 4) = 13#4 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h41 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 28 25) : BitVec 4) = 13#4 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h42 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 28 25) : BitVec 4) = 13#4 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h43 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 28 26) : BitVec 3) = 6#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h44 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 28 26) : BitVec 3) = 6#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h45 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 10) : BitVec 21) = 952256#21 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h46 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 10) : BitVec 21) = 952256#21 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h47 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 10) : BitVec 21) = 952256#21 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h48 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 10) : BitVec 21) = 952256#21 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h49 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 10) : BitVec 21) = 952256#21 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h50 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 10) : BitVec 21) = 952256#21 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h51 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 10) : BitVec 21) = 952256#21 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h52 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 11) : BitVec 20) = 476128#20 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h53 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h54 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h55 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h56 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h57 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h58 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h59 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h60 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h61 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h62 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h63 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h64 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h65 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h66 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 21) : BitVec 10) = 464#10 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h67 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 24) : BitVec 7) = 58#7 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h68 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 24) : BitVec 7) = 58#7 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h69 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 24) : BitVec 7) = 58#7 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h70 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 24) : BitVec 7) = 58#7 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h71 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 24) : BitVec 7) = 58#7 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h72 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 24) : BitVec 7) = 58#7 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h73 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 24) : BitVec 7) = 58#7 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h74 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 24) : BitVec 7) = 58#7 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h75 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 10) : BitVec 22) = 3049408#22 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h76 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 11) : BitVec 21) = 1524704#21 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h77 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 14) : BitVec 18) = 190588#18 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h78 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 15) : BitVec 17) = 95294#17 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h79 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 21) : BitVec 11) = 1488#11 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h80 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 21) : BitVec 11) = 1488#11 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h81 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 21) : BitVec 11) = 1488#11 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h82 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 21) : BitVec 11) = 1488#11 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h83 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 21) : BitVec 11) = 1488#11 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h84 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 21) : BitVec 11) = 1488#11 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h85 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 21) : BitVec 11) = 1488#11 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h86 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h87 (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h88 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 0 4 = 15#4 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h89 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 0 5 = 31#5 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h90 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 5 5 = Rn := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    bv_field

theorem dispatch_h91 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 10 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h92 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 10 2 = 0#2 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h93 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 10 3 = 0#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h94 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 10 5 = 0#5 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h95 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 10 6 = 0#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h96 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 12 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h97 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 12 4 = 0#4 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h98 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 13 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h99 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 13 3 = 0#3 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h100 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 14 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h101 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h102 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 15 6 = 62#6 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h103 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 16 5 = 31#5 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h104 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 21 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h105 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 22 2 = 0#2 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h106 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 23 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h107 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 29 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h108 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 29 2 = 1#2 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h109 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 30 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h110 (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) 31 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpAdcsZR.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch (pc : Int) (Rn : BitVec 5) :
    __DecodeA64 (real := real) pc (NativeEntryBodyDispatch.SecpAdcsZR.word 1#1 0#1 1#1 208#8 31#5 0#6 Rn 31#5) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 7))
      if c = true then (do writeReg Register.SEE 7; decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry 31#5 Rn 31#5 1#1 0#1 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h98, dispatch_h99, dispatch_h100, dispatch_h101, dispatch_h102, dispatch_h103, dispatch_h104, dispatch_h105, dispatch_h106, dispatch_h107, dispatch_h108, dispatch_h109, dispatch_h110, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcReg
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h98, dispatch_h99, dispatch_h100, dispatch_h101, dispatch_h102, dispatch_h103, dispatch_h104, dispatch_h105, dispatch_h106, dispatch_h107, dispatch_h108, dispatch_h109, dispatch_h110, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch

/- Internal actual-state selector. The canonical prelude/owner frame must derive
this SEE bound; it is not a public entry premise or a discarded fallback. -/
theorem dispatch_at (pc : Int) (Rn : BitVec 5) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 7) :
    (__DecodeA64 (real := real) pc (NativeEntryBodyDispatch.SecpAdcsZR.selected Rn) : SailM Unit) s =
      (do writeReg Register.SEE 7; decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry 31#5 Rn 31#5 1#1 0#1 1#1 : SailM Unit) s := by
  rw [NativeEntryBodyDispatch.SecpAdcsZR.selected, dispatch real pc Rn]
  have h : (s.regs.bank_Int .SEE <b 7) = true := by simpa using see
  have read : ((do let x ← readReg Register.SEE; pure (x <b 7)) : SailM Bool) s =
      .ok (s.regs.bank_Int .SEE <b 7) s := by rfl
  rw [ArmBridge.CruxCore.bind_app, read]
  dsimp only []
  rw [if_pos h]

#print axioms dispatch_at
end NativeEntryBodyDispatch.SecpAdcsZR
