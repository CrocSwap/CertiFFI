import NativeEntryBodyDispatch.SecpLsr63Word
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.CruxCore
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace NativeEntryBodyDispatch.SecpLsr63
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 15 14) : BitVec 2) = 3#2 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h1 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 21 21) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h2 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 25 25) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h3 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 27 25) : BitVec 3) = 1#3 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h4 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 27 27) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h5 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 28 24) : BitVec 5) = 19#5 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h6 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h7 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h8 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h9 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h10 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 28 26) : BitVec 3) = 4#3 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h11 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 28 26) : BitVec 3) = 4#3 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h12 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 18) : BitVec 13) = 5343#13 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h13 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 18) : BitVec 13) = 5343#13 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h14 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 18) : BitVec 13) = 5343#13 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h15 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 18) : BitVec 13) = 5343#13 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h16 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h17 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h18 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h19 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h20 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h21 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h22 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h23 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h24 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h25 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h26 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h27 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h28 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h29 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h30 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 23) : BitVec 8) = 166#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h31 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 31 22) : BitVec 10) = 845#10 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h32 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 31 22) : BitVec 10) = 845#10 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h33 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h34 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h35 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 0 5 = Rd := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    bv_field

theorem dispatch_h36 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 5 5 = Rn := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    bv_field

theorem dispatch_h37 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 10 4 = 15#4 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h38 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 10 6 = 63#6 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h39 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 10 8 = 255#8 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h40 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 10 12 = 4095#12 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h41 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 14 2 = 3#2 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h42 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 16 5 = 31#5 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h43 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 16 6 = 63#6 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h44 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 21 2 = 3#2 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h45 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 22 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h46 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 29 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h47 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 29 2 = 2#2 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h48 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 30 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h49 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) 31 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.SecpLsr63.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch (pc : Int) (Rn : BitVec 5) (Rd : BitVec 5) :
    __DecodeA64 (real := real) pc (NativeEntryBodyDispatch.SecpLsr63.word 1#1 2#2 38#6 1#1 63#6 63#6 Rn Rd) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 78))
      if c = true then (do writeReg Register.SEE 78; decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 63#6 1#1 2#2 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcImm
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch

/- Internal actual-state selector. The canonical prelude/owner frame must derive
this SEE bound; it is not a public entry premise or a discarded fallback. -/
theorem dispatch_at (pc : Int) (Rd : BitVec 5) (Rn : BitVec 5) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 78) :
    (__DecodeA64 (real := real) pc (NativeEntryBodyDispatch.SecpLsr63.selected Rd Rn) : SailM Unit) s =
      (do writeReg Register.SEE 78; decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn 63#6 63#6 1#1 2#2 1#1 : SailM Unit) s := by
  rw [NativeEntryBodyDispatch.SecpLsr63.selected, dispatch real pc Rn Rd]
  have h : (s.regs.bank_Int .SEE <b 78) = true := by simpa using see
  have read : ((do let x ← readReg Register.SEE; pure (x <b 78)) : SailM Bool) s =
      .ok (s.regs.bank_Int .SEE <b 78) s := by rfl
  rw [ArmBridge.CruxCore.bind_app, read]
  dsimp only []
  rw [if_pos h]

#print axioms dispatch_at
end NativeEntryBodyDispatch.SecpLsr63
