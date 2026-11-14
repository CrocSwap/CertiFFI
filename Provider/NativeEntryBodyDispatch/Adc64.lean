import NativeEntryBodyDispatch.Adc64Word
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.CruxCore
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace NativeEntryBodyDispatch.Adc64
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 11 10) : BitVec 2) = 0#2 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h1 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 11 10) : BitVec 2) = 0#2 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h2 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 11 10) : BitVec 2) = 0#2 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h3 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h4 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h5 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h6 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h7 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h8 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h9 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h10 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h11 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 13 10) : BitVec 4) = 0#4 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h12 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 14 10) : BitVec 5) = 0#5 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h13 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h14 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h15 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h16 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h17 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h18 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h19 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h20 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h21 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h22 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h23 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h24 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h25 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h26 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h27 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h28 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 12) : BitVec 4) = 0#4 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h29 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 12) : BitVec 4) = 0#4 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h30 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 15) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h31 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 15) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h32 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h33 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h34 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 25 25) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h35 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 27 25) : BitVec 3) = 5#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h36 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 27 27) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h37 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h38 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h39 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h40 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h41 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 28 26) : BitVec 3) = 6#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h42 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 28 26) : BitVec 3) = 6#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h43 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486848#21) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h43b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486848#21) = false := by
  have := dispatch_h43 Rm Rn Rd
  simpa using this

theorem dispatch_h44 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486849#21) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h44b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486849#21) = false := by
  have := dispatch_h44 Rm Rn Rd
  simpa using this

theorem dispatch_h45 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486852#21) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h45b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486852#21) = false := by
  have := dispatch_h45 Rm Rn Rd
  simpa using this

theorem dispatch_h46 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486853#21) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h46b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486853#21) = false := by
  have := dispatch_h46 Rm Rn Rd
  simpa using this

theorem dispatch_h47 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486854#21) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h47b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486854#21) = false := by
  have := dispatch_h47 Rm Rn Rd
  simpa using this

theorem dispatch_h48 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486855#21) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h48b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486855#21) = false := by
  have := dispatch_h48 Rm Rn Rd
  simpa using this

theorem dispatch_h49 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486856#21) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h49b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486856#21) = false := by
  have := dispatch_h49 Rm Rn Rd
  simpa using this

theorem dispatch_h50 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 11) : BitVec 20) = 743425#20) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h50b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 11) : BitVec 20) == 743425#20) = false := by
  have := dispatch_h50 Rm Rn Rd
  simpa using this

theorem dispatch_h51 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h52 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h53 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h54 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h55 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h56 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h57 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h58 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h59 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h60 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h61 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h62 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h63 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h64 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 208#10 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h65 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h66 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h67 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h68 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h69 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h70 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h71 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h72 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h73 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 10) : BitVec 22) = 3584002#22) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h73b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 10) : BitVec 22) == 3584002#22) = false := by
  have := dispatch_h73 Rm Rn Rd
  simpa using this

theorem dispatch_h74 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 11) : BitVec 21) = 1792040#21) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h74b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 11) : BitVec 21) == 1792040#21) = false := by
  have := dispatch_h74 Rm Rn Rd
  simpa using this

theorem dispatch_h75 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 14) : BitVec 18) = 224004#18) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h75b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 14) : BitVec 18) == 224004#18) = false := by
  have := dispatch_h75 Rm Rn Rd
  simpa using this

theorem dispatch_h76 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 15) : BitVec 17) = 29696#17) := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h76b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 15) : BitVec 17) == 29696#17) = false := by
  have := dispatch_h76 Rm Rn Rd
  simpa using this

theorem dispatch_h77 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 1232#11 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h78 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 1232#11 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h79 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 1232#11 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h80 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 1232#11 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h81 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 1232#11 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h82 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 1232#11 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h83 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 1232#11 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h84 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h85 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h86 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 0 5 = Rd := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    bv_field

theorem dispatch_h87 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 5 5 = Rn := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    bv_field

theorem dispatch_h88 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 10 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h89 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 10 2 = 0#2 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h90 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 10 3 = 0#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h91 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 10 5 = 0#5 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h92 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 10 6 = 0#6 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h93 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 12 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h94 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 12 4 = 0#4 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h95 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 13 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h96 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 13 3 = 0#3 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h97 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 14 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h98 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 15 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h99 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 16 5 = Rm := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    bv_field

theorem dispatch_h100 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 21 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h101 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 22 2 = 0#2 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h102 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 23 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h103 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 29 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h104 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 29 2 = 0#2 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h105 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 30 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h106 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) 31 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.Adc64.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch (pc : Int) (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    __DecodeA64 (real := real) pc (NativeEntryBodyDispatch.Adc64.word 1#1 0#1 0#1 208#8 Rm 0#6 Rn Rd) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 6))
      if c = true then (do writeReg Register.SEE 6; decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 0#1 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h73b, dispatch_h74, dispatch_h74b, dispatch_h75, dispatch_h75b, dispatch_h76, dispatch_h76b, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h98, dispatch_h99, dispatch_h100, dispatch_h101, dispatch_h102, dispatch_h103, dispatch_h104, dispatch_h105, dispatch_h106, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcReg
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h73b, dispatch_h74, dispatch_h74b, dispatch_h75, dispatch_h75b, dispatch_h76, dispatch_h76b, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h98, dispatch_h99, dispatch_h100, dispatch_h101, dispatch_h102, dispatch_h103, dispatch_h104, dispatch_h105, dispatch_h106, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch

/- Internal actual-state selector. The canonical prelude/owner frame must derive
this SEE bound; it is not a public entry premise or a discarded fallback. -/
theorem dispatch_at (pc : Int) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 6) :
    (__DecodeA64 (real := real) pc (NativeEntryBodyDispatch.Adc64.selected Rd Rn Rm) : SailM Unit) s =
      (do writeReg Register.SEE 6; decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm 0#1 0#1 1#1 : SailM Unit) s := by
  rw [NativeEntryBodyDispatch.Adc64.selected, dispatch real pc Rm Rn Rd]
  have h : (s.regs.bank_Int .SEE <b 6) = true := by simpa using see
  have read : ((do let x ← readReg Register.SEE; pure (x <b 6)) : SailM Bool) s =
      .ok (s.regs.bank_Int .SEE <b 6) s := by rfl
  rw [ArmBridge.CruxCore.bind_app, read]
  dsimp only []
  rw [if_pos h]

#print axioms dispatch_at
end NativeEntryBodyDispatch.Adc64
