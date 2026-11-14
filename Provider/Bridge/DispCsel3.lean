import CryptoBridge.CondSelDecode
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace ArmBridge.Disp
variable (real : Type) [Sail.SailReal real]

theorem disp_csel_3_h0 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 11 10) : BitVec 2) = 0#2 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_csel_3_h1 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 11 10) : BitVec 2) = 0#2 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_csel_3_h2 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 11 10) : BitVec 2) = 0#2 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_csel_3_h3 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 12 10) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h4 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 12 10) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h5 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 12 10) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h6 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 12 10) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h7 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 12 10) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h8 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 12 10) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h9 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 12 10) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h10 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 12 10) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h11 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 13 10) : BitVec 4) = 12#4 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h12 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 14 10) : BitVec 5) = 12#5 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h13 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h14 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h15 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h16 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h17 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h18 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h19 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h20 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h21 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h22 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h23 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h24 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h25 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h26 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h27 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 10) : BitVec 6) = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h28 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 12) : BitVec 4) = 3#4 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h29 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 12) : BitVec 4) = 3#4 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h30 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 15) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h31 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 15) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h32 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h33 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h34 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 25 25) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h35 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 27 25) : BitVec 3) = 5#3 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h36 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 27 27) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h37 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h38 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h39 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h40 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h41 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 28 26) : BitVec 3) = 6#3 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h42 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 28 26) : BitVec 3) = 6#3 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h43 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) = 1486848#21) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h43b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) == 1486848#21) = false := by
  have := disp_csel_3_h43 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h44 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) = 1486849#21) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h44b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) == 1486849#21) = false := by
  have := disp_csel_3_h44 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h45 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) = 1486852#21) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h45b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) == 1486852#21) = false := by
  have := disp_csel_3_h45 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h46 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) = 1486853#21) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h46b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) == 1486853#21) = false := by
  have := disp_csel_3_h46 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h47 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) = 1486854#21) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h47b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) == 1486854#21) = false := by
  have := disp_csel_3_h47 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h48 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) = 1486855#21) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h48b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) == 1486855#21) = false := by
  have := disp_csel_3_h48 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h49 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) = 1486856#21) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h49b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 10) : BitVec 21) == 1486856#21) = false := by
  have := disp_csel_3_h49 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h50 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 11) : BitVec 20) = 743425#20) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h50b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 11) : BitVec 20) == 743425#20) = false := by
  have := disp_csel_3_h50 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h51 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h52 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h53 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h54 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h55 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h56 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h57 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h58 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h59 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h60 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h61 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h62 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h63 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h64 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h65 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h66 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h67 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h68 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h69 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h70 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h71 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h72 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h73 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 10) : BitVec 22) = 3584002#22) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h73b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 10) : BitVec 22) == 3584002#22) = false := by
  have := disp_csel_3_h73 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h74 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 11) : BitVec 21) = 1792040#21) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h74b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 11) : BitVec 21) == 1792040#21) = false := by
  have := disp_csel_3_h74 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h75 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 14) : BitVec 18) = 224004#18) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h75b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 14) : BitVec 18) == 224004#18) = false := by
  have := disp_csel_3_h75 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h76 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 15) : BitVec 17) = 29696#17) := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_csel_3_h76b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 15) : BitVec 17) == 29696#17) = false := by
  have := disp_csel_3_h76 Rm Rn Rd
  simpa using this

theorem disp_csel_3_h77 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 21) : BitVec 11) = 1236#11 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h78 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 21) : BitVec 11) = 1236#11 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h79 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 21) : BitVec 11) = 1236#11 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h80 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 21) : BitVec 11) = 1236#11 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h81 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 21) : BitVec 11) = 1236#11 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h82 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 21) : BitVec 11) = 1236#11 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h83 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 21) : BitVec 11) = 1236#11 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h84 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h85 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.CondSel.condSelWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h86 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 0 5 = Rd := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    bv_field

theorem disp_csel_3_h87 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 5 5 = Rn := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    bv_field

theorem disp_csel_3_h88 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 10 1 = 0#1 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h89 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 10 2 = 0#2 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_csel_3_h90 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 10 3 = 4#3 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h91 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 10 5 = 12#5 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h92 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 10 6 = 12#6 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h93 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 12 1 = 1#1 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h94 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 12 4 = 3#4 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_csel_3_h95 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 13 1 = 1#1 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h96 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 13 3 = 1#3 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_csel_3_h97 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 14 1 = 0#1 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h98 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 15 1 = 0#1 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h99 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 16 5 = Rm := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    bv_field

theorem disp_csel_3_h100 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 21 1 = 0#1 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h101 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 22 2 = 2#2 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_csel_3_h102 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 23 1 = 1#1 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h103 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 29 1 = 0#1 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h104 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 29 2 = 0#2 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_csel_3_h105 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 30 1 = 0#1 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3_h106 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) 31 1 = 1#1 := by
    unfold CryptoBridge.CondSel.condSelWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_csel_3 (pc : Int) (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    __DecodeA64 (real := real) pc (CryptoBridge.CondSel.condSelWord 1#1 0#1 0#1 Rm 3#4 0#2 Rn Rd) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 187))
      if c = true then (do writeReg Register.SEE 187; decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 Rm 0#1 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [disp_csel_3_h0, disp_csel_3_h1, disp_csel_3_h2, disp_csel_3_h3, disp_csel_3_h4, disp_csel_3_h5, disp_csel_3_h6, disp_csel_3_h7, disp_csel_3_h8, disp_csel_3_h9, disp_csel_3_h10, disp_csel_3_h11, disp_csel_3_h12, disp_csel_3_h13, disp_csel_3_h14, disp_csel_3_h15, disp_csel_3_h16, disp_csel_3_h17, disp_csel_3_h18, disp_csel_3_h19, disp_csel_3_h20, disp_csel_3_h21, disp_csel_3_h22, disp_csel_3_h23, disp_csel_3_h24, disp_csel_3_h25, disp_csel_3_h26, disp_csel_3_h27, disp_csel_3_h28, disp_csel_3_h29, disp_csel_3_h30, disp_csel_3_h31, disp_csel_3_h32, disp_csel_3_h33, disp_csel_3_h34, disp_csel_3_h35, disp_csel_3_h36, disp_csel_3_h37, disp_csel_3_h38, disp_csel_3_h39, disp_csel_3_h40, disp_csel_3_h41, disp_csel_3_h42, disp_csel_3_h43, disp_csel_3_h43b, disp_csel_3_h44, disp_csel_3_h44b, disp_csel_3_h45, disp_csel_3_h45b, disp_csel_3_h46, disp_csel_3_h46b, disp_csel_3_h47, disp_csel_3_h47b, disp_csel_3_h48, disp_csel_3_h48b, disp_csel_3_h49, disp_csel_3_h49b, disp_csel_3_h50, disp_csel_3_h50b, disp_csel_3_h51, disp_csel_3_h52, disp_csel_3_h53, disp_csel_3_h54, disp_csel_3_h55, disp_csel_3_h56, disp_csel_3_h57, disp_csel_3_h58, disp_csel_3_h59, disp_csel_3_h60, disp_csel_3_h61, disp_csel_3_h62, disp_csel_3_h63, disp_csel_3_h64, disp_csel_3_h65, disp_csel_3_h66, disp_csel_3_h67, disp_csel_3_h68, disp_csel_3_h69, disp_csel_3_h70, disp_csel_3_h71, disp_csel_3_h72, disp_csel_3_h73, disp_csel_3_h73b, disp_csel_3_h74, disp_csel_3_h74b, disp_csel_3_h75, disp_csel_3_h75b, disp_csel_3_h76, disp_csel_3_h76b, disp_csel_3_h77, disp_csel_3_h78, disp_csel_3_h79, disp_csel_3_h80, disp_csel_3_h81, disp_csel_3_h82, disp_csel_3_h83, disp_csel_3_h84, disp_csel_3_h85, disp_csel_3_h86, disp_csel_3_h87, disp_csel_3_h88, disp_csel_3_h89, disp_csel_3_h90, disp_csel_3_h91, disp_csel_3_h92, disp_csel_3_h93, disp_csel_3_h94, disp_csel_3_h95, disp_csel_3_h96, disp_csel_3_h97, disp_csel_3_h98, disp_csel_3_h99, disp_csel_3_h100, disp_csel_3_h101, disp_csel_3_h102, disp_csel_3_h103, disp_csel_3_h104, disp_csel_3_h105, disp_csel_3_h106, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcReg
  simp (config := {decide := true}) only [disp_csel_3_h0, disp_csel_3_h1, disp_csel_3_h2, disp_csel_3_h3, disp_csel_3_h4, disp_csel_3_h5, disp_csel_3_h6, disp_csel_3_h7, disp_csel_3_h8, disp_csel_3_h9, disp_csel_3_h10, disp_csel_3_h11, disp_csel_3_h12, disp_csel_3_h13, disp_csel_3_h14, disp_csel_3_h15, disp_csel_3_h16, disp_csel_3_h17, disp_csel_3_h18, disp_csel_3_h19, disp_csel_3_h20, disp_csel_3_h21, disp_csel_3_h22, disp_csel_3_h23, disp_csel_3_h24, disp_csel_3_h25, disp_csel_3_h26, disp_csel_3_h27, disp_csel_3_h28, disp_csel_3_h29, disp_csel_3_h30, disp_csel_3_h31, disp_csel_3_h32, disp_csel_3_h33, disp_csel_3_h34, disp_csel_3_h35, disp_csel_3_h36, disp_csel_3_h37, disp_csel_3_h38, disp_csel_3_h39, disp_csel_3_h40, disp_csel_3_h41, disp_csel_3_h42, disp_csel_3_h43, disp_csel_3_h43b, disp_csel_3_h44, disp_csel_3_h44b, disp_csel_3_h45, disp_csel_3_h45b, disp_csel_3_h46, disp_csel_3_h46b, disp_csel_3_h47, disp_csel_3_h47b, disp_csel_3_h48, disp_csel_3_h48b, disp_csel_3_h49, disp_csel_3_h49b, disp_csel_3_h50, disp_csel_3_h50b, disp_csel_3_h51, disp_csel_3_h52, disp_csel_3_h53, disp_csel_3_h54, disp_csel_3_h55, disp_csel_3_h56, disp_csel_3_h57, disp_csel_3_h58, disp_csel_3_h59, disp_csel_3_h60, disp_csel_3_h61, disp_csel_3_h62, disp_csel_3_h63, disp_csel_3_h64, disp_csel_3_h65, disp_csel_3_h66, disp_csel_3_h67, disp_csel_3_h68, disp_csel_3_h69, disp_csel_3_h70, disp_csel_3_h71, disp_csel_3_h72, disp_csel_3_h73, disp_csel_3_h73b, disp_csel_3_h74, disp_csel_3_h74b, disp_csel_3_h75, disp_csel_3_h75b, disp_csel_3_h76, disp_csel_3_h76b, disp_csel_3_h77, disp_csel_3_h78, disp_csel_3_h79, disp_csel_3_h80, disp_csel_3_h81, disp_csel_3_h82, disp_csel_3_h83, disp_csel_3_h84, disp_csel_3_h85, disp_csel_3_h86, disp_csel_3_h87, disp_csel_3_h88, disp_csel_3_h89, disp_csel_3_h90, disp_csel_3_h91, disp_csel_3_h92, disp_csel_3_h93, disp_csel_3_h94, disp_csel_3_h95, disp_csel_3_h96, disp_csel_3_h97, disp_csel_3_h98, disp_csel_3_h99, disp_csel_3_h100, disp_csel_3_h101, disp_csel_3_h102, disp_csel_3_h103, disp_csel_3_h104, disp_csel_3_h105, disp_csel_3_h106, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms disp_csel_3
end ArmBridge.Disp
