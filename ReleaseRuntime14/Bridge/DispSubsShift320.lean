import CryptoBridge.AddSubShiftDecode
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace ArmBridge.Disp
variable (real : Type) [Sail.SailReal real]

theorem disp_subsshift32_0_h0 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 11 10) : BitVec 2) = 0#2 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h1 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 11 10) : BitVec 2) = 0#2 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h2 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 11 10) : BitVec 2) = 0#2 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h3 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h4 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h5 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h6 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h7 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h8 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h9 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h10 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 12 10) : BitVec 3) = 0#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h11 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 13 10) : BitVec 4) = 0#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h12 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 14 10) : BitVec 5) = 0#5 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h13 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h14 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h15 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h16 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h17 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h18 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h19 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h20 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h21 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h22 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h23 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h24 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h25 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h26 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h27 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 10) : BitVec 6) = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h28 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 12) : BitVec 4) = 0#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h29 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 12) : BitVec 4) = 0#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h30 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 15) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h31 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 15) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h32 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h33 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h34 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 25 25) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h35 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 27 25) : BitVec 3) = 5#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h36 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 27 27) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h37 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h38 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h39 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h40 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h41 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 28 26) : BitVec 3) = 2#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h42 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 28 26) : BitVec 3) = 2#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h43 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486848#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h43b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486848#21) = false := by
  have := disp_subsshift32_0_h43 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h44 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486849#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h44b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486849#21) = false := by
  have := disp_subsshift32_0_h44 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h45 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486852#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h45b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486852#21) = false := by
  have := disp_subsshift32_0_h45 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h46 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486853#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h46b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486853#21) = false := by
  have := disp_subsshift32_0_h46 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h47 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486854#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h47b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486854#21) = false := by
  have := disp_subsshift32_0_h47 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h48 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486855#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h48b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486855#21) = false := by
  have := disp_subsshift32_0_h48 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h49 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) = 1486856#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h49b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 10) : BitVec 21) == 1486856#21) = false := by
  have := disp_subsshift32_0_h49 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h50 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 11) : BitVec 20) = 743425#20) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h50b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 11) : BitVec 20) == 743425#20) = false := by
  have := disp_subsshift32_0_h50 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h51 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h52 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h53 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h54 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h55 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h56 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h57 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h58 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h59 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h60 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h61 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h62 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h63 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h64 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 21) : BitVec 10) = 856#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h65 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 107#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h66 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 107#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h67 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 107#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h68 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 107#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h69 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 107#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h70 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 107#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h71 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 107#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h72 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 24) : BitVec 7) = 107#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h73 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 10) : BitVec 22) = 3584002#22) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h73b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 10) : BitVec 22) == 3584002#22) = false := by
  have := disp_subsshift32_0_h73 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h74 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 11) : BitVec 21) = 1792040#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h74b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 11) : BitVec 21) == 1792040#21) = false := by
  have := disp_subsshift32_0_h74 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h75 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 14) : BitVec 18) = 224004#18) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h75b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 14) : BitVec 18) == 224004#18) = false := by
  have := disp_subsshift32_0_h75 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h76 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 15) : BitVec 17) = 29696#17) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsshift32_0_h76b (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 15) : BitVec 17) == 29696#17) = false := by
  have := disp_subsshift32_0_h76 Rm Rn Rd
  simpa using this

theorem disp_subsshift32_0_h77 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 856#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h78 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 856#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h79 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 856#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h80 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 856#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h81 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 856#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h82 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 856#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h83 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 21) : BitVec 11) = 856#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h84 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 31) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h85 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 31) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h86 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 0 5 = Rd := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    bv_field

theorem disp_subsshift32_0_h87 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 5 5 = Rn := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    bv_field

theorem disp_subsshift32_0_h88 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 10 1 = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h89 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 10 2 = 0#2 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h90 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 10 3 = 0#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h91 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 10 5 = 0#5 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h92 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 10 6 = 0#6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h93 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 12 1 = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h94 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 12 4 = 0#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h95 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 13 1 = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h96 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 13 3 = 0#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h97 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 14 1 = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h98 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 15 1 = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h99 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 16 5 = Rm := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    bv_field

theorem disp_subsshift32_0_h100 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 21 1 = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h101 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 22 2 = 0#2 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h102 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 23 1 = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h103 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 29 1 = 1#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h104 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 29 2 = 3#2 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_subsshift32_0_h105 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 30 1 = 1#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0_h106 (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) 31 1 = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsshift32_0 (pc : Int) (Rm : BitVec 5) (Rn : BitVec 5) (Rd : BitVec 5) :
    __DecodeA64 (real := real) pc (CryptoBridge.AddSubShift.addSubShiftWord 0#1 1#1 1#1 0#2 Rm 0#6 Rn Rd) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 17))
      if c = true then (do writeReg Register.SEE 17; decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn 0#6 Rm 0#2 1#1 1#1 0#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [disp_subsshift32_0_h0, disp_subsshift32_0_h1, disp_subsshift32_0_h2, disp_subsshift32_0_h3, disp_subsshift32_0_h4, disp_subsshift32_0_h5, disp_subsshift32_0_h6, disp_subsshift32_0_h7, disp_subsshift32_0_h8, disp_subsshift32_0_h9, disp_subsshift32_0_h10, disp_subsshift32_0_h11, disp_subsshift32_0_h12, disp_subsshift32_0_h13, disp_subsshift32_0_h14, disp_subsshift32_0_h15, disp_subsshift32_0_h16, disp_subsshift32_0_h17, disp_subsshift32_0_h18, disp_subsshift32_0_h19, disp_subsshift32_0_h20, disp_subsshift32_0_h21, disp_subsshift32_0_h22, disp_subsshift32_0_h23, disp_subsshift32_0_h24, disp_subsshift32_0_h25, disp_subsshift32_0_h26, disp_subsshift32_0_h27, disp_subsshift32_0_h28, disp_subsshift32_0_h29, disp_subsshift32_0_h30, disp_subsshift32_0_h31, disp_subsshift32_0_h32, disp_subsshift32_0_h33, disp_subsshift32_0_h34, disp_subsshift32_0_h35, disp_subsshift32_0_h36, disp_subsshift32_0_h37, disp_subsshift32_0_h38, disp_subsshift32_0_h39, disp_subsshift32_0_h40, disp_subsshift32_0_h41, disp_subsshift32_0_h42, disp_subsshift32_0_h43, disp_subsshift32_0_h43b, disp_subsshift32_0_h44, disp_subsshift32_0_h44b, disp_subsshift32_0_h45, disp_subsshift32_0_h45b, disp_subsshift32_0_h46, disp_subsshift32_0_h46b, disp_subsshift32_0_h47, disp_subsshift32_0_h47b, disp_subsshift32_0_h48, disp_subsshift32_0_h48b, disp_subsshift32_0_h49, disp_subsshift32_0_h49b, disp_subsshift32_0_h50, disp_subsshift32_0_h50b, disp_subsshift32_0_h51, disp_subsshift32_0_h52, disp_subsshift32_0_h53, disp_subsshift32_0_h54, disp_subsshift32_0_h55, disp_subsshift32_0_h56, disp_subsshift32_0_h57, disp_subsshift32_0_h58, disp_subsshift32_0_h59, disp_subsshift32_0_h60, disp_subsshift32_0_h61, disp_subsshift32_0_h62, disp_subsshift32_0_h63, disp_subsshift32_0_h64, disp_subsshift32_0_h65, disp_subsshift32_0_h66, disp_subsshift32_0_h67, disp_subsshift32_0_h68, disp_subsshift32_0_h69, disp_subsshift32_0_h70, disp_subsshift32_0_h71, disp_subsshift32_0_h72, disp_subsshift32_0_h73, disp_subsshift32_0_h73b, disp_subsshift32_0_h74, disp_subsshift32_0_h74b, disp_subsshift32_0_h75, disp_subsshift32_0_h75b, disp_subsshift32_0_h76, disp_subsshift32_0_h76b, disp_subsshift32_0_h77, disp_subsshift32_0_h78, disp_subsshift32_0_h79, disp_subsshift32_0_h80, disp_subsshift32_0_h81, disp_subsshift32_0_h82, disp_subsshift32_0_h83, disp_subsshift32_0_h84, disp_subsshift32_0_h85, disp_subsshift32_0_h86, disp_subsshift32_0_h87, disp_subsshift32_0_h88, disp_subsshift32_0_h89, disp_subsshift32_0_h90, disp_subsshift32_0_h91, disp_subsshift32_0_h92, disp_subsshift32_0_h93, disp_subsshift32_0_h94, disp_subsshift32_0_h95, disp_subsshift32_0_h96, disp_subsshift32_0_h97, disp_subsshift32_0_h98, disp_subsshift32_0_h99, disp_subsshift32_0_h100, disp_subsshift32_0_h101, disp_subsshift32_0_h102, disp_subsshift32_0_h103, disp_subsshift32_0_h104, disp_subsshift32_0_h105, disp_subsshift32_0_h106, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcReg
  simp (config := {decide := true}) only [disp_subsshift32_0_h0, disp_subsshift32_0_h1, disp_subsshift32_0_h2, disp_subsshift32_0_h3, disp_subsshift32_0_h4, disp_subsshift32_0_h5, disp_subsshift32_0_h6, disp_subsshift32_0_h7, disp_subsshift32_0_h8, disp_subsshift32_0_h9, disp_subsshift32_0_h10, disp_subsshift32_0_h11, disp_subsshift32_0_h12, disp_subsshift32_0_h13, disp_subsshift32_0_h14, disp_subsshift32_0_h15, disp_subsshift32_0_h16, disp_subsshift32_0_h17, disp_subsshift32_0_h18, disp_subsshift32_0_h19, disp_subsshift32_0_h20, disp_subsshift32_0_h21, disp_subsshift32_0_h22, disp_subsshift32_0_h23, disp_subsshift32_0_h24, disp_subsshift32_0_h25, disp_subsshift32_0_h26, disp_subsshift32_0_h27, disp_subsshift32_0_h28, disp_subsshift32_0_h29, disp_subsshift32_0_h30, disp_subsshift32_0_h31, disp_subsshift32_0_h32, disp_subsshift32_0_h33, disp_subsshift32_0_h34, disp_subsshift32_0_h35, disp_subsshift32_0_h36, disp_subsshift32_0_h37, disp_subsshift32_0_h38, disp_subsshift32_0_h39, disp_subsshift32_0_h40, disp_subsshift32_0_h41, disp_subsshift32_0_h42, disp_subsshift32_0_h43, disp_subsshift32_0_h43b, disp_subsshift32_0_h44, disp_subsshift32_0_h44b, disp_subsshift32_0_h45, disp_subsshift32_0_h45b, disp_subsshift32_0_h46, disp_subsshift32_0_h46b, disp_subsshift32_0_h47, disp_subsshift32_0_h47b, disp_subsshift32_0_h48, disp_subsshift32_0_h48b, disp_subsshift32_0_h49, disp_subsshift32_0_h49b, disp_subsshift32_0_h50, disp_subsshift32_0_h50b, disp_subsshift32_0_h51, disp_subsshift32_0_h52, disp_subsshift32_0_h53, disp_subsshift32_0_h54, disp_subsshift32_0_h55, disp_subsshift32_0_h56, disp_subsshift32_0_h57, disp_subsshift32_0_h58, disp_subsshift32_0_h59, disp_subsshift32_0_h60, disp_subsshift32_0_h61, disp_subsshift32_0_h62, disp_subsshift32_0_h63, disp_subsshift32_0_h64, disp_subsshift32_0_h65, disp_subsshift32_0_h66, disp_subsshift32_0_h67, disp_subsshift32_0_h68, disp_subsshift32_0_h69, disp_subsshift32_0_h70, disp_subsshift32_0_h71, disp_subsshift32_0_h72, disp_subsshift32_0_h73, disp_subsshift32_0_h73b, disp_subsshift32_0_h74, disp_subsshift32_0_h74b, disp_subsshift32_0_h75, disp_subsshift32_0_h75b, disp_subsshift32_0_h76, disp_subsshift32_0_h76b, disp_subsshift32_0_h77, disp_subsshift32_0_h78, disp_subsshift32_0_h79, disp_subsshift32_0_h80, disp_subsshift32_0_h81, disp_subsshift32_0_h82, disp_subsshift32_0_h83, disp_subsshift32_0_h84, disp_subsshift32_0_h85, disp_subsshift32_0_h86, disp_subsshift32_0_h87, disp_subsshift32_0_h88, disp_subsshift32_0_h89, disp_subsshift32_0_h90, disp_subsshift32_0_h91, disp_subsshift32_0_h92, disp_subsshift32_0_h93, disp_subsshift32_0_h94, disp_subsshift32_0_h95, disp_subsshift32_0_h96, disp_subsshift32_0_h97, disp_subsshift32_0_h98, disp_subsshift32_0_h99, disp_subsshift32_0_h100, disp_subsshift32_0_h101, disp_subsshift32_0_h102, disp_subsshift32_0_h103, disp_subsshift32_0_h104, disp_subsshift32_0_h105, disp_subsshift32_0_h106, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms disp_subsshift32_0
end ArmBridge.Disp
