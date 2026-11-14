import CryptoBridge.LogImmDecode
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace ArmBridge.Disp
variable (real : Type) [Sail.SailReal real]

theorem disp_andslimm__0_2_h0 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 15 14) : BitVec 2) = 0#2 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h1 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_andslimm__0_2_h2 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 25 25) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_andslimm__0_2_h3 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 27 25) : BitVec 3) = 1#3 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h4 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 27 27) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_andslimm__0_2_h5 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 28 24) : BitVec 5) = 18#5 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h6 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h7 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h8 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h9 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h10 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 28 26) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h11 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 28 26) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h12 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 18) : BitVec 13) = 7312#13 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h13 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 18) : BitVec 13) = 7312#13 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h14 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 18) : BitVec 13) = 7312#13 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h15 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 18) : BitVec 13) = 7312#13 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h16 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h17 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h18 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h19 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h20 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h21 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h22 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h23 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h24 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h25 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h26 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h27 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h28 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h29 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h30 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 23) : BitVec 8) = 228#8 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h31 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 31 22) : BitVec 10) = 969#10 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h32 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 31 22) : BitVec 10) = 969#10 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h33 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_andslimm__0_2_h34 (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.LogImm.logImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_andslimm__0_2_h35 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 0 5 = Rd := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    bv_field

theorem disp_andslimm__0_2_h36 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 5 5 = Rn := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    bv_field

theorem disp_andslimm__0_2_h37 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 10 4 = 2#4 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h38 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 10 6 = 2#6 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h39 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 10 8 = 2#8 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h40 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 10 12 = 2#12 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h41 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 14 2 = 0#2 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h42 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 16 5 = 0#5 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h43 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 16 6 = 0#6 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h44 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 21 2 = 2#2 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h45 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 22 1 = 1#1 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_andslimm__0_2_h46 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 29 1 = 1#1 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_andslimm__0_2_h47 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 29 2 = 3#2 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_andslimm__0_2_h48 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 30 1 = 1#1 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_andslimm__0_2_h49 (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) 31 1 = 1#1 := by
    unfold CryptoBridge.LogImm.logImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_andslimm__0_2 (pc : Int) (Rn : BitVec 5) (Rd : BitVec 5) :
    __DecodeA64 (real := real) pc (CryptoBridge.LogImm.logImmWord 1#1 3#2 1#1 0#6 2#6 Rn Rd) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 41))
      if c = true then (do writeReg Register.SEE 41; decode_ands_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn 2#6 0#6 1#1 3#2 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [disp_andslimm__0_2_h0, disp_andslimm__0_2_h1, disp_andslimm__0_2_h2, disp_andslimm__0_2_h3, disp_andslimm__0_2_h4, disp_andslimm__0_2_h5, disp_andslimm__0_2_h6, disp_andslimm__0_2_h7, disp_andslimm__0_2_h8, disp_andslimm__0_2_h9, disp_andslimm__0_2_h10, disp_andslimm__0_2_h11, disp_andslimm__0_2_h12, disp_andslimm__0_2_h13, disp_andslimm__0_2_h14, disp_andslimm__0_2_h15, disp_andslimm__0_2_h16, disp_andslimm__0_2_h17, disp_andslimm__0_2_h18, disp_andslimm__0_2_h19, disp_andslimm__0_2_h20, disp_andslimm__0_2_h21, disp_andslimm__0_2_h22, disp_andslimm__0_2_h23, disp_andslimm__0_2_h24, disp_andslimm__0_2_h25, disp_andslimm__0_2_h26, disp_andslimm__0_2_h27, disp_andslimm__0_2_h28, disp_andslimm__0_2_h29, disp_andslimm__0_2_h30, disp_andslimm__0_2_h31, disp_andslimm__0_2_h32, disp_andslimm__0_2_h33, disp_andslimm__0_2_h34, disp_andslimm__0_2_h35, disp_andslimm__0_2_h36, disp_andslimm__0_2_h37, disp_andslimm__0_2_h38, disp_andslimm__0_2_h39, disp_andslimm__0_2_h40, disp_andslimm__0_2_h41, disp_andslimm__0_2_h42, disp_andslimm__0_2_h43, disp_andslimm__0_2_h44, disp_andslimm__0_2_h45, disp_andslimm__0_2_h46, disp_andslimm__0_2_h47, disp_andslimm__0_2_h48, disp_andslimm__0_2_h49, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcImm
  simp (config := {decide := true}) only [disp_andslimm__0_2_h0, disp_andslimm__0_2_h1, disp_andslimm__0_2_h2, disp_andslimm__0_2_h3, disp_andslimm__0_2_h4, disp_andslimm__0_2_h5, disp_andslimm__0_2_h6, disp_andslimm__0_2_h7, disp_andslimm__0_2_h8, disp_andslimm__0_2_h9, disp_andslimm__0_2_h10, disp_andslimm__0_2_h11, disp_andslimm__0_2_h12, disp_andslimm__0_2_h13, disp_andslimm__0_2_h14, disp_andslimm__0_2_h15, disp_andslimm__0_2_h16, disp_andslimm__0_2_h17, disp_andslimm__0_2_h18, disp_andslimm__0_2_h19, disp_andslimm__0_2_h20, disp_andslimm__0_2_h21, disp_andslimm__0_2_h22, disp_andslimm__0_2_h23, disp_andslimm__0_2_h24, disp_andslimm__0_2_h25, disp_andslimm__0_2_h26, disp_andslimm__0_2_h27, disp_andslimm__0_2_h28, disp_andslimm__0_2_h29, disp_andslimm__0_2_h30, disp_andslimm__0_2_h31, disp_andslimm__0_2_h32, disp_andslimm__0_2_h33, disp_andslimm__0_2_h34, disp_andslimm__0_2_h35, disp_andslimm__0_2_h36, disp_andslimm__0_2_h37, disp_andslimm__0_2_h38, disp_andslimm__0_2_h39, disp_andslimm__0_2_h40, disp_andslimm__0_2_h41, disp_andslimm__0_2_h42, disp_andslimm__0_2_h43, disp_andslimm__0_2_h44, disp_andslimm__0_2_h45, disp_andslimm__0_2_h46, disp_andslimm__0_2_h47, disp_andslimm__0_2_h48, disp_andslimm__0_2_h49, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms disp_andslimm__0_2
end ArmBridge.Disp
