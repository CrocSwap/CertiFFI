import CryptoBridge.AddSubShiftDecode
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace ArmBridge.Disp
variable (real : Type) [Sail.SailReal real]

theorem disp_addsshift_0_h0 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_addsshift_0_h1 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_addsshift_0_h2 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 25 25) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_addsshift_0_h3 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 27 25) : BitVec 3) = 5#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h4 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 27 27) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_addsshift_0_h5 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h6 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h7 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h8 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h9 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 28 26) : BitVec 3) = 2#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h10 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 28 26) : BitVec 3) = 2#3 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h11 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486848#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h11b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486848#21) = false := by
  have := disp_addsshift_0_h11 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h12 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486849#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h12b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486849#21) = false := by
  have := disp_addsshift_0_h12 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h13 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486852#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h13b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486852#21) = false := by
  have := disp_addsshift_0_h13 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h14 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486853#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h14b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486853#21) = false := by
  have := disp_addsshift_0_h14 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h15 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486854#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h15b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486854#21) = false := by
  have := disp_addsshift_0_h15 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h16 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486855#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h16b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486855#21) = false := by
  have := disp_addsshift_0_h16 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h17 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486856#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h17b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486856#21) = false := by
  have := disp_addsshift_0_h17 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h18 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 11) : BitVec 20) = 743425#20) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 11) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h18b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 11) : BitVec 20) == 743425#20) = false := by
  have := disp_addsshift_0_h18 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h19 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h20 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h21 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h22 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h23 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h24 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h25 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h26 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h27 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h28 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h29 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h30 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h31 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h32 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h33 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h34 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h35 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h36 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h37 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h38 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h39 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h40 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h41 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 10) : BitVec 22) = 3584002#22) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h41b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 10) : BitVec 22) == 3584002#22) = false := by
  have := disp_addsshift_0_h41 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h42 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 11) : BitVec 21) = 1792040#21) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 11) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h42b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 11) : BitVec 21) == 1792040#21) = false := by
  have := disp_addsshift_0_h42 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h43 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 14) : BitVec 18) = 224004#18) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h43b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 14) : BitVec 18) == 224004#18) = false := by
  have := disp_addsshift_0_h43 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h44 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 15) : BitVec 17) = 29696#17) := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_addsshift_0_h44b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 15) : BitVec 17) == 29696#17) = false := by
  have := disp_addsshift_0_h44 Rm imm6 Rn Rd
  simpa using this

theorem disp_addsshift_0_h45 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h46 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h47 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h48 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h49 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h50 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h51 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_addsshift_0_h52 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_addsshift_0_h53 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_addsshift_0_h54 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 0 5 = Rd := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    bv_field

theorem disp_addsshift_0_h55 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 5 5 = Rn := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    bv_field

theorem disp_addsshift_0_h56 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 10 6 = imm6 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    bv_field

theorem disp_addsshift_0_h57 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 16 5 = Rm := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    bv_field

theorem disp_addsshift_0_h58 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 21 1 = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_addsshift_0_h59 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 22 2 = 0#2 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_addsshift_0_h60 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 23 1 = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_addsshift_0_h61 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 29 1 = 1#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_addsshift_0_h62 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 29 2 = 1#2 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_addsshift_0_h63 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 30 1 = 0#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_addsshift_0_h64 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) 31 1 = 1#1 := by
    unfold CryptoBridge.AddSubShift.addSubShiftWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_addsshift_0 (pc : Int) (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    __DecodeA64 (real := real) pc (CryptoBridge.AddSubShift.addSubShiftWord 1#1 0#1 1#1 0#2 Rm imm6 Rn Rd) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 15))
      if c = true then (do writeReg Register.SEE 15; decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 0#1 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [disp_addsshift_0_h0, disp_addsshift_0_h1, disp_addsshift_0_h2, disp_addsshift_0_h3, disp_addsshift_0_h4, disp_addsshift_0_h5, disp_addsshift_0_h6, disp_addsshift_0_h7, disp_addsshift_0_h8, disp_addsshift_0_h9, disp_addsshift_0_h10, disp_addsshift_0_h11, disp_addsshift_0_h11b, disp_addsshift_0_h12, disp_addsshift_0_h12b, disp_addsshift_0_h13, disp_addsshift_0_h13b, disp_addsshift_0_h14, disp_addsshift_0_h14b, disp_addsshift_0_h15, disp_addsshift_0_h15b, disp_addsshift_0_h16, disp_addsshift_0_h16b, disp_addsshift_0_h17, disp_addsshift_0_h17b, disp_addsshift_0_h18, disp_addsshift_0_h18b, disp_addsshift_0_h19, disp_addsshift_0_h20, disp_addsshift_0_h21, disp_addsshift_0_h22, disp_addsshift_0_h23, disp_addsshift_0_h24, disp_addsshift_0_h25, disp_addsshift_0_h26, disp_addsshift_0_h27, disp_addsshift_0_h28, disp_addsshift_0_h29, disp_addsshift_0_h30, disp_addsshift_0_h31, disp_addsshift_0_h32, disp_addsshift_0_h33, disp_addsshift_0_h34, disp_addsshift_0_h35, disp_addsshift_0_h36, disp_addsshift_0_h37, disp_addsshift_0_h38, disp_addsshift_0_h39, disp_addsshift_0_h40, disp_addsshift_0_h41, disp_addsshift_0_h41b, disp_addsshift_0_h42, disp_addsshift_0_h42b, disp_addsshift_0_h43, disp_addsshift_0_h43b, disp_addsshift_0_h44, disp_addsshift_0_h44b, disp_addsshift_0_h45, disp_addsshift_0_h46, disp_addsshift_0_h47, disp_addsshift_0_h48, disp_addsshift_0_h49, disp_addsshift_0_h50, disp_addsshift_0_h51, disp_addsshift_0_h52, disp_addsshift_0_h53, disp_addsshift_0_h54, disp_addsshift_0_h55, disp_addsshift_0_h56, disp_addsshift_0_h57, disp_addsshift_0_h58, disp_addsshift_0_h59, disp_addsshift_0_h60, disp_addsshift_0_h61, disp_addsshift_0_h62, disp_addsshift_0_h63, disp_addsshift_0_h64, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcReg
  simp (config := {decide := true}) only [disp_addsshift_0_h0, disp_addsshift_0_h1, disp_addsshift_0_h2, disp_addsshift_0_h3, disp_addsshift_0_h4, disp_addsshift_0_h5, disp_addsshift_0_h6, disp_addsshift_0_h7, disp_addsshift_0_h8, disp_addsshift_0_h9, disp_addsshift_0_h10, disp_addsshift_0_h11, disp_addsshift_0_h11b, disp_addsshift_0_h12, disp_addsshift_0_h12b, disp_addsshift_0_h13, disp_addsshift_0_h13b, disp_addsshift_0_h14, disp_addsshift_0_h14b, disp_addsshift_0_h15, disp_addsshift_0_h15b, disp_addsshift_0_h16, disp_addsshift_0_h16b, disp_addsshift_0_h17, disp_addsshift_0_h17b, disp_addsshift_0_h18, disp_addsshift_0_h18b, disp_addsshift_0_h19, disp_addsshift_0_h20, disp_addsshift_0_h21, disp_addsshift_0_h22, disp_addsshift_0_h23, disp_addsshift_0_h24, disp_addsshift_0_h25, disp_addsshift_0_h26, disp_addsshift_0_h27, disp_addsshift_0_h28, disp_addsshift_0_h29, disp_addsshift_0_h30, disp_addsshift_0_h31, disp_addsshift_0_h32, disp_addsshift_0_h33, disp_addsshift_0_h34, disp_addsshift_0_h35, disp_addsshift_0_h36, disp_addsshift_0_h37, disp_addsshift_0_h38, disp_addsshift_0_h39, disp_addsshift_0_h40, disp_addsshift_0_h41, disp_addsshift_0_h41b, disp_addsshift_0_h42, disp_addsshift_0_h42b, disp_addsshift_0_h43, disp_addsshift_0_h43b, disp_addsshift_0_h44, disp_addsshift_0_h44b, disp_addsshift_0_h45, disp_addsshift_0_h46, disp_addsshift_0_h47, disp_addsshift_0_h48, disp_addsshift_0_h49, disp_addsshift_0_h50, disp_addsshift_0_h51, disp_addsshift_0_h52, disp_addsshift_0_h53, disp_addsshift_0_h54, disp_addsshift_0_h55, disp_addsshift_0_h56, disp_addsshift_0_h57, disp_addsshift_0_h58, disp_addsshift_0_h59, disp_addsshift_0_h60, disp_addsshift_0_h61, disp_addsshift_0_h62, disp_addsshift_0_h63, disp_addsshift_0_h64, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms disp_addsshift_0
end ArmBridge.Disp
