import CryptoBridge.SubsImmDecode
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace ArmBridge.Disp
variable (real : Type) [Sail.SailReal real]

theorem disp_subsimm_0_h0 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 25 25) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsimm_0_h1 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 27 25) : BitVec 3) = 0#3 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h2 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 27 27) : BitVec 1) = 0#1 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsimm_0_h3 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 28 24) : BitVec 5) = 17#5 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h4 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 28 25) : BitVec 4) = 8#4 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h5 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 28 25) : BitVec 4) = 8#4 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h6 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 28 25) : BitVec 4) = 8#4 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h7 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 28 25) : BitVec 4) = 8#4 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h8 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 28 26) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h9 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 28 26) : BitVec 3) = 4#3 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h10 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 18) : BitVec 13) = 1136#13) := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsimm_0_h10b (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 18) : BitVec 13) == 1136#13) = false := by
  have := disp_subsimm_0_h10 imm12 Rn Rd
  simpa using this

theorem disp_subsimm_0_h11 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 18) : BitVec 13) = 1137#13) := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsimm_0_h11b (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 18) : BitVec 13) == 1137#13) = false := by
  have := disp_subsimm_0_h11 imm12 Rn Rd
  simpa using this

theorem disp_subsimm_0_h12 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 18) : BitVec 13) = 1138#13) := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsimm_0_h12b (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 18) : BitVec 13) == 1138#13) = false := by
  have := disp_subsimm_0_h12 imm12 Rn Rd
  simpa using this

theorem disp_subsimm_0_h13 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 18) : BitVec 13) = 1139#13) := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_subsimm_0_h13b (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 18) : BitVec 13) == 1139#13) = false := by
  have := disp_subsimm_0_h13 imm12 Rn Rd
  simpa using this

theorem disp_subsimm_0_h14 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h15 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h16 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h17 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h18 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h19 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h20 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h21 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h22 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h23 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h24 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h25 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h26 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h27 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h28 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 23) : BitVec 8) = 226#8 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h29 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 31 22) : BitVec 10) = 964#10 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h30 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 31 22) : BitVec 10) = 964#10 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_subsimm_0_h31 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsimm_0_h32 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsimm_0_h33 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 0 5 = Rd := by
    unfold CryptoBridge.AddSubImm.addSubImmWord BitVec.slice
    bv_field

theorem disp_subsimm_0_h34 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 5 5 = Rn := by
    unfold CryptoBridge.AddSubImm.addSubImmWord BitVec.slice
    bv_field

theorem disp_subsimm_0_h35 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 10 12 = imm12 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord BitVec.slice
    bv_field

theorem disp_subsimm_0_h36 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 22 1 = 0#1 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsimm_0_h37 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 29 1 = 1#1 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsimm_0_h38 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 29 2 = 3#2 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_subsimm_0_h39 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 30 1 = 1#1 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsimm_0_h40 (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) 31 1 = 1#1 := by
    unfold CryptoBridge.AddSubImm.addSubImmWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_subsimm_0 (pc : Int) (imm12 : BitVec 12) (Rn : BitVec 5) (Rd : BitVec 5) :
    __DecodeA64 (real := real) pc (CryptoBridge.AddSubImm.addSubImmWord 1#1 1#1 1#1 0#1 imm12 Rn Rd) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 21))
      if c = true then (do writeReg Register.SEE 21; decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 0#1 1#1 1#1 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [disp_subsimm_0_h0, disp_subsimm_0_h1, disp_subsimm_0_h2, disp_subsimm_0_h3, disp_subsimm_0_h4, disp_subsimm_0_h5, disp_subsimm_0_h6, disp_subsimm_0_h7, disp_subsimm_0_h8, disp_subsimm_0_h9, disp_subsimm_0_h10, disp_subsimm_0_h10b, disp_subsimm_0_h11, disp_subsimm_0_h11b, disp_subsimm_0_h12, disp_subsimm_0_h12b, disp_subsimm_0_h13, disp_subsimm_0_h13b, disp_subsimm_0_h14, disp_subsimm_0_h15, disp_subsimm_0_h16, disp_subsimm_0_h17, disp_subsimm_0_h18, disp_subsimm_0_h19, disp_subsimm_0_h20, disp_subsimm_0_h21, disp_subsimm_0_h22, disp_subsimm_0_h23, disp_subsimm_0_h24, disp_subsimm_0_h25, disp_subsimm_0_h26, disp_subsimm_0_h27, disp_subsimm_0_h28, disp_subsimm_0_h29, disp_subsimm_0_h30, disp_subsimm_0_h31, disp_subsimm_0_h32, disp_subsimm_0_h33, disp_subsimm_0_h34, disp_subsimm_0_h35, disp_subsimm_0_h36, disp_subsimm_0_h37, disp_subsimm_0_h38, disp_subsimm_0_h39, disp_subsimm_0_h40, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcImm
  simp (config := {decide := true}) only [disp_subsimm_0_h0, disp_subsimm_0_h1, disp_subsimm_0_h2, disp_subsimm_0_h3, disp_subsimm_0_h4, disp_subsimm_0_h5, disp_subsimm_0_h6, disp_subsimm_0_h7, disp_subsimm_0_h8, disp_subsimm_0_h9, disp_subsimm_0_h10, disp_subsimm_0_h10b, disp_subsimm_0_h11, disp_subsimm_0_h11b, disp_subsimm_0_h12, disp_subsimm_0_h12b, disp_subsimm_0_h13, disp_subsimm_0_h13b, disp_subsimm_0_h14, disp_subsimm_0_h15, disp_subsimm_0_h16, disp_subsimm_0_h17, disp_subsimm_0_h18, disp_subsimm_0_h19, disp_subsimm_0_h20, disp_subsimm_0_h21, disp_subsimm_0_h22, disp_subsimm_0_h23, disp_subsimm_0_h24, disp_subsimm_0_h25, disp_subsimm_0_h26, disp_subsimm_0_h27, disp_subsimm_0_h28, disp_subsimm_0_h29, disp_subsimm_0_h30, disp_subsimm_0_h31, disp_subsimm_0_h32, disp_subsimm_0_h33, disp_subsimm_0_h34, disp_subsimm_0_h35, disp_subsimm_0_h36, disp_subsimm_0_h37, disp_subsimm_0_h38, disp_subsimm_0_h39, disp_subsimm_0_h40, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms disp_subsimm_0
end ArmBridge.Disp
