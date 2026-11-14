import N1D226.CmpShiftZero64.Encoding
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace N1D226.CmpShiftZero64.Dispatch
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 4 0) : BitVec 5) = 31#5 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h1 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 4 4) : BitVec 1) = 1#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h2 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 21 21) : BitVec 1) = 0#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h3 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 21 21) : BitVec 1) = 0#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h4 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 25 25) : BitVec 1) = 1#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h5 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 27 25) : BitVec 3) = 5#3 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h6 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 27 27) : BitVec 1) = 1#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h7 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 28 25) : BitVec 4) = 5#4 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h8 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 28 25) : BitVec 4) = 5#4 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h9 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 28 25) : BitVec 4) = 5#4 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h10 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 28 25) : BitVec 4) = 5#4 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h11 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 28 26) : BitVec 3) = 2#3 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h12 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 28 26) : BitVec 3) = 2#3 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h13 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) = 1486848#21) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h13b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) == 1486848#21) = false := by
  have := dispatch_h13 imm6 Rn
  simpa using this

theorem dispatch_h14 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) = 1486849#21) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h14b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) == 1486849#21) = false := by
  have := dispatch_h14 imm6 Rn
  simpa using this

theorem dispatch_h15 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) = 1486852#21) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h15b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) == 1486852#21) = false := by
  have := dispatch_h15 imm6 Rn
  simpa using this

theorem dispatch_h16 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) = 1486853#21) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h16b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) == 1486853#21) = false := by
  have := dispatch_h16 imm6 Rn
  simpa using this

theorem dispatch_h17 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) = 1486854#21) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h17b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) == 1486854#21) = false := by
  have := dispatch_h17 imm6 Rn
  simpa using this

theorem dispatch_h18 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) = 1486855#21) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h18b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) == 1486855#21) = false := by
  have := dispatch_h18 imm6 Rn
  simpa using this

theorem dispatch_h19 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) = 1486856#21) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h19b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 10) : BitVec 21) == 1486856#21) = false := by
  have := dispatch_h19 imm6 Rn
  simpa using this

theorem dispatch_h20 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 11) : BitVec 20) = 743425#20) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h20b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 11) : BitVec 20) == 743425#20) = false := by
  have := dispatch_h20 imm6 Rn
  simpa using this

theorem dispatch_h21 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h22 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h23 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h24 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h25 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h26 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h27 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h28 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h29 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h30 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h31 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h32 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h33 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h34 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 21) : BitVec 10) = 856#10 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h35 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 24) : BitVec 7) = 107#7 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h36 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 24) : BitVec 7) = 107#7 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h37 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 24) : BitVec 7) = 107#7 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h38 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 24) : BitVec 7) = 107#7 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h39 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 24) : BitVec 7) = 107#7 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h40 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 24) : BitVec 7) = 107#7 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h41 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 24) : BitVec 7) = 107#7 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h42 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 24) : BitVec 7) = 107#7 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h43 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 10) : BitVec 22) = 3584002#22) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h43b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 10) : BitVec 22) == 3584002#22) = false := by
  have := dispatch_h43 imm6 Rn
  simpa using this

theorem dispatch_h44 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 11) : BitVec 21) = 1792040#21) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h44b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 11) : BitVec 21) == 1792040#21) = false := by
  have := dispatch_h44 imm6 Rn
  simpa using this

theorem dispatch_h45 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 14) : BitVec 18) = 224004#18) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h45b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 14) : BitVec 18) == 224004#18) = false := by
  have := dispatch_h45 imm6 Rn
  simpa using this

theorem dispatch_h46 (imm6 : BitVec 6) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 15) : BitVec 17) = 29696#17) := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h46b (imm6 : BitVec 6) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 15) : BitVec 17) == 29696#17) = false := by
  have := dispatch_h46 imm6 Rn
  simpa using this

theorem dispatch_h47 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 21) : BitVec 11) = 1880#11 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h48 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 21) : BitVec 11) = 1880#11 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h49 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 21) : BitVec 11) = 1880#11 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h50 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 21) : BitVec 11) = 1880#11 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h51 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 21) : BitVec 11) = 1880#11 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h52 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 21) : BitVec 11) = 1880#11 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h53 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 21) : BitVec 11) = 1880#11 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h54 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 31) : BitVec 1) = 1#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h55 (imm6 : BitVec 6) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 31) : BitVec 1) = 1#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h56 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 0 4 = 15#4 := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h57 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 0 5 = 31#5 := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h58 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 5 5 = Rn := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    bv_field

theorem dispatch_h59 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 10 6 = imm6 := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    bv_field

theorem dispatch_h60 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 16 5 = 31#5 := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h61 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 21 1 = 0#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h62 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 22 2 = 0#2 := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h63 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 23 1 = 0#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h64 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 29 1 = 1#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h65 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 29 2 = 3#2 := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h66 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 30 1 = 1#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h67 (imm6 : BitVec 6) (Rn : BitVec 5) :
    BitVec.slice (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) 31 1 = 1#1 := by
    unfold N1D226.CmpShiftZero64.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch (pc : Int) (imm6 : BitVec 6) (Rn : BitVec 5) :
    __DecodeA64 (real := real) pc (N1D226.CmpShiftZero64.Encoding.word 60191#16 imm6 Rn 31#5) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 17))
      if c = true then (do writeReg Register.SEE 17; decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5 Rn imm6 31#5 0#2 1#1 1#1 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcReg
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch
end N1D226.CmpShiftZero64.Dispatch
