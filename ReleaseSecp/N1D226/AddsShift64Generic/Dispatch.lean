import N1D226.AddsShift64Generic.Encoding
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace N1D226.AddsShift64Generic.Dispatch
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h1 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h2 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 25 25) : BitVec 1) = 1#1 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h3 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 27 25) : BitVec 3) = 5#3 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h4 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 27 27) : BitVec 1) = 1#1 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h5 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h6 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h7 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h8 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 28 25) : BitVec 4) = 5#4 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h9 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 28 26) : BitVec 3) = 2#3 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h10 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 28 26) : BitVec 3) = 2#3 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h11 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486848#21) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h11b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486848#21) = false := by
  have := dispatch_h11 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h12 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486849#21) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h12b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486849#21) = false := by
  have := dispatch_h12 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h13 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486852#21) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h13b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486852#21) = false := by
  have := dispatch_h13 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h14 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486853#21) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h14b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486853#21) = false := by
  have := dispatch_h14 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h15 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486854#21) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h15b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486854#21) = false := by
  have := dispatch_h15 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h16 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486855#21) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h16b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486855#21) = false := by
  have := dispatch_h16 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h17 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) = 1486856#21) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h17b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 10) : BitVec 21) == 1486856#21) = false := by
  have := dispatch_h17 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h18 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 11) : BitVec 20) = 743425#20) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 11) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h18b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 11) : BitVec 20) == 743425#20) = false := by
  have := dispatch_h18 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h19 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h20 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h21 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h22 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h23 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h24 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h25 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h26 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h27 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h28 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h29 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h30 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h31 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h32 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 21) : BitVec 10) = 344#10 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h33 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h34 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h35 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h36 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h37 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h38 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h39 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h40 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 24) : BitVec 7) = 43#7 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h41 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 10) : BitVec 22) = 3584002#22) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h41b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 10) : BitVec 22) == 3584002#22) = false := by
  have := dispatch_h41 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h42 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 11) : BitVec 21) = 1792040#21) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 11) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h42b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 11) : BitVec 21) == 1792040#21) = false := by
  have := dispatch_h42 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h43 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 14) : BitVec 18) = 224004#18) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h43b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 14) : BitVec 18) == 224004#18) = false := by
  have := dispatch_h43 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h44 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 15) : BitVec 17) = 29696#17) := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h44b (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 15) : BitVec 17) == 29696#17) = false := by
  have := dispatch_h44 Rm imm6 Rn Rd
  simpa using this

theorem dispatch_h45 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h46 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h47 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h48 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h49 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h50 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h51 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 21) : BitVec 11) = 1368#11 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h52 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h53 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold N1D226.AddsShift64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h54 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 0 5 = Rd := by
    unfold N1D226.AddsShift64Generic.Encoding.word BitVec.slice
    bv_field

theorem dispatch_h55 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 5 5 = Rn := by
    unfold N1D226.AddsShift64Generic.Encoding.word BitVec.slice
    bv_field

theorem dispatch_h56 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 10 6 = imm6 := by
    unfold N1D226.AddsShift64Generic.Encoding.word BitVec.slice
    bv_field

theorem dispatch_h57 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 16 5 = Rm := by
    unfold N1D226.AddsShift64Generic.Encoding.word BitVec.slice
    bv_field

theorem dispatch_h58 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 21 1 = 0#1 := by
    unfold N1D226.AddsShift64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h59 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 22 2 = 0#2 := by
    unfold N1D226.AddsShift64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h60 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 23 1 = 0#1 := by
    unfold N1D226.AddsShift64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h61 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 29 1 = 1#1 := by
    unfold N1D226.AddsShift64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h62 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 29 2 = 1#2 := by
    unfold N1D226.AddsShift64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h63 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 30 1 = 0#1 := by
    unfold N1D226.AddsShift64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h64 (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) 31 1 = 1#1 := by
    unfold N1D226.AddsShift64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch (pc : Int) (Rm : BitVec 5) (imm6 : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    __DecodeA64 (real := real) pc (N1D226.AddsShift64Generic.Encoding.word 1368#11 Rm imm6 Rn Rd) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 15))
      if c = true then (do writeReg Register.SEE 15; decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm 0#2 1#1 0#1 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcReg
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch
end N1D226.AddsShift64Generic.Dispatch
