import N1D226.Extr64Generic.Encoding
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace N1D226.Extr64Generic.Dispatch
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h1 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 25 25) : BitVec 1) = 1#1 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h2 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 27 25) : BitVec 3) = 1#3 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h3 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 27 27) : BitVec 1) = 0#1 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h4 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 28 24) : BitVec 5) = 19#5 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h5 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h6 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h7 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h8 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 28 25) : BitVec 4) = 9#4 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h9 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 28 26) : BitVec 3) = 4#3 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h10 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 28 26) : BitVec 3) = 4#3 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h11 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 18) : BitVec 13) = 1136#13) := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h11b (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 18) : BitVec 13) == 1136#13) = false := by
  have := dispatch_h11 Rm imms Rn Rd
  simpa using this

theorem dispatch_h12 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 18) : BitVec 13) = 1137#13) := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h12b (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 18) : BitVec 13) == 1137#13) = false := by
  have := dispatch_h12 Rm imms Rn Rd
  simpa using this

theorem dispatch_h13 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 18) : BitVec 13) = 1138#13) := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h13b (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 18) : BitVec 13) == 1138#13) = false := by
  have := dispatch_h13 Rm imms Rn Rd
  simpa using this

theorem dispatch_h14 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 18) : BitVec 13) = 1139#13) := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h14b (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 18) : BitVec 13) == 1139#13) = false := by
  have := dispatch_h14 Rm imms Rn Rd
  simpa using this

theorem dispatch_h15 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h16 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h17 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h18 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h19 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h20 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h21 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h22 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h23 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h24 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h25 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h26 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h27 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h28 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h29 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 23) : BitVec 8) = 39#8 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h30 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 31 22) : BitVec 10) = 591#10 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h31 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 31 22) : BitVec 10) = 591#10 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h32 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h33 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 31 31) : BitVec 1) = 1#1 := by
    unfold N1D226.Extr64Generic.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h34 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 0 5 = Rd := by
    unfold N1D226.Extr64Generic.Encoding.word BitVec.slice
    bv_field

theorem dispatch_h35 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 5 5 = Rn := by
    unfold N1D226.Extr64Generic.Encoding.word BitVec.slice
    bv_field

theorem dispatch_h36 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 10 6 = imms := by
    unfold N1D226.Extr64Generic.Encoding.word BitVec.slice
    bv_field

theorem dispatch_h37 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 16 5 = Rm := by
    unfold N1D226.Extr64Generic.Encoding.word BitVec.slice
    bv_field

theorem dispatch_h38 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 21 2 = 2#2 := by
    unfold N1D226.Extr64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h39 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 22 1 = 1#1 := by
    unfold N1D226.Extr64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h40 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 29 1 = 0#1 := by
    unfold N1D226.Extr64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h41 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 29 2 = 0#2 := by
    unfold N1D226.Extr64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h42 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 30 1 = 0#1 := by
    unfold N1D226.Extr64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h43 (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    BitVec.slice (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) 31 1 = 1#1 := by
    unfold N1D226.Extr64Generic.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch (pc : Int) (Rm : BitVec 5) (imms : BitVec 6) (Rn : BitVec 5) (Rd : BitVec 5) :
    __DecodeA64 (real := real) pc (N1D226.Extr64Generic.Encoding.word 1182#11 Rm imms Rn Rd) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 206))
      if c = true then (do writeReg Register.SEE 206; decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate Rd Rn imms Rm 1#1 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcImm
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch
end N1D226.Extr64Generic.Dispatch
