import N1D226.CsetEq32.Encoding
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace N1D226.CsetEq32.Dispatch
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 9 5) : BitVec 5) = 31#5 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h1 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 11 10) : BitVec 2) = 1#2 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h2 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 11 10) : BitVec 2) = 1#2 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h3 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 11 10) : BitVec 2) = 1#2 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h4 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 12 10) : BitVec 3) = 5#3 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h5 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 12 10) : BitVec 3) = 5#3 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h6 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 12 10) : BitVec 3) = 5#3 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h7 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 12 10) : BitVec 3) = 5#3 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h8 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 12 10) : BitVec 3) = 5#3 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h9 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 12 10) : BitVec 3) = 5#3 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h10 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 12 10) : BitVec 3) = 5#3 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h11 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 12 10) : BitVec 3) = 5#3 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h12 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 13 10) : BitVec 4) = 5#4 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h13 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 14 10) : BitVec 5) = 5#5 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h14 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h15 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h16 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h17 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h18 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h19 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h20 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h21 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h22 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h23 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h24 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h25 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h26 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h27 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h28 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 10) : BitVec 6) = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h29 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 12) : BitVec 4) = 1#4 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h30 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 12) : BitVec 4) = 1#4 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h31 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 15) : BitVec 1) = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h32 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 15) : BitVec 1) = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h33 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h34 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 21 21) : BitVec 1) = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h35 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 25 25) : BitVec 1) = 1#1 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h36 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 27 25) : BitVec 3) = 5#3 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h37 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 27 27) : BitVec 1) = 1#1 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h38 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h39 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h40 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h41 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 28 25) : BitVec 4) = 13#4 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h42 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 28 26) : BitVec 3) = 6#3 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h43 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 28 26) : BitVec 3) = 6#3 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h44 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 10) : BitVec 21) = 436165#21 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h45 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 10) : BitVec 21) = 436165#21 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h46 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 10) : BitVec 21) = 436165#21 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h47 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 10) : BitVec 21) = 436165#21 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h48 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 10) : BitVec 21) = 436165#21 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h49 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 10) : BitVec 21) = 436165#21 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h50 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 10) : BitVec 21) = 436165#21 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h51 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 11) : BitVec 20) = 218082#20 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h52 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h53 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h54 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h55 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h56 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h57 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h58 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h59 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h60 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h61 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h62 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h63 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h64 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h65 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 21) : BitVec 10) = 212#10 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h66 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h67 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h68 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h69 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h70 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h71 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h72 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h73 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 24) : BitVec 7) = 26#7 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h74 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 10) : BitVec 22) = 436165#22 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h75 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 11) : BitVec 21) = 218082#21 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h76 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 14) : BitVec 18) = 27260#18 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h77 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 15) : BitVec 17) = 13630#17 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h78 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 21) : BitVec 11) = 212#11 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h79 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 21) : BitVec 11) = 212#11 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h80 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 21) : BitVec 11) = 212#11 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h81 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 21) : BitVec 11) = 212#11 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h82 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 21) : BitVec 11) = 212#11 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h83 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 21) : BitVec 11) = 212#11 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h84 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 21) : BitVec 11) = 212#11 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h85 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 31) : BitVec 1) = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h86 (Rd : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 31) : BitVec 1) = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h87 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 0 5 = Rd := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    bv_field

theorem dispatch_h88 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 5 5 = 31#5 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h89 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 10 1 = 1#1 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h90 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 10 2 = 1#2 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h91 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 10 3 = 5#3 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h92 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 10 5 = 5#5 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h93 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 10 6 = 5#6 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h94 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 12 1 = 1#1 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h95 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 12 4 = 1#4 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h96 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 13 1 = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h97 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 13 3 = 0#3 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h98 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 14 1 = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h99 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 1 = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h100 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 15 6 = 62#6 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h101 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 16 5 = 31#5 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h102 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 21 1 = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h103 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 22 2 = 2#2 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h104 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 23 1 = 1#1 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h105 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 29 1 = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h106 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 29 2 = 0#2 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h107 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 30 1 = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h108 (Rd : BitVec 5) :
    BitVec.slice (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) 31 1 = 0#1 := by
    unfold N1D226.CsetEq32.Encoding.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch (pc : Int) (Rd : BitVec 5) :
    __DecodeA64 (real := real) pc (N1D226.CsetEq32.Encoding.word 13957311#27 Rd) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 188))
      if c = true then (do writeReg Register.SEE 188; decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 1#4 31#5 0#1 0#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h98, dispatch_h99, dispatch_h100, dispatch_h101, dispatch_h102, dispatch_h103, dispatch_h104, dispatch_h105, dispatch_h106, dispatch_h107, dispatch_h108, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcReg
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_h55, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h84, dispatch_h85, dispatch_h86, dispatch_h87, dispatch_h88, dispatch_h89, dispatch_h90, dispatch_h91, dispatch_h92, dispatch_h93, dispatch_h94, dispatch_h95, dispatch_h96, dispatch_h97, dispatch_h98, dispatch_h99, dispatch_h100, dispatch_h101, dispatch_h102, dispatch_h103, dispatch_h104, dispatch_h105, dispatch_h106, dispatch_h107, dispatch_h108, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch
end N1D226.CsetEq32.Dispatch
