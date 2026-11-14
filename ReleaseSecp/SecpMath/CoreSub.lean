-- Connect pure limb arithmetic to the frozen value-layer operations.
-- This does not assert a native instruction or whole Sail run.
import ArmCertValue.Core
import SecpMath.LimbSub

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace SecpMath
open ArmCertValue

theorem sbc3_limb (x y : BitVec 64) (borrow : Nat) (hc : borrow ≤ 1) :
    (Op.sbc3.eval [x, y, BitVec.ofNat 64 (1 - borrow)]).toNat =
      limbDifference x.toNat y.toNat borrow := by
  have hx : x.toNat < limbRadix := x.isLt
  have hy : y.toNat < limbRadix := y.isLt
  have hn : (BitVec.ofNat 64 (1 - borrow)).toNat = 1 - borrow :=
    Nat.mod_eq_of_lt (by omega)
  have he : (Op.sbc3.eval [x, y, BitVec.ofNat 64 (1 - borrow)]).toNat =
      (x.toNat + (limbRadix - 1 - y.toNat) + (1 - borrow)) % limbRadix := by
    change (x + ~~~y + BitVec.ofNat 64 (1 - borrow)).toNat = _
    simp only [BitVec.toNat_add, BitVec.toNat_not, hn]
    simp only [limbRadix, Nat.mod_add_mod]
  rw [he]
  unfold limbDifference
  split
  · have hs : x.toNat + (limbRadix - 1 - y.toNat) + (1 - borrow) =
        (x.toNat - (y.toNat + borrow)) + limbRadix := by omega
    rw [hs]
    simp [Nat.mod_eq_of_lt (show x.toNat - (y.toNat + borrow) < limbRadix by omega)]
  · rw [Nat.mod_eq_of_lt (show x.toNat + (limbRadix - 1 - y.toNat) + (1 - borrow) < limbRadix by omega)]
    omega

theorem sbc3C_borrow (x y : BitVec 64) (borrow : Nat) (hc : borrow ≤ 1) :
    (Op.sbc3C.eval [x, y, BitVec.ofNat 64 (1 - borrow)]).toNat =
      1 - limbBorrow x.toNat y.toNat borrow := by
  have hx : x.toNat < limbRadix := x.isLt
  have hy : y.toNat < limbRadix := y.isLt
  have hn : (BitVec.ofNat 64 (1 - borrow)).toNat = 1 - borrow :=
    Nat.mod_eq_of_lt (by omega)
  have he : (limbRadix ≤ x.toNat + (limbRadix - 1 - y.toNat) + (1 - borrow)) ↔
      y.toNat + borrow ≤ x.toNat := by omega
  change (b01 (decide (2 ^ 64 ≤ x.toNat + (~~~y).toNat +
    (BitVec.ofNat 64 (1 - borrow)).toNat))).toNat = _
  simp only [BitVec.toNat_not, hn]
  change (b01 (decide (limbRadix ≤ x.toNat + (limbRadix - 1 - y.toNat) + (1 - borrow)))).toNat = _
  simp only [he]
  by_cases h : y.toNat + borrow ≤ x.toNat <;> simp [b01, limbBorrow, h]

theorem correction_constant :
    Op.orr.eval [977#64, 4294967296#64] = BitVec.ofNat 64 correction := by
  change (977#64 ||| 4294967296#64) = BitVec.ofNat 64 correction
  decide

theorem correction_select (n z v : BitVec 64) (borrow : Nat) (hc : borrow ≤ 1) :
    (Op.cselc 3#4).eval [n, z, BitVec.ofNat 64 (1 - borrow), v,
      BitVec.ofNat 64 correction, 0#64] =
        BitVec.ofNat 64 (if borrow = 0 then 0 else correction) := by
  change (if condHolds 3#4 n z (BitVec.ofNat 64 (1 - borrow)) v then
    BitVec.ofNat 64 correction else 0#64) = _
  have h : borrow = 0 ∨ borrow = 1 := by omega
  rcases h with h | h <;> subst borrow <;> simp [condHolds]

theorem sbc3C_word (x y : BitVec 64) (borrow : Nat) (hc : borrow ≤ 1) :
    Op.sbc3C.eval [x, y, BitVec.ofNat 64 (1 - borrow)] =
      BitVec.ofNat 64 (1 - limbBorrow x.toNat y.toNat borrow) := by
  apply BitVec.eq_of_toNat_eq
  rw [sbc3C_borrow x y borrow hc]
  exact (Nat.mod_eq_of_lt (by omega : 1 - limbBorrow x.toNat y.toNat borrow < 2 ^ 64)).symm

structure LimbWords where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64

def LimbWords.value (x : LimbWords) : Nat := pack4 x.w0.toNat x.w1.toNat x.w2.toNat x.w3.toNat

theorem LimbWords.value_lt (x : LimbWords) : x.value < radix :=
  pack4_lt _ _ _ _ x.w0.isLt x.w1.isLt x.w2.isLt x.w3.isLt

/-- Exact frozen Core operations for the four subtraction instructions.
    Memory/table identities and native execution are not assumed here. -/
def coreChain4 (x y : LimbWords) : LimbWords × BitVec 64 :=
  let d0 := Op.sbc3.eval [x.w0, y.w0, 1#64]
  let c0 := Op.sbc3C.eval [x.w0, y.w0, 1#64]
  let d1 := Op.sbc3.eval [x.w1, y.w1, c0]
  let c1 := Op.sbc3C.eval [x.w1, y.w1, c0]
  let d2 := Op.sbc3.eval [x.w2, y.w2, c1]
  let c2 := Op.sbc3C.eval [x.w2, y.w2, c1]
  let d3 := Op.sbc3.eval [x.w3, y.w3, c2]
  let c3 := Op.sbc3C.eval [x.w3, y.w3, c2]
  (⟨d0,d1,d2,d3⟩, c3)

theorem coreChain4_subtract4 (x y : LimbWords) :
    ((coreChain4 x y).1.value, 1 - (coreChain4 x y).2.toNat) =
      subtract4 x.w0.toNat x.w1.toNat x.w2.toNat x.w3.toNat
        y.w0.toNat y.w1.toNat y.w2.toNat y.w3.toNat := by
  let b0 := limbBorrow x.w0.toNat y.w0.toNat 0
  let b1 := limbBorrow x.w1.toNat y.w1.toNat b0
  let b2 := limbBorrow x.w2.toNat y.w2.toNat b1
  let b3 := limbBorrow x.w3.toNat y.w3.toNat b2
  have h0 : b0 ≤ 1 := limbBorrow_le_one ..
  have h1 : b1 ≤ 1 := limbBorrow_le_one ..
  have h2 : b2 ≤ 1 := limbBorrow_le_one ..
  have h3 : b3 ≤ 1 := limbBorrow_le_one ..
  have c0 := sbc3C_word x.w0 y.w0 0 (by omega)
  have c1 := sbc3C_word x.w1 y.w1 b0 h0
  have c2 := sbc3C_word x.w2 y.w2 b1 h1
  have c3 := sbc3C_borrow x.w3 y.w3 b2 h2
  have d0 := sbc3_limb x.w0 y.w0 0 (by omega)
  have d1 := sbc3_limb x.w1 y.w1 b0 h0
  have d2 := sbc3_limb x.w2 y.w2 b1 h1
  have d3 := sbc3_limb x.w3 y.w3 b2 h2
  change (Op.sbc3C.eval [x.w0,y.w0,1#64]) = BitVec.ofNat 64 (1-b0) at c0
  change (Op.sbc3C.eval [x.w1,y.w1,BitVec.ofNat 64 (1-b0)]) = BitVec.ofNat 64 (1-b1) at c1
  change (Op.sbc3C.eval [x.w2,y.w2,BitVec.ofNat 64 (1-b1)]) = BitVec.ofNat 64 (1-b2) at c2
  change (Op.sbc3C.eval [x.w3,y.w3,BitVec.ofNat 64 (1-b2)]).toNat = 1-b3 at c3
  simp only [coreChain4, c0, c1, c2, LimbWords.value, d0, d1, d2, d3, c3]
  change (_, 1 - (1 - b3)) = (_, b3)
  congr 1
  omega

theorem coreChain4_correct (x y : LimbWords) :
    (coreChain4 x y).1.value = ((radix - y.value) + x.value) % radix ∧
      1 - (coreChain4 x y).2.toNat = (if y.value ≤ x.value then 0 else 1) := by
  have pure := subtract4_correct x.w0.toNat x.w1.toNat x.w2.toNat x.w3.toNat
    y.w0.toNat y.w1.toNat y.w2.toNat y.w3.toNat
    x.w0.isLt x.w1.isLt x.w2.isLt x.w3.isLt y.w0.isLt y.w1.isLt y.w2.isLt y.w3.isLt
  have eqv := coreChain4_subtract4 x y
  have values := congrArg Prod.fst eqv
  have borrows := congrArg Prod.snd eqv
  exact ⟨values.trans pure.2.2, borrows.trans pure.2.1⟩

theorem sbc3C_le_one (x y carry : BitVec 64) :
    (Op.sbc3C.eval [x,y,carry]).toNat ≤ 1 := by
  change (b01 _).toNat ≤ 1
  unfold b01
  split <;> decide

theorem coreChain4_flag (x y : LimbWords) : (coreChain4 x y).2.toNat ≤ 1 :=
  sbc3C_le_one ..

def correctionWords (borrow : Bool) : LimbWords :=
  ⟨if borrow then BitVec.ofNat 64 correction else 0#64, 0#64, 0#64, 0#64⟩

theorem correctionWords_value (borrow : Bool) :
    (correctionWords borrow).value = if borrow then correction else 0 := by
  have hc : correction < 2 ^ 64 := by decide
  cases borrow <;> simp [correctionWords, LimbWords.value, pack4, Nat.mod_eq_of_lt hc]

/-- The two four-instruction Core chains and conditional borrow correction.
    The compiled table, input-byte assembly and native memory/run joins remain separate. -/
def coreSub4 (x y : LimbWords) : LimbWords :=
  let first := coreChain4 x y
  (coreChain4 first.1 (correctionWords (first.2 == 0#64))).1

theorem coreSub4_eq_core (x y : LimbWords) (hx : x.value < modulus) (hy : y.value < modulus) :
    (coreSub4 x y).value = subCore modulus x.value y.value := by
  have first := coreChain4_correct x y
  have flag := coreChain4_flag x y
  have second := (coreChain4_correct (coreChain4 x y).1
    (correctionWords ((coreChain4 x y).2 == 0#64))).1
  have target := wrappedSub_eq_core radix correction modulus x.value y.value
    radix_split modulus_pos correction_pos hx hy
  rw [← target]
  change (coreChain4 (coreChain4 x y).1 (correctionWords ((coreChain4 x y).2 == 0#64))).1.value = _
  rw [second, correctionWords_value, first.1]
  by_cases h : y.value ≤ x.value
  · have hf : (coreChain4 x y).2.toNat = 1 := by
      have := first.2
      simp only [h, ↓reduceIte] at this
      omega
    have hn : (coreChain4 x y).2 ≠ 0#64 := by
      intro hz
      rw [hz] at hf
      contradiction
    simp [hn, wrappedSub, h]
  · have hf : (coreChain4 x y).2.toNat = 0 := by
      have := first.2
      simp only [h, ↓reduceIte] at this
      omega
    have hz : (coreChain4 x y).2 = 0#64 := BitVec.eq_of_toNat_eq hf
    simp [hz, wrappedSub, h]

theorem coreSub4_correct (x y : LimbWords) (hx : x.value < modulus) (hy : y.value < modulus) :
    (coreSub4 x y).value < modulus ∧ ((coreSub4 x y).value : Int) =
      ((x.value : Int) - (y.value : Int)) % (modulus : Int) := by
  rw [coreSub4_eq_core x y hx hy]
  exact ⟨subCore_lt modulus x.value y.value hx hy, subCore_int modulus x.value y.value hx hy⟩

#print axioms sbc3_limb
#print axioms sbc3C_borrow
#print axioms correction_constant
#print axioms correction_select
#print axioms sbc3C_word
#print axioms coreChain4_subtract4
#print axioms coreChain4_correct
#print axioms coreChain4_flag
#print axioms correctionWords_value
#print axioms coreSub4_eq_core
#print axioms coreSub4_correct

end SecpMath
