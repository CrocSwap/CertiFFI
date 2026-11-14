-- Frozen Core word products and wide multiply-by-word carry arithmetic.
import SecpMath.Cmul
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
namespace SecpMath.Product
open ArmCertValue SecpMath.Addition

theorem mul_limb (x y : BitVec 64) :
    (Op.mul.eval [x,y]).toNat = (x.toNat*y.toNat)%limbRadix := by
  change (x*y).toNat = _
  exact BitVec.toNat_mul x y

theorem product_upper (x y : BitVec 64) :
    x.toNat*y.toNat ≤ (limbRadix-1)*(limbRadix-1) := by
  have hx : x.toNat ≤ limbRadix-1 := by have bound : x.toNat < limbRadix := x.isLt; omega
  have hy : y.toNat ≤ limbRadix-1 := by have bound : y.toNat < limbRadix := y.isLt; omega
  exact Nat.mul_le_mul hx hy

theorem umulh_limb (x y : BitVec 64) :
    (Op.umulh.eval [x,y]).toNat = (x.toNat*y.toNat)/limbRadix := by
  have bound := product_upper x y
  have below : (x.toNat*y.toNat)/limbRadix < 2^64 := by
    simp only [limbRadix] at *
    omega
  exact Nat.mod_eq_of_lt below

theorem umulh_le (x y : BitVec 64) : (Op.umulh.eval [x,y]).toNat ≤ limbRadix-2 := by
  rw [umulh_limb]
  have bound := product_upper x y
  simp only [limbRadix] at *
  omega

theorem mul_balance (x y : BitVec 64) :
    (Op.mul.eval [x,y]).toNat+limbRadix*(Op.umulh.eval [x,y]).toNat = x.toNat*y.toNat := by
  rw [mul_limb,umulh_limb]
  exact Nat.mod_add_div _ _

theorem add_balance (x y carry : BitVec 64) (hc : carry.toNat ≤ 1) :
    (Op.add3.eval [x,y,carry]).toNat+limbRadix*(Op.carry3.eval [x,y,carry]).toNat =
      x.toNat+y.toNat+carry.toNat := by
  have sum := add3_limb x y carry.toNat hc
  have flag := carry3_limb x y carry.toNat hc
  have same : BitVec.ofNat 64 carry.toNat = carry := by simp
  rw [same] at sum flag
  rw [sum,flag]
  exact limb_balance _ _ _

private theorem scale_pack (c a0 a1 a2 a3 : Nat) :
    c*pack4 a0 a1 a2 a3 = pack4 (c*a0) (c*a1) (c*a2) (c*a3) := by
  simp only [pack4,Nat.mul_add,Nat.mul_left_comm]

#check "CURRENT_DECL packed_product_balance"
theorem packed_product_balance
    (c a0 a1 a2 a3 u0 u1 u2 u3 v0 v1 v2 v3 d1 d2 d3 h c1 c2 c3 : Nat)
    (p0 : u0+limbRadix*v0 = c*a0) (p1 : u1+limbRadix*v1 = c*a1)
    (p2 : u2+limbRadix*v2 = c*a2) (p3 : u3+limbRadix*v3 = c*a3)
    (s1 : d1+limbRadix*c1 = u1+v0) (s2 : d2+limbRadix*c2 = u2+v1+c1)
    (s3 : d3+limbRadix*c3 = u3+v2+c2) (top : h = v3+c3) :
    pack4 u0 d1 d2 d3+radix*h = c*pack4 a0 a1 a2 a3 := by
  rw [scale_pack]
  simp only [pack4,limbRadix,radix] at *
  omega

structure WideWords where
  low : LimbWords
  high : BitVec 64

def WideWords.value (x : WideWords) : Nat := x.low.value+radix*x.high.toNat

def coreMultiplyWord (c : BitVec 64) (x : LimbWords) : WideWords :=
  let u0 := Op.mul.eval [c,x.w0]
  let u1 := Op.mul.eval [c,x.w1]
  let u2 := Op.mul.eval [c,x.w2]
  let u3 := Op.mul.eval [c,x.w3]
  let v0 := Op.umulh.eval [c,x.w0]
  let v1 := Op.umulh.eval [c,x.w1]
  let v2 := Op.umulh.eval [c,x.w2]
  let v3 := Op.umulh.eval [c,x.w3]
  let d1 := Op.add3.eval [u1,v0,0#64]
  let c1 := Op.carry3.eval [u1,v0,0#64]
  let d2 := Op.add3.eval [u2,v1,c1]
  let c2 := Op.carry3.eval [u2,v1,c1]
  let d3 := Op.add3.eval [u3,v2,c2]
  let c3 := Op.carry3.eval [u3,v2,c2]
  let high := Op.add3.eval [v3,0#64,c3]
  ⟨⟨u0,d1,d2,d3⟩,high⟩

private theorem high_add (high carry : BitVec 64)
    (hh : high.toNat ≤ limbRadix-2) (hc : carry.toNat ≤ 1) :
    (Op.add3.eval [high,0#64,carry]).toNat = high.toNat+carry.toNat := by
  have sum := add3_limb high (0#64) carry.toNat hc
  have same : BitVec.ofNat 64 carry.toNat = carry := by simp
  rw [same] at sum
  have below : high.toNat+0+carry.toNat < limbRadix := by
    have positive : 2 ≤ limbRadix := by decide
    omega
  rw [sum]
  exact (Nat.mod_eq_of_lt below).trans (by simp)

#check "CURRENT_DECL coreMultiplyWord_correct"
theorem coreMultiplyWord_correct (c : BitVec 64) (x : LimbWords) :
    (coreMultiplyWord c x).value = c.toNat*x.value := by
  let u0 := Op.mul.eval [c,x.w0]
  let u1 := Op.mul.eval [c,x.w1]
  let u2 := Op.mul.eval [c,x.w2]
  let u3 := Op.mul.eval [c,x.w3]
  let v0 := Op.umulh.eval [c,x.w0]
  let v1 := Op.umulh.eval [c,x.w1]
  let v2 := Op.umulh.eval [c,x.w2]
  let v3 := Op.umulh.eval [c,x.w3]
  let d1 := Op.add3.eval [u1,v0,0#64]
  let c1 := Op.carry3.eval [u1,v0,0#64]
  let d2 := Op.add3.eval [u2,v1,c1]
  let c2 := Op.carry3.eval [u2,v1,c1]
  let d3 := Op.add3.eval [u3,v2,c2]
  let c3 := Op.carry3.eval [u3,v2,c2]
  let high := Op.add3.eval [v3,0#64,c3]
  have s1 := add_balance u1 v0 (0#64) (by decide)
  have s2 := add_balance u2 v1 c1 (carry3_le_one ..)
  have s3 := add_balance u3 v2 c2 (carry3_le_one ..)
  have top := high_add v3 c3 (umulh_le c x.w3) (carry3_le_one ..)
  simp only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero] at s1
  exact packed_product_balance c.toNat x.w0.toNat x.w1.toNat x.w2.toNat x.w3.toNat
    u0.toNat u1.toNat u2.toNat u3.toNat v0.toNat v1.toNat v2.toNat v3.toNat
    d1.toNat d2.toNat d3.toNat high.toNat c1.toNat c2.toNat c3.toNat
    (mul_balance c x.w0) (mul_balance c x.w1) (mul_balance c x.w2) (mul_balance c x.w3)
    s1 s2 s3 top

theorem WideWords.parts (wide : WideWords) :
    wide.low.value = wide.value%radix ∧ wide.high.toNat = wide.value/radix := by
  have low := wide.low.value_lt
  simp only [WideWords.value,radix] at *
  omega

theorem coreMultiplyWord_parts (c : BitVec 64) (x : LimbWords) :
    (coreMultiplyWord c x).low.value = (c.toNat*x.value)%radix ∧
    (coreMultiplyWord c x).high.toNat = (c.toNat*x.value)/radix := by
  have parts := (coreMultiplyWord c x).parts
  simpa only [coreMultiplyWord_correct] using parts

#print axioms mul_balance
#print axioms packed_product_balance
#print axioms coreMultiplyWord_correct
#print axioms coreMultiplyWord_parts
end SecpMath.Product
