import SecpMath.Product
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
namespace SecpMath.WordMulAdd
open ArmCertValue SecpMath.Addition SecpMath.Product

def lowProducts (c : BitVec 64) (y : LimbWords) : LimbWords :=
  ⟨Op.mul.eval [c,y.w0], Op.mul.eval [c,y.w1],
    Op.mul.eval [c,y.w2], Op.mul.eval [c,y.w3]⟩

def highProducts (c : BitVec 64) (y : LimbWords) : LimbWords :=
  ⟨0#64, Op.umulh.eval [c,y.w0], Op.umulh.eval [c,y.w1], Op.umulh.eval [c,y.w2]⟩

def mulAdd4 (a : LimbWords) (c : BitVec 64) (y : LimbWords) : WideWords :=
  let first := Addition.coreChain4 a (lowProducts c y)
  let second := Addition.coreChain4 first.1 (highProducts c y)
  ⟨second.1, Op.add3.eval [Op.umulh.eval [c,y.w3],first.2,second.2]⟩

theorem products_balance (c : BitVec 64) (y : LimbWords) :
    (lowProducts c y).value + (highProducts c y).value +
      radix * (Op.umulh.eval [c,y.w3]).toNat = c.toNat * y.value := by
  have p0 := mul_balance c y.w0
  have p1 := mul_balance c y.w1
  have p2 := mul_balance c y.w2
  have p3 := mul_balance c y.w3
  have expanded : c.toNat * y.value =
      pack4 (c.toNat*y.w0.toNat) (c.toNat*y.w1.toNat)
        (c.toNat*y.w2.toNat) (c.toNat*y.w3.toNat) := by
    simp only [LimbWords.value, pack4, Nat.mul_add, Nat.mul_left_comm]
  rw [expanded]
  simp only [lowProducts, highProducts, LimbWords.value, pack4, radix, limbRadix,
    BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.zero_add] at *
  omega

theorem sum_bound (a : LimbWords) (c : BitVec 64) (y : LimbWords) :
    a.value + c.toNat * y.value < radix * limbRadix := by
  have ha := a.value_lt
  have hy : y.value ≤ radix-1 := by have := y.value_lt; omega
  have hc : c.toNat ≤ limbRadix-1 := by have := c.isLt; change c.toNat < limbRadix at this; omega
  have product := Nat.mul_le_mul hc hy
  simp only [radix, limbRadix] at *
  omega

theorem add3_nat (x y z : BitVec 64) :
    (Op.add3.eval [x,y,z]).toNat = (x.toNat+y.toNat+z.toNat)%limbRadix := by
  change (x+y+z).toNat = _
  simp only [BitVec.toNat_add, limbRadix, Nat.mod_add_mod]

theorem mulAdd4_correct (a : LimbWords) (c : BitVec 64) (y : LimbWords) :
    (mulAdd4 a c y).value = a.value + c.toNat * y.value := by
  let first := Addition.coreChain4 a (lowProducts c y)
  let second := Addition.coreChain4 first.1 (highProducts c y)
  let top := Op.umulh.eval [c,y.w3]
  have firstBalance : first.1.value + radix*first.2.toNat = a.value + (lowProducts c y).value :=
    Addition.coreChain4_balance a (lowProducts c y)
  have secondBalance : second.1.value + radix*second.2.toNat = first.1.value + (highProducts c y).value :=
    Addition.coreChain4_balance first.1 (highProducts c y)
  have product := products_balance c y
  have combined : second.1.value + radix*(top.toNat+first.2.toNat+second.2.toNat) =
      a.value + c.toNat*y.value := by
    change (lowProducts c y).value + (highProducts c y).value + radix*top.toNat = c.toNat*y.value at product
    simp only [radix] at *
    omega
  have bound := sum_bound a c y
  have fit : top.toNat+first.2.toNat+second.2.toNat < limbRadix := by
    simp only [radix, limbRadix] at *
    omega
  change second.1.value + radix*(Op.add3.eval [top,first.2,second.2]).toNat = _
  rw [add3_nat, Nat.mod_eq_of_lt fit]
  exact combined

theorem add_zero (x : BitVec 64) : Op.add3.eval [x,0#64,0#64] = x := by
  change x+0#64+0#64 = x
  simp

theorem carry_zero (x : BitVec 64) : Op.carry3.eval [x,0#64,0#64] = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have h := Addition.carry3_limb x (0#64) 0 (by omega)
  have small : x.toNat < limbRadix := x.isLt
  simpa [limbCarry, Nat.div_eq_of_lt small] using h

theorem add_top (x low high : BitVec 64) :
    Op.add3.eval [Op.add3.eval [x,0#64,low],0#64,high] = Op.add3.eval [x,low,high] := by
  change (x+0#64+low)+0#64+high = x+low+high
  simp

theorem add_swap (x y z : BitVec 64) :
    Op.add3.eval [x,y,z] = Op.add3.eval [y,x,z] := by
  change x+y+z = y+x+z
  rw [BitVec.add_comm x y]

theorem carry_swap (x y z : BitVec 64) :
    Op.carry3.eval [x,y,z] = Op.carry3.eval [y,x,z] := by
  change b01 (decide (2^64 ≤ x.toNat+y.toNat+z.toNat)) =
    b01 (decide (2^64 ≤ y.toNat+x.toNat+z.toNat))
  rw [Nat.add_comm x.toNat y.toNat]

theorem mul_swap (x y : BitVec 64) : Op.mul.eval [x,y] = Op.mul.eval [y,x] := by
  change x*y = y*x
  exact BitVec.mul_comm x y

theorem umulh_swap (x y : BitVec 64) : Op.umulh.eval [x,y] = Op.umulh.eval [y,x] := by
  apply BitVec.eq_of_toNat_eq
  rw [Product.umulh_limb, Product.umulh_limb, Nat.mul_comm x.toNat y.toNat]

theorem condition_carry (nf zf cf vf : BitVec 64) (bound : cf.toNat ≤ 1) :
    (Op.cond 2#4).eval [nf,zf,cf,vf] = cf := by
  have cases : cf = 0#64 ∨ cf = 1#64 := by
    have values : cf.toNat = 0 ∨ cf.toNat = 1 := by omega
    rcases values with zero | one
    · left; apply BitVec.eq_of_toNat_eq; simpa using zero
    · right; apply BitVec.eq_of_toNat_eq; simpa using one
  rcases cases with zero | one
  · subst cf; rfl
  · subst cf; rfl

#print axioms products_balance
#print axioms mulAdd4_correct
end SecpMath.WordMulAdd
