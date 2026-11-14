import SecpMath.SquareWord
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
namespace SecpMath.HalfWord
open ArmCertValue SecpMath.Addition SecpMath.Product

theorem add_zero (x : BitVec 64) : Op.add.eval [x,0#64] = x := by
  change x+0#64=x
  exact BitVec.add_zero x

def halfRadix : Nat := 2^32
def low32 (x : BitVec 64) : BitVec 64 := Op.and.eval [x,4294967295#64]
def high32 (x : BitVec 64) : BitVec 64 := (Op.lsr 32).eval [x]
def mul32 (x y : BitVec 64) : BitVec 64 :=
  Op.add.eval [Op.mul.eval [low32 x,low32 y],0#64]

theorem low32_nat (x : BitVec 64) : (low32 x).toNat = x.toNat%halfRadix := by
  change (x &&& 4294967295#64).toNat = _
  rw [BitVec.toNat_and]
  change x.toNat &&& (2^32-1) = x.toNat%2^32
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 32

theorem high32_nat (x : BitVec 64) : (high32 x).toNat = x.toNat/halfRadix := by
  change (x >>> 32).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

theorem high32_bound (x : BitVec 64) : (high32 x).toNat < halfRadix := by
  rw [high32_nat]
  have bound := x.isLt
  simp only [halfRadix] at *
  omega

theorem low32_high32 (x : BitVec 64) : low32 (high32 x) = high32 x := by
  apply BitVec.eq_of_toNat_eq
  rw [low32_nat, Nat.mod_eq_of_lt (high32_bound x)]

theorem split (x : BitVec 64) :
    (low32 x).toNat + halfRadix*(high32 x).toNat = x.toNat := by
  rw [low32_nat, high32_nat]
  exact Nat.mod_add_div _ _

theorem mul32_nat (x y : BitVec 64) :
    (mul32 x y).toNat = (low32 x).toNat*(low32 y).toNat := by
  have hx : (low32 x).toNat ≤ halfRadix-1 := by
    rw [low32_nat]; have := Nat.mod_lt x.toNat (show 0 < halfRadix by decide); omega
  have hy : (low32 y).toNat ≤ halfRadix-1 := by
    rw [low32_nat]; have := Nat.mod_lt y.toNat (show 0 < halfRadix by decide); omega
  have bound := Nat.mul_le_mul hx hy
  have fit : (low32 x).toNat*(low32 y).toNat < 2^64 := by
    simp only [halfRadix] at bound
    omega
  change (low32 x*low32 y+0#64).toNat = _
  rw [BitVec.add_zero, BitVec.toNat_mul, Nat.mod_eq_of_lt fit]

theorem shifted_cross (x : BitVec 64) :
    ((Op.lsl 33).eval [x]).toNat + limbRadix*((Op.lsr 31).eval [x]).toNat =
      2*halfRadix*x.toNat := by
  change (x <<< 33).toNat + limbRadix*(x >>> 31).toNat = _
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, limbRadix, halfRadix]
  omega

def squareCross (x : BitVec 64) : BitVec 64 := mul32 x (high32 x)
def squareLow (x : BitVec 64) : BitVec 64 :=
  Op.add3.eval [mul32 x x,(Op.lsl 33).eval [squareCross x],0#64]
def squareCarry (x : BitVec 64) : BitVec 64 :=
  Op.carry3.eval [mul32 x x,(Op.lsl 33).eval [squareCross x],0#64]
def squareHigh (x : BitVec 64) : BitVec 64 :=
  Op.add3.eval [mul32 (high32 x) (high32 x),(Op.lsr 31).eval [squareCross x],squareCarry x]

theorem square64_correct (x : BitVec 64) :
    (squareLow x).toNat + limbRadix*(squareHigh x).toNat = x.toNat*x.toNat := by
  have lower := Product.add_balance (mul32 x x) ((Op.lsl 33).eval [squareCross x]) (0#64) (by decide)
  change (squareLow x).toNat + limbRadix*(squareCarry x).toNat = _ at lower
  have upper := Product.add_balance (mul32 (high32 x) (high32 x))
    ((Op.lsr 31).eval [squareCross x]) (squareCarry x) (Addition.carry3_le_one ..)
  change (squareHigh x).toNat + limbRadix*(Op.carry3.eval
    [mul32 (high32 x) (high32 x),(Op.lsr 31).eval [squareCross x],squareCarry x]).toNat = _ at upper
  generalize overflow_eq : (Op.carry3.eval
    [mul32 (high32 x) (high32 x),(Op.lsr 31).eval [squareCross x],squareCarry x]).toNat = overflow at upper
  clear overflow_eq
  have cross := shifted_cross (squareCross x)
  have parts := split x
  rw [mul32_nat] at lower
  rw [mul32_nat, low32_high32] at upper
  change ((Op.lsl 33).eval [squareCross x]).toNat + limbRadix*((Op.lsr 31).eval [squareCross x]).toNat =
    2*halfRadix*(mul32 x (high32 x)).toNat at cross
  rw [mul32_nat, low32_high32] at cross
  have productBound := Product.product_upper x x
  simp only [limbRadix, halfRadix, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at *
  have combined : (squareLow x).toNat + 18446744073709551616*(squareHigh x).toNat +
      340282366920938463463374607431768211456*overflow = x.toNat*x.toNat := by
    grind only
  omega

#print axioms low32_nat
#print axioms mul32_nat
#print axioms shifted_cross
#print axioms square64_correct
theorem sub_balance (x y carry : BitVec 64) (bound : carry.toNat ≤ 1) :
    (Op.sbc3.eval [x,y,carry]).toNat + y.toNat + 1 =
      x.toNat + carry.toNat + limbRadix*(1-(Op.sbc3C.eval [x,y,carry]).toNat) := by
  have balance := Product.add_balance x (~~~y) carry bound
  have flag := SecpMath.sbc3C_le_one x y carry
  have hy := y.isLt
  change (Op.sbc3.eval [x,y,carry]).toNat + limbRadix*(Op.sbc3C.eval [x,y,carry]).toNat =
    x.toNat+(~~~y).toNat+carry.toNat at balance
  rw [BitVec.toNat_not] at balance
  simp only [limbRadix] at *
  omega

def pairValue (x : BitVec 64 × BitVec 64) : Nat := x.1.toNat+limbRadix*x.2.toNat

theorem pair_bound (x : BitVec 64 × BitVec 64) : pairValue x < limbRadix^2 := by
  have low := x.1.isLt
  have high := x.2.isLt
  simp only [pairValue, limbRadix] at *
  omega

def sub2 (x y : BitVec 64 × BitVec 64) : (BitVec 64 × BitVec 64) × BitVec 64 :=
  let low := Op.sbc3.eval [x.1,y.1,1#64]
  let carry := Op.sbc3C.eval [x.1,y.1,1#64]
  ((low,Op.sbc3.eval [x.2,y.2,carry]),Op.sbc3C.eval [x.2,y.2,carry])

theorem sub2_balance (x y : BitVec 64 × BitVec 64) :
    pairValue (sub2 x y).1 + pairValue y =
      pairValue x + limbRadix^2*(1-(sub2 x y).2.toNat) := by
  have low := sub_balance x.1 y.1 (1#64) (by decide)
  have lowFlag := SecpMath.sbc3C_le_one x.1 y.1 (1#64)
  have high := sub_balance x.2 y.2 (Op.sbc3C.eval [x.1,y.1,1#64]) (SecpMath.sbc3C_le_one ..)
  simp only [sub2, pairValue, limbRadix, BitVec.toNat_ofNat] at *
  omega

def negate2 (x : BitVec 64 × BitVec 64) (mask : BitVec 64) : BitVec 64 × BitVec 64 :=
  let low := Op.eor.eval [x.1,mask]
  let high := Op.eor.eval [x.2,mask]
  let carry := Op.sbc3C.eval [low,mask,1#64]
  (Op.sbc3.eval [low,mask,1#64],Op.sbc3.eval [high,mask,carry])

theorem negate2_zero (x : BitVec 64 × BitVec 64) : negate2 x (0#64) = x := by
  rcases x with ⟨lo,hi⟩
  simp only [negate2]
  change ((lo ^^^ 0#64)+~~~(0#64)+1#64,
    (hi ^^^ 0#64)+~~~(0#64)+b01 (decide (2^64 ≤ (lo ^^^ 0#64).toNat+(~~~(0#64)).toNat+1))) = (lo,hi)
  have carry : decide (2^64 ≤ (lo ^^^ 0#64).toNat+(~~~(0#64)).toNat+1) = true := by
    simp only [BitVec.xor_zero, BitVec.toNat_not, BitVec.toNat_ofNat]
    simp
  rw [carry]
  simp [b01, BitVec.add_assoc]

theorem negate2_ones (x : BitVec 64 × BitVec 64) (positive : 0 < pairValue x) :
    pairValue (negate2 x (18446744073709551615#64)) + pairValue x = limbRadix^2 := by
  let lo := Op.eor.eval [x.1,18446744073709551615#64]
  let hi := Op.eor.eval [x.2,18446744073709551615#64]
  have loNat : lo.toNat = limbRadix-1-x.1.toNat := by
    change (x.1 ^^^ BitVec.allOnes 64).toNat = _
    rw [BitVec.xor_allOnes,BitVec.toNat_not]
    rfl
  have hiNat : hi.toNat = limbRadix-1-x.2.toNat := by
    change (x.2 ^^^ BitVec.allOnes 64).toNat = _
    rw [BitVec.xor_allOnes,BitVec.toNat_not]
    rfl
  have low := sub_balance lo (18446744073709551615#64) (1#64) (by decide)
  have high := sub_balance hi (18446744073709551615#64)
    (Op.sbc3C.eval [lo,18446744073709551615#64,1#64]) (SecpMath.sbc3C_le_one ..)
  have flag := SecpMath.sbc3C_le_one hi (18446744073709551615#64)
    (Op.sbc3C.eval [lo,18446744073709551615#64,1#64])
  have lowFlag := SecpMath.sbc3C_le_one lo (18446744073709551615#64) (1#64)
  have xLow := x.1.isLt
  have xHigh := x.2.isLt
  have resultBound := pair_bound (negate2 x (18446744073709551615#64))
  have xBound := pair_bound x
  change (Op.sbc3.eval [lo,18446744073709551615#64,1#64]).toNat +
    limbRadix*(Op.sbc3.eval [hi,18446744073709551615#64,Op.sbc3C.eval [lo,18446744073709551615#64,1#64]]).toNat +
      pairValue x = limbRadix^2
  simp only [loNat,hiNat,pairValue,limbRadix,BitVec.toNat_ofNat] at *
  omega

theorem mask_carry (n z carry v : BitVec 64) :
    (Op.cselc 2#4).eval [n,z,carry,v,0#64,18446744073709551615#64] =
      if carry = 0#64 then 18446744073709551615#64 else 0#64 := by
  change (if condHolds 2#4 n z carry v then 0#64 else 18446744073709551615#64) = _
  by_cases zero : carry = 0#64 <;> simp [condHolds,zero]

def abs2 (x y : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  let difference := sub2 x y
  negate2 difference.1 (if difference.2 = 0#64 then 18446744073709551615#64 else 0#64)

theorem abs2_correct (x y : BitVec 64 × BitVec 64) :
    pairValue (abs2 x y)+pairValue y = pairValue x ∨
      pairValue (abs2 x y)+pairValue x = pairValue y := by
  have balance := sub2_balance x y
  have flag : (sub2 x y).2.toNat ≤ 1 := SecpMath.sbc3C_le_one ..
  have xBound := pair_bound x
  have yBound := pair_bound y
  by_cases zero : (sub2 x y).2 = 0#64
  · have flagNat := congrArg BitVec.toNat zero
    have positive : 0 < pairValue (sub2 x y).1 := by
      simp only [flagNat,BitVec.toNat_ofNat,limbRadix] at balance xBound yBound
      omega
    have negated := negate2_ones (sub2 x y).1 positive
    right
    simp only [abs2,zero,↓reduceIte]
    simp only [flagNat,BitVec.toNat_ofNat,limbRadix] at balance negated
    omega
  · have flagNat : (sub2 x y).2.toNat = 1 := by
      have nonzero : (sub2 x y).2.toNat ≠ 0 := by
        intro eq
        exact zero (BitVec.eq_of_toNat_eq eq)
      omega
    left
    simp only [abs2,zero,↓reduceIte,negate2_zero]
    simp only [flagNat,Nat.sub_self,Nat.mul_zero,Nat.add_zero] at balance
    exact balance

#print axioms sub_balance
#print axioms sub2_balance
#print axioms negate2_zero
#print axioms negate2_ones
#print axioms mask_carry
#print axioms abs2_correct

theorem mask_balance (n z carry v : BitVec 64) (bound : carry.toNat ≤ 1) :
    ((Op.cselc 2#4).eval [n,z,carry,v,0#64,18446744073709551615#64]).toNat +
      limbRadix*carry.toNat = limbRadix-1+carry.toNat := by
  rw [mask_carry]
  by_cases zero : carry = 0#64
  · simp [zero,limbRadix]
  · have nonzero : carry.toNat ≠ 0 := by
      intro eq
      exact zero (BitVec.eq_of_toNat_eq eq)
    have one : carry.toNat = 1 := by omega
    simp [zero,one,limbRadix]
#print axioms mask_balance
theorem shifted_half (x : BitVec 64) :
    ((Op.lsl 32).eval [x]).toNat+limbRadix*(high32 x).toNat = halfRadix*x.toNat := by
  change (x <<< 32).toNat+limbRadix*(x >>> 32).toNat = _
  rw [BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight]
  simp only [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow,limbRadix,halfRadix]
  omega

theorem mul977_nat (x : BitVec 64) (bound : x.toNat < halfRadix) :
    (Op.mul.eval [977#64,x]).toNat = 977*x.toNat := by
  have fit : 977*x.toNat < limbRadix := by
    simp only [limbRadix,halfRadix] at *
    omega
  change (977#64*x).toNat = _
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt fit

def correctionMiddle (x : BitVec 64) : BitVec 64 :=
  Op.add.eval [Op.mul.eval [977#64,high32 x],low32 x]
def correctionLow (x : BitVec 64) : BitVec 64 :=
  Op.add3.eval [Op.mul.eval [977#64,low32 x],(Op.lsl 32).eval [correctionMiddle x],0#64]
def correctionCarry (x : BitVec 64) : BitVec 64 :=
  Op.carry3.eval [Op.mul.eval [977#64,low32 x],(Op.lsl 32).eval [correctionMiddle x],0#64]
def correctionHigh (x : BitVec 64) : BitVec 64 :=
  Op.add3.eval [high32 x,high32 (correctionMiddle x),correctionCarry x]

theorem correction_middle_nat (x : BitVec 64) :
    (correctionMiddle x).toNat = 977*(high32 x).toNat+(low32 x).toNat := by
  have hi := high32_bound x
  have lo : (low32 x).toNat < halfRadix := by
    rw [low32_nat]
    exact Nat.mod_lt _ (by decide)
  have fit : 977*(high32 x).toNat+(low32 x).toNat < limbRadix := by
    simp only [limbRadix,halfRadix] at *
    omega
  change (Op.mul.eval [977#64,high32 x]+low32 x).toNat = _
  rw [BitVec.toNat_add,mul977_nat _ hi]
  exact Nat.mod_eq_of_lt fit

theorem correction64_correct (x : BitVec 64) :
    (correctionLow x).toNat+limbRadix*(correctionHigh x).toNat = correction*x.toNat := by
  have lower := Product.add_balance (Op.mul.eval [977#64,low32 x])
    ((Op.lsl 32).eval [correctionMiddle x]) (0#64) (by decide)
  change (correctionLow x).toNat+limbRadix*(correctionCarry x).toNat = _ at lower
  have upper := Product.add_balance (high32 x) (high32 (correctionMiddle x))
    (correctionCarry x) (Addition.carry3_le_one ..)
  change (correctionHigh x).toNat+limbRadix*(Op.carry3.eval
    [high32 x,high32 (correctionMiddle x),correctionCarry x]).toNat = _ at upper
  generalize overflow_eq : (Op.carry3.eval
    [high32 x,high32 (correctionMiddle x),correctionCarry x]).toNat = overflow at upper
  clear overflow_eq
  have shifted := shifted_half (correctionMiddle x)
  have middle := correction_middle_nat x
  have parts := split x
  have lo : (low32 x).toNat < halfRadix := by rw [low32_nat]; exact Nat.mod_lt _ (by decide)
  rw [mul977_nat _ lo] at lower
  have inputBound := x.isLt
  simp only [limbRadix,halfRadix,correction,BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero] at *
  have combined : (correctionLow x).toNat+18446744073709551616*(correctionHigh x).toNat+
      340282366920938463463374607431768211456*overflow = 4294968273*x.toNat := by
    omega
  omega

#print axioms shifted_half
#print axioms mul977_nat
#print axioms correction_middle_nat
#print axioms correction64_correct

theorem sub_balance_additive (x y carry : BitVec 64) (bound : carry.toNat ≤ 1) :
    (Op.sbc3.eval [x,y,carry]).toNat+y.toNat+1+
      limbRadix*(Op.sbc3C.eval [x,y,carry]).toNat = x.toNat+carry.toNat+limbRadix := by
  have balance := Product.add_balance x (~~~y) carry bound
  have hy := y.isLt
  change (Op.sbc3.eval [x,y,carry]).toNat+limbRadix*(Op.sbc3C.eval [x,y,carry]).toNat =
    x.toNat+(~~~y).toNat+carry.toNat at balance
  rw [BitVec.toNat_not] at balance
  simp only [limbRadix] at *
  omega
#print axioms sub_balance_additive
theorem pair_injective (left right : BitVec 64 × BitVec 64)
    (same : pairValue left = pairValue right) : left = right := by
  have l0 := left.1.isLt
  have l1 := left.2.isLt
  have r0 := right.1.isLt
  have r1 := right.2.isLt
  simp only [pairValue,limbRadix] at same
  apply Prod.ext <;> apply BitVec.eq_of_toNat_eq <;> omega

theorem correction_pair (x : BitVec 64) :
    (correctionLow x,correctionHigh x) =
      (Op.mul.eval [BitVec.ofNat 64 correction,x],Op.umulh.eval [BitVec.ofNat 64 correction,x]) := by
  apply pair_injective
  have actual := correction64_correct x
  have target := Product.mul_balance (BitVec.ofNat 64 correction) x
  change _ = (BitVec.ofNat 64 correction).toNat*x.toNat at target
  have constantNat : (BitVec.ofNat 64 correction).toNat = correction := by decide
  rw [constantNat] at target
  exact actual.trans target.symm
#print axioms pair_injective
#print axioms correction_pair
def quotientLow (q : BitVec 64) : BitVec 64 :=
  Op.add3.eval [Op.mul.eval [977#64,q],(Op.lsl 32).eval [q],0#64]
def quotientCarry (q : BitVec 64) : BitVec 64 :=
  Op.carry3.eval [Op.mul.eval [977#64,q],(Op.lsl 32).eval [q],0#64]
def quotientHigh (q : BitVec 64) : BitVec 64 :=
  Op.add3.eval [0#64,high32 q,quotientCarry q]

theorem quotient_pair (q : BitVec 64) (fit : 977*q.toNat < limbRadix) :
    (quotientLow q,quotientHigh q) =
      (Op.mul.eval [q,BitVec.ofNat 64 correction],Op.umulh.eval [q,BitVec.ofNat 64 correction]) := by
  apply pair_injective
  have lower := Product.add_balance (Op.mul.eval [977#64,q]) ((Op.lsl 32).eval [q]) (0#64) (by decide)
  change (quotientLow q).toNat+limbRadix*(quotientCarry q).toNat = _ at lower
  have smallProduct : (Op.mul.eval [977#64,q]).toNat = 977*q.toNat := by
    change (977#64*q).toNat = _
    rw [BitVec.toNat_mul]
    exact Nat.mod_eq_of_lt fit
  rw [smallProduct] at lower
  have highBound := high32_bound q
  have carryBound : (quotientCarry q).toNat ≤ 1 := Addition.carry3_le_one ..
  have upperFit : (0#64).toNat+(high32 q).toNat+(quotientCarry q).toNat < limbRadix := by
    simp only [BitVec.toNat_ofNat,halfRadix,limbRadix] at *
    omega
  have upper : (quotientHigh q).toNat = (high32 q).toNat+(quotientCarry q).toNat := by
    unfold quotientHigh
    rw [WordMulAdd.add3_nat,Nat.mod_eq_of_lt upperFit]
    simp only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.zero_add]
  have shifted := shifted_half q
  have target := Product.mul_balance q (BitVec.ofNat 64 correction)
  have constantNat : (BitVec.ofNat 64 correction).toNat = correction := by decide
  rw [constantNat] at target
  simp only [pairValue,upper,limbRadix,halfRadix,correction,BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero] at *
  omega
#print axioms quotient_pair

theorem upper_square_carry (digits overflow upper top : Nat)
    (bound : upper ≤ (limbRadix^2-1)*(limbRadix^2-1))
    (topBound : top < limbRadix^2)
    (balance : digits+radix*overflow = upper+top) : overflow = 0 := by
  simp only [radix,limbRadix] at *
  omega
#print axioms upper_square_carry
theorem wide_bound (low high : Nat) (lowBound : low < radix) (highBound : high < radix) :
    low+radix*high < radix^2 := by
  simp only [radix] at *
  omega

theorem bounded512 (value product left right : Nat)
    (valueBound : value < radix^2) (productBound : product < radix^2)
    (balance : value+radix^2*left = product+radix^2*right) : value = product := by
  simp only [radix] at *
  omega
#print axioms wide_bound
#print axioms bounded512
end SecpMath.HalfWord
