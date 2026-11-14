import SecpMath.HalfWord
import Std.Tactic
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
namespace SecpMath.Karatsuba.Arithmetic

/-- Mathematical decomposition used by the two32-bit UMULL sequences in the
official mul body. Actual instruction/carry correspondence is separate. -/
theorem split_product (x y radix : Nat) :
    x * y = (x % radix) * (y % radix) +
      radix * ((x / radix) * (y % radix) + (x % radix) * (y / radix)) +
      (radix * radix) * ((x / radix) * (y / radix)) := by
  calc
    x * y = (x % radix + radix * (x / radix)) *
        (y % radix + radix * (y / radix)) := by rw [Nat.mod_add_div, Nat.mod_add_div]
    _ = _ := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
      ac_rfl

/-- Bounds justify that each UMULL result is a full64-bit product, including
unreduced input limbs. -/
theorem product32_bound (x y : Nat) (hx : x < 2^32) (hy : y < 2^32) :
    x * y < 2^64 := by
  simpa only [← Nat.pow_add] using Nat.mul_lt_mul_of_lt_of_lt hx hy

/-- The signed cross term selected by SUBS/CNEG/CSETM/CINV. The sign choice and
multiword two's-complement accumulation still need actual machine proofs. -/
theorem cross_terms (a0 a1 b0 b1 : Int) :
    (a1-a0) * (b0-b1) + a0*b0 + a1*b1 = a0*b1 + a1*b0 := by
  simp only [Int.sub_mul, Int.mul_sub]
  omega

theorem karatsuba (a0 a1 b0 b1 radix : Int) :
    (a0 + radix*a1) * (b0 + radix*b1) =
      a0*b0 + radix * ((a1-a0)*(b0-b1) + a0*b0 + a1*b1) +
      (radix*radix) * (a1*b1) := by
  rw [cross_terms]
  simp only [Int.add_mul, Int.mul_add, Int.mul_assoc]
  ac_rfl

/-- Full256-bit operands require a512-bit product bound; canonical-field
restrictions are unnecessary for the raw s2n contract. -/
theorem product256_bound (x y : Nat) (hx : x < 2^256) (hy : y < 2^256) :
    x * y < 2^512 := by
  simpa only [← Nat.pow_add] using Nat.mul_lt_mul_of_lt_of_lt hx hy

end SecpMath.Karatsuba.Arithmetic

namespace SecpMath.Karatsuba.Signs

def magnitude (x y : Nat) : Nat := if y ≤ x then x-y else y-x

theorem signed_magnitude (x y : Nat) :
    (if y ≤ x then (magnitude x y : Int) else -(magnitude x y : Int)) = (x : Int)-y := by
  by_cases order : y ≤ x
  · simp only [order, ↓reduceIte, magnitude, Int.ofNat_sub order]
  · have reverse : x ≤ y := by omega
    simp only [order, ↓reduceIte, magnitude, Int.ofNat_sub reverse]
    omega

def diagonal (a0 a1 b0 b1 radix : Nat) : Nat :=
  a0*b0 + radix*(a0*b0+a1*b1) + (radix*radix)*(a1*b1)

/-- The two carry-clear tests select precisely the sign of the Karatsuba
cross term. Both branches use nonnegative magnitudes of unsigned limbs. -/
theorem recombine (a0 a1 b0 b1 radix : Nat) :
    if ((a0 ≤ a1) ↔ (b1 ≤ b0)) then
      diagonal a0 a1 b0 b1 radix + radix*(magnitude a1 a0*magnitude b0 b1) =
        (a0+radix*a1)*(b0+radix*b1)
    else
      (a0+radix*a1)*(b0+radix*b1) + radix*(magnitude a1 a0*magnitude b0 b1) =
        diagonal a0 a1 b0 b1 radix := by
  have identity := SecpMath.Karatsuba.Arithmetic.karatsuba
    (a0 : Int) (a1 : Int) (b0 : Int) (b1 : Int) (radix : Int)
  rw [← signed_magnitude a1 a0, ← signed_magnitude b0 b1] at identity
  by_cases aOrder : a0 ≤ a1 <;> by_cases bOrder : b1 ≤ b0
  all_goals simp only [aOrder, bOrder, ↓reduceIte, iff_self, not_false_eq_true,
    not_true_eq_false, iff_true, iff_false, true_iff, false_iff] at identity ⊢
  all_goals apply Int.ofNat_inj.mp
  all_goals simp only [diagonal, Int.natCast_add, Int.natCast_mul]
  all_goals simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.mul_add,
    Int.add_mul, Int.mul_assoc] at identity ⊢
  all_goals omega

end SecpMath.Karatsuba.Signs

namespace SecpMath.Karatsuba.Carry

/-- The five carry steps before signed cross-term addition. The one required
upper-product bound proves that the first discarded carry is zero. The final
discarded carry remains explicit until the full-product bound is available. -/
theorem diagonal_balance (l0 l1 h0 h1 p0 p1 q0 q1 q2 c0 k0 c1 c2 k1 : Nat)
    (upperBound : h0 + 2^64*h1 + l1 < 2^128)
    (first : p0 + 2^64*c0 = h0+l1)
    (second : p1 + 2^64*k0 = h1+c0)
    (third : q0 + 2^64*c1 = l0+p0)
    (fourth : q1 + 2^64*c2 = p0+p1+c1)
    (fifth : q2 + 2^64*k1 = p1+c2) :
    k0 = 0 ∧
    l0 + 2^64*q0 + 2^128*q1 + 2^192*q2 + 2^256*k1 =
      (l0 + 2^64*l1) + 2^64*((l0 + 2^64*l1) + (h0 + 2^64*h1)) +
        2^128*(h0 + 2^64*h1) := by
  simp only [Nat.reducePow] at *
  constructor <;> omega

theorem positive_balance (l0 q0 q1 q2 d0 d1 r0 r1 r2 c0 c1 finalCarry : Nat)
    (first : r0 + 2^64*c0 = d0+q0)
    (second : r1 + 2^64*c1 = d1+q1+c0)
    (third : r2 + 2^64*finalCarry = q2+c1) :
    l0 + 2^64*r0 + 2^128*r1 + 2^192*r2 + 2^256*finalCarry =
      l0 + 2^64*q0 + 2^128*q1 + 2^192*q2 + 2^64*(d0+2^64*d1) := by
  simp only [Nat.reducePow] at *
  omega

/-- The all-ones XOR, carry-in one, and sign-extension word implement a signed
subtraction across the three upper limbs. -/
theorem negative_balance (l0 q0 q1 q2 d0 d1 r0 r1 r2 c0 c1 finalCarry : Nat)
    (first : r0 + 2^64*c0 + d0 = q0+2^64)
    (second : r1 + 2^64*c1 + d1 = q1+c0+(2^64-1))
    (third : r2 + 2^64*finalCarry = q2+c1+(2^64-1)) :
    l0 + 2^64*r0 + 2^128*r1 + 2^192*r2 + 2^256*finalCarry +
      2^64*(d0+2^64*d1) =
        l0 + 2^64*q0 + 2^128*q1 + 2^192*q2 + 2^256 := by
  simp only [Nat.reducePow] at *
  omega

/-- A bounded complete product selects the unique256-bit result, even when a
negative cross term causes carries to wrap in the intermediate assembly. -/
theorem bounded_finish (value product base magnitude firstCarry lastCarry : Nat)
    (valueBound : value < 2^256) (productBound : product < 2^256)
    (diagonal : base + 2^256*firstCarry = product + 2^64*magnitude)
    (negative : value + 2^256*lastCarry + 2^64*magnitude = base + 2^256) :
    value = product := by
  simp only [Nat.reducePow] at *
  omega

theorem bounded_positive_finish (value product base magnitude firstCarry lastCarry : Nat)
    (productBound : product < 2^256)
    (diagonal : base + 2^256*firstCarry + 2^64*magnitude = product)
    (positive : value + 2^256*lastCarry = base + 2^64*magnitude) :
    value = product := by
  simp only [Nat.reducePow] at *
  omega

end SecpMath.Karatsuba.Carry

namespace SecpMath.KaratsubaWord
open ArmCertValue SecpMath.Addition SecpMath.Product

def magnitudeWord (x y : BitVec 64) : BitVec 64 :=
  if y.toNat ≤ x.toNat then x-y else y-x

theorem sbc_sub (x y : BitVec 64) : Op.sbc3.eval [x,y,1#64] = x-y := by
  apply BitVec.eq_of_toNat_eq
  have actual := SecpMath.sbc3_limb x y 0 (by decide)
  simpa only [limbDifference,Nat.add_zero,wordSub_nat] using actual

theorem word_carry (x y : BitVec 64) :
    Op.sbc3C.eval [x,y,1#64] = if y.toNat ≤ x.toNat then 1#64 else 0#64 := by
  have actual := SecpMath.sbc3C_word x y 0 (by decide)
  by_cases order : y.toNat ≤ x.toNat <;> simpa [limbBorrow,order] using actual

theorem magnitude_nat (x y : BitVec 64) :
    (magnitudeWord x y).toNat = Karatsuba.Signs.magnitude x.toNat y.toNat := by
  by_cases order : y.toNat ≤ x.toNat
  · simp only [magnitudeWord,Karatsuba.Signs.magnitude,order,↓reduceIte,wordSub_nat]
  · have reverse : x.toNat ≤ y.toNat := by omega
    simp only [magnitudeWord,Karatsuba.Signs.magnitude,order,reverse,↓reduceIte,wordSub_nat]

theorem magnitude_control (x y n z overflow : BitVec 64) :
    Op.csel.eval [(Op.cond 2#4).eval [n,z,Op.sbc3C.eval [x,y,1#64],overflow],
      Op.sbc3.eval [x,y,1#64],Op.sub.eval [0#64,Op.sbc3.eval [x,y,1#64]]] = magnitudeWord x y := by
  rw [WordMulAdd.condition_carry _ _ _ _ (SecpMath.sbc3C_le_one ..),word_carry,sbc_sub]
  change (if (if y.toNat ≤ x.toNat then 1#64 else 0#64) ≠ 0#64 then x-y else 0#64-(x-y)) = _
  by_cases order : y.toNat ≤ x.toNat
  · simp only [order,↓reduceIte,magnitudeWord,show (1#64) ≠ 0#64 by decide]
    simp
  · simp only [order,↓reduceIte,magnitudeWord,ne_eq,not_true_eq_false]
    rw [BitVec.zero_sub,BitVec.neg_sub,BitVec.sub_eq_add_neg]
    exact BitVec.add_comm _ _

def signMask (a0 a1 b0 b1 : BitVec 64) : BitVec 64 :=
  if ((a0.toNat ≤ a1.toNat) ↔ (b1.toNat ≤ b0.toNat)) then 0#64 else 18446744073709551615#64

theorem sign_control (a0 a1 b0 b1 n0 z0 v0 n1 z1 v1 : BitVec 64) :
    Op.csel.eval [(Op.cond 2#4).eval [n1,z1,Op.sbc3C.eval [b0,b1,1#64],v1],
      (Op.cselc 2#4).eval [n0,z0,Op.sbc3C.eval [a1,a0,1#64],v0,0#64,18446744073709551615#64],
      Op.not.eval [(Op.cselc 2#4).eval [n0,z0,Op.sbc3C.eval [a1,a0,1#64],v0,0#64,18446744073709551615#64]]]
      = signMask a0 a1 b0 b1 := by
  rw [WordMulAdd.condition_carry _ _ _ _ (SecpMath.sbc3C_le_one ..),HalfWord.mask_carry,word_carry,word_carry]
  by_cases first : a0.toNat ≤ a1.toNat <;> by_cases second : b1.toNat ≤ b0.toNat
  all_goals simp only [signMask,first,second,↓reduceIte,iff_self,not_false_eq_true,
    not_true_eq_false,iff_true,iff_false,true_iff,false_iff]
  all_goals decide

#print axioms sbc_sub
#print axioms word_carry
#print axioms magnitude_nat
#print axioms magnitude_control
#print axioms sign_control
def diagonalWords (l0 l1 h0 h1 : BitVec 64) : LimbWords × BitVec 64 :=
  let p0 := Op.add3.eval [h0,l1,0#64]
  let c0 := Op.carry3.eval [h0,l1,0#64]
  let p1 := Op.add3.eval [h1,0#64,c0]
  let q0 := Op.add3.eval [l0,p0,0#64]
  let c1 := Op.carry3.eval [l0,p0,0#64]
  let q1 := Op.add3.eval [p0,p1,c1]
  let c2 := Op.carry3.eval [p0,p1,c1]
  let q2 := Op.add3.eval [p1,0#64,c2]
  let c3 := Op.carry3.eval [p1,0#64,c2]
  (⟨l0,q0,q1,q2⟩,c3)

theorem diagonal_balance (l0 l1 h0 h1 : BitVec 64)
    (upperBound : h0.toNat+limbRadix*h1.toNat+l1.toNat < limbRadix^2) :
    (diagonalWords l0 l1 h0 h1).1.value+radix*(diagonalWords l0 l1 h0 h1).2.toNat =
      (l0.toNat+limbRadix*l1.toNat)+
        limbRadix*((l0.toNat+limbRadix*l1.toNat)+(h0.toNat+limbRadix*h1.toNat))+
        limbRadix^2*(h0.toNat+limbRadix*h1.toNat) := by
  let p0 := Op.add3.eval [h0,l1,0#64]
  let c0 := Op.carry3.eval [h0,l1,0#64]
  let p1 := Op.add3.eval [h1,0#64,c0]
  let k0 := Op.carry3.eval [h1,0#64,c0]
  let q0 := Op.add3.eval [l0,p0,0#64]
  let c1 := Op.carry3.eval [l0,p0,0#64]
  let q1 := Op.add3.eval [p0,p1,c1]
  let c2 := Op.carry3.eval [p0,p1,c1]
  let q2 := Op.add3.eval [p1,0#64,c2]
  let k1 := Op.carry3.eval [p1,0#64,c2]
  have first := Product.add_balance h0 l1 (0#64) (by decide)
  have second := Product.add_balance h1 (0#64) c0 (Addition.carry3_le_one ..)
  have third := Product.add_balance l0 p0 (0#64) (by decide)
  have fourth := Product.add_balance p0 p1 c1 (Addition.carry3_le_one ..)
  have fifth := Product.add_balance p1 (0#64) c2 (Addition.carry3_le_one ..)
  change p0.toNat+limbRadix*c0.toNat = _ at first
  change p1.toNat+limbRadix*k0.toNat = _ at second
  change q0.toNat+limbRadix*c1.toNat = _ at third
  change q1.toNat+limbRadix*c2.toNat = _ at fourth
  change q2.toNat+limbRadix*k1.toNat = _ at fifth
  simp only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero] at first second third fifth
  have balanced := Karatsuba.Carry.diagonal_balance l0.toNat l1.toNat h0.toNat h1.toNat
    p0.toNat p1.toNat q0.toNat q1.toNat q2.toNat c0.toNat k0.toNat c1.toNat c2.toNat k1.toNat
    upperBound first second third fourth fifth
  exact balanced.2

def signedWords (base : LimbWords) (m0 m1 mask : BitVec 64) : LimbWords × BitVec 64 :=
  let carry := Op.carry3.eval [mask,1#64,0#64]
  let r0 := Op.add3.eval [Op.eor.eval [m0,mask],base.w1,carry]
  let c0 := Op.carry3.eval [Op.eor.eval [m0,mask],base.w1,carry]
  let r1 := Op.add3.eval [Op.eor.eval [m1,mask],base.w2,c0]
  let c1 := Op.carry3.eval [Op.eor.eval [m1,mask],base.w2,c0]
  let r2 := Op.add3.eval [base.w3,mask,c1]
  let c2 := Op.carry3.eval [base.w3,mask,c1]
  (⟨base.w0,r0,r1,r2⟩,c2)

theorem zero_carry : Op.carry3.eval [0#64,1#64,0#64] = 0#64 := by decide
theorem ones_carry : Op.carry3.eval [18446744073709551615#64,1#64,0#64] = 1#64 := by decide
theorem xor_zero (x : BitVec 64) : Op.eor.eval [x,0#64] = x := BitVec.xor_zero
theorem xor_ones (x : BitVec 64) : Op.eor.eval [x,18446744073709551615#64] = ~~~x :=
  BitVec.xor_allOnes

theorem signed_positive (base : LimbWords) (m0 m1 : BitVec 64) :
    (signedWords base m0 m1 (0#64)).1.value+radix*(signedWords base m0 m1 (0#64)).2.toNat =
      base.value+limbRadix*(m0.toNat+limbRadix*m1.toNat) := by
  let c0 := Op.carry3.eval [m0,base.w1,0#64]
  let c1 := Op.carry3.eval [m1,base.w2,c0]
  have first := Product.add_balance m0 base.w1 (0#64) (by decide)
  have second := Product.add_balance m1 base.w2 c0 (Addition.carry3_le_one ..)
  have third := Product.add_balance base.w3 (0#64) c1 (Addition.carry3_le_one ..)
  simp only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero] at first third
  have balanced := Karatsuba.Carry.positive_balance base.w0.toNat base.w1.toNat base.w2.toNat base.w3.toNat
    m0.toNat m1.toNat _ _ _ _ _ _ first second third
  simpa only [signedWords,zero_carry,xor_zero,LimbWords.value,pack4,limbRadix,radix] using balanced

theorem signed_negative (base : LimbWords) (m0 m1 : BitVec 64) :
    (signedWords base m0 m1 (18446744073709551615#64)).1.value+
      radix*(signedWords base m0 m1 (18446744073709551615#64)).2.toNat+
      limbRadix*(m0.toNat+limbRadix*m1.toNat) = base.value+radix := by
  let r0 := Op.add3.eval [~~~m0,base.w1,1#64]
  let c0 := Op.carry3.eval [~~~m0,base.w1,1#64]
  let r1 := Op.add3.eval [~~~m1,base.w2,c0]
  let c1 := Op.carry3.eval [~~~m1,base.w2,c0]
  let r2 := Op.add3.eval [base.w3,18446744073709551615#64,c1]
  let c2 := Op.carry3.eval [base.w3,18446744073709551615#64,c1]
  have first := Product.add_balance (~~~m0) base.w1 (1#64) (by decide)
  have second := Product.add_balance (~~~m1) base.w2 c0 (Addition.carry3_le_one ..)
  have third := Product.add_balance base.w3 (18446744073709551615#64) c1 (Addition.carry3_le_one ..)
  have firstNat : r0.toNat+2^64*c0.toNat+m0.toNat = base.w1.toNat+2^64 := by
    have bound := m0.isLt
    simp only [BitVec.toNat_not,BitVec.toNat_ofNat,limbRadix] at first
    change (Op.add3.eval [~~~m0,base.w1,1#64]).toNat+2^64*(Op.carry3.eval [~~~m0,base.w1,1#64]).toNat+
      m0.toNat = _
    omega
  have secondNat : r1.toNat+2^64*c1.toNat+m1.toNat = base.w2.toNat+c0.toNat+(2^64-1) := by
    have bound := m1.isLt
    simp only [BitVec.toNat_not,limbRadix] at second
    change (Op.add3.eval [~~~m1,base.w2,c0]).toNat+2^64*(Op.carry3.eval [~~~m1,base.w2,c0]).toNat+
      m1.toNat = _
    omega
  have balanced := Karatsuba.Carry.negative_balance base.w0.toNat base.w1.toNat base.w2.toNat base.w3.toNat
    m0.toNat m1.toNat r0.toNat r1.toNat r2.toNat c0.toNat c1.toNat c2.toNat firstNat secondNat
    (by simpa only [BitVec.toNat_ofNat,limbRadix,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using third)
  simpa only [signedWords,ones_carry,xor_ones,LimbWords.value,pack4,limbRadix,radix] using balanced

def core128 (a0 a1 b0 b1 : BitVec 64) : LimbWords :=
  let diagonal := diagonalWords (Op.mul.eval [a0,b0]) (Op.umulh.eval [a0,b0])
    (Op.mul.eval [a1,b1]) (Op.umulh.eval [a1,b1])
  let ma := magnitudeWord a1 a0
  let mb := magnitudeWord b0 b1
  (signedWords diagonal.1 (Op.mul.eval [ma,mb]) (Op.umulh.eval [ma,mb]) (signMask a0 a1 b0 b1)).1

theorem core128_correct (a0 a1 b0 b1 : BitVec 64) :
    (core128 a0 a1 b0 b1).value =
      (a0.toNat+limbRadix*a1.toNat)*(b0.toNat+limbRadix*b1.toNat) := by
  let ll := (Op.mul.eval [a0,b0],Op.umulh.eval [a0,b0])
  let hh := (Op.mul.eval [a1,b1],Op.umulh.eval [a1,b1])
  let cross := (Op.mul.eval [magnitudeWord a1 a0,magnitudeWord b0 b1],
    Op.umulh.eval [magnitudeWord a1 a0,magnitudeWord b0 b1])
  let diagonal := diagonalWords ll.1 ll.2 hh.1 hh.2
  have lowProduct := Product.mul_balance a0 b0
  have highProduct := Product.mul_balance a1 b1
  have highBound := Product.product_upper a1 b1
  have lowHighBound := Product.umulh_le a0 b0
  have upperBound : hh.1.toNat+limbRadix*hh.2.toNat+ll.2.toNat < limbRadix^2 := by
    change (Op.mul.eval [a1,b1]).toNat+limbRadix*(Op.umulh.eval [a1,b1]).toNat+_ < _
    rw [highProduct]
    simp only [limbRadix] at *
    omega
  have diagonalBalance := diagonal_balance ll.1 ll.2 hh.1 hh.2 upperBound
  change diagonal.1.value+radix*diagonal.2.toNat = _ at diagonalBalance
  change ll.1.toNat+limbRadix*ll.2.toNat = _ at lowProduct
  change hh.1.toNat+limbRadix*hh.2.toNat = _ at highProduct
  rw [lowProduct,highProduct] at diagonalBalance
  have crossProduct := Product.mul_balance (magnitudeWord a1 a0) (magnitudeWord b0 b1)
  rw [magnitude_nat,magnitude_nat] at crossProduct
  change cross.1.toNat+limbRadix*cross.2.toNat = _ at crossProduct
  have algebra := Karatsuba.Signs.recombine a0.toNat a1.toNat b0.toNat b1.toNat limbRadix
  have leftBound := HalfWord.pair_bound (a0,a1)
  have rightBound := HalfWord.pair_bound (b0,b1)
  have productBound : (a0.toNat+limbRadix*a1.toNat)*(b0.toNat+limbRadix*b1.toNat) < radix := by
    have bound := Nat.mul_lt_mul_of_lt_of_lt leftBound rightBound
    simpa only [HalfWord.pairValue,limbRadix,radix] using bound
  by_cases positive : ((a0.toNat ≤ a1.toNat) ↔ (b1.toNat ≤ b0.toNat))
  · simp only [positive,↓reduceIte] at algebra
    have machine := signed_positive diagonal.1 cross.1 cross.2
    change (core128 a0 a1 b0 b1).value = _
    have diagonalEq : diagonal.1.value+radix*diagonal.2.toNat+
        limbRadix*(cross.1.toNat+limbRadix*cross.2.toNat) =
        (a0.toNat+limbRadix*a1.toNat)*(b0.toNat+limbRadix*b1.toNat) := by
      rw [diagonalBalance,crossProduct]
      exact algebra
    have finish := Karatsuba.Carry.bounded_positive_finish
      (signedWords diagonal.1 cross.1 cross.2 (0#64)).1.value _ diagonal.1.value
      (cross.1.toNat+limbRadix*cross.2.toNat) diagonal.2.toNat
      (signedWords diagonal.1 cross.1 cross.2 (0#64)).2.toNat
      productBound diagonalEq machine
    simpa only [core128,signMask,positive,↓reduceIte] using finish
  · simp only [positive,↓reduceIte] at algebra
    have machine := signed_negative diagonal.1 cross.1 cross.2
    have diagonalEq : diagonal.1.value+radix*diagonal.2.toNat =
        (a0.toNat+limbRadix*a1.toNat)*(b0.toNat+limbRadix*b1.toNat)+
        limbRadix*(cross.1.toNat+limbRadix*cross.2.toNat) := by
      rw [diagonalBalance,crossProduct]
      exact algebra.symm
    have finish := Karatsuba.Carry.bounded_finish
      (signedWords diagonal.1 cross.1 cross.2 (18446744073709551615#64)).1.value _ diagonal.1.value
      (cross.1.toNat+limbRadix*cross.2.toNat) diagonal.2.toNat
      (signedWords diagonal.1 cross.1 cross.2 (18446744073709551615#64)).2.toNat
      (signedWords diagonal.1 cross.1 cross.2 (18446744073709551615#64)).1.value_lt
      productBound diagonalEq machine
    simpa only [core128,signMask,positive,↓reduceIte] using finish

#print axioms diagonal_balance
#print axioms signed_positive
#print axioms signed_negative
#print axioms core128_correct

end SecpMath.KaratsubaWord

namespace SecpMath.Karatsuba.Carry128


theorem diagonal_balance (l0 l1 h0 h1 p0 p1 q0 q1 q2 c0 k0 c1 c2 k1 : Nat)
    (upperBound : h0 + 2^128*h1 + l1 < 2^256)
    (first : p0 + 2^128*c0 = h0+l1)
    (second : p1 + 2^128*k0 = h1+c0)
    (third : q0 + 2^128*c1 = l0+p0)
    (fourth : q1 + 2^128*c2 = p0+p1+c1)
    (fifth : q2 + 2^128*k1 = p1+c2) :
    k0 = 0 ∧
    l0 + 2^128*q0 + 2^256*q1 + 2^384*q2 + 2^512*k1 =
      (l0 + 2^128*l1) + 2^128*((l0 + 2^128*l1) + (h0 + 2^128*h1)) +
        2^256*(h0 + 2^128*h1) := by
  simp only [Nat.reducePow] at *
  constructor <;> omega

theorem positive_balance (l0 q0 q1 q2 d0 d1 r0 r1 r2 c0 c1 finalCarry : Nat)
    (first : r0 + 2^128*c0 = d0+q0)
    (second : r1 + 2^128*c1 = d1+q1+c0)
    (third : r2 + 2^128*finalCarry = q2+c1) :
    l0 + 2^128*r0 + 2^256*r1 + 2^384*r2 + 2^512*finalCarry =
      l0 + 2^128*q0 + 2^256*q1 + 2^384*q2 + 2^128*(d0+2^128*d1) := by
  simp only [Nat.reducePow] at *
  omega


theorem negative_balance (l0 q0 q1 q2 d0 d1 r0 r1 r2 c0 c1 finalCarry : Nat)
    (first : r0 + 2^128*c0 + d0 = q0+2^128)
    (second : r1 + 2^128*c1 + d1 = q1+c0+(2^128-1))
    (third : r2 + 2^128*finalCarry = q2+c1+(2^128-1)) :
    l0 + 2^128*r0 + 2^256*r1 + 2^384*r2 + 2^512*finalCarry +
      2^128*(d0+2^128*d1) =
        l0 + 2^128*q0 + 2^256*q1 + 2^384*q2 + 2^512 := by
  simp only [Nat.reducePow] at *
  omega


theorem bounded_finish (value product base magnitude firstCarry lastCarry : Nat)
    (valueBound : value < 2^512) (productBound : product < 2^512)
    (diagonal : base + 2^512*firstCarry = product + 2^128*magnitude)
    (negative : value + 2^512*lastCarry + 2^128*magnitude = base + 2^512) :
    value = product := by
  simp only [Nat.reducePow] at *
  omega

theorem bounded_positive_finish (value product base magnitude firstCarry lastCarry : Nat)
    (productBound : product < 2^512)
    (diagonal : base + 2^512*firstCarry + 2^128*magnitude = product)
    (positive : value + 2^512*lastCarry = base + 2^128*magnitude) :
    value = product := by
  simp only [Nat.reducePow] at *
  omega

end SecpMath.Karatsuba.Carry128

namespace SecpMath.KaratsubaWord
open ArmCertValue SecpMath.Product

theorem sub2_carry (x y : BitVec 64 × BitVec 64) :
    (HalfWord.sub2 x y).2 = if HalfWord.pairValue y ≤ HalfWord.pairValue x then 1#64 else 0#64 := by
  have balance := HalfWord.sub2_balance x y
  have flag : (HalfWord.sub2 x y).2.toNat ≤ 1 := SecpMath.sbc3C_le_one ..
  have differenceBound := HalfWord.pair_bound (HalfWord.sub2 x y).1
  have xBound := HalfWord.pair_bound x
  have yBound := HalfWord.pair_bound y
  by_cases order : HalfWord.pairValue y ≤ HalfWord.pairValue x
  · have flagNat : (HalfWord.sub2 x y).2.toNat = 1 := by
      simp only [limbRadix] at *
      omega
    simp only [order,↓reduceIte]
    exact BitVec.eq_of_toNat_eq flagNat
  · have flagNat : (HalfWord.sub2 x y).2.toNat = 0 := by
      simp only [limbRadix] at *
      omega
    simp only [order,↓reduceIte]
    exact BitVec.eq_of_toNat_eq flagNat

theorem abs2_nat (x y : BitVec 64 × BitVec 64) :
    HalfWord.pairValue (HalfWord.abs2 x y) = Karatsuba.Signs.magnitude (HalfWord.pairValue x) (HalfWord.pairValue y) := by
  have actual := HalfWord.abs2_correct x y
  unfold Karatsuba.Signs.magnitude
  by_cases order : HalfWord.pairValue y ≤ HalfWord.pairValue x
  all_goals simp only [order,↓reduceIte]
  all_goals rcases actual with forward | backward <;> omega

theorem pair_sign_control (xlo xhi ylo yhi : BitVec 64 × BitVec 64)
    (nx zx vx ny zy vy : BitVec 64) :
    Op.eor.eval [
      (Op.cselc 2#4).eval [ny,zy,(HalfWord.sub2 ylo yhi).2,vy,0#64,18446744073709551615#64],
      (Op.cselc 2#4).eval [nx,zx,(HalfWord.sub2 xhi xlo).2,vx,0#64,18446744073709551615#64]] =
      if ((HalfWord.pairValue xlo ≤ HalfWord.pairValue xhi) ↔
        (HalfWord.pairValue yhi ≤ HalfWord.pairValue ylo)) then 0#64 else 18446744073709551615#64 := by
  simp only [HalfWord.mask_carry,sub2_carry]
  by_cases first : HalfWord.pairValue xlo ≤ HalfWord.pairValue xhi
  all_goals by_cases second : HalfWord.pairValue yhi ≤ HalfWord.pairValue ylo
  all_goals simp only [first,second,↓reduceIte,iff_self,not_false_eq_true,
    not_true_eq_false,iff_true,iff_false,true_iff,false_iff]
  all_goals decide

theorem pair_add_balance (a0 a1 b0 b1 r0 r1 carryIn middle carryOut : Nat)
    (first : r0+limbRadix*middle = a0+b0+carryIn)
    (second : r1+limbRadix*carryOut = a1+b1+middle) :
    (r0+limbRadix*r1)+limbRadix^2*carryOut =
      (a0+limbRadix*a1)+(b0+limbRadix*b1)+carryIn := by
  simp only [limbRadix] at *
  omega

#print axioms sub2_carry
#print axioms abs2_nat
#print axioms pair_sign_control
#print axioms pair_add_balance
theorem pair_complement (x : BitVec 64 × BitVec 64) :
    HalfWord.pairValue (~~~x.1,~~~x.2)+HalfWord.pairValue x = limbRadix^2-1 := by
  have lowBound := x.1.isLt
  have highBound := x.2.isLt
  simp only [HalfWord.pairValue,BitVec.toNat_not,limbRadix] at *
  omega

theorem negative_chunk_first (result carry magnitude complement other : Nat)
    (balance : result+limbRadix^2*carry = complement+other+1)
    (complementEq : complement+magnitude = limbRadix^2-1) :
    result+limbRadix^2*carry+magnitude = other+limbRadix^2 := by
  simp only [limbRadix] at *
  omega

theorem negative_chunk_next (result carry magnitude complement other carryIn : Nat)
    (balance : result+limbRadix^2*carry = complement+other+carryIn)
    (complementEq : complement+magnitude = limbRadix^2-1) :
    result+limbRadix^2*carry+magnitude = other+carryIn+(limbRadix^2-1) := by
  simp only [limbRadix] at *
  omega

theorem diagonal_upper_bound (product top : Nat)
    (productBound : product ≤ (limbRadix^2-1)*(limbRadix^2-1))
    (topBound : top < limbRadix^2) : product+top < (limbRadix^2)^2 := by
  simp only [limbRadix] at *
  omega

#print axioms pair_complement
#print axioms negative_chunk_first
#print axioms negative_chunk_next
#print axioms diagonal_upper_bound

end SecpMath.KaratsubaWord
