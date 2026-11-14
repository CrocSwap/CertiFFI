import SecpMath.HalfWord
import SecpMath.WideWordReduce
import SecpMath.SubSSA
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
namespace SecpMath.MainReduction
open ArmCertValue SecpMath.Addition SecpMath.Product
structure Equations (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords) : Prop where
  row_0 : v n = 977#64
  row_1 : v (n+1) = (Op.orr).eval [v n, 4294967296#64]
  row_2 : v (n+2) = (Op.mul).eval [v (n+1), high.w0]
  row_3 : v (n+3) = (Op.umulh).eval [v (n+1), high.w0]
  row_4 : v (n+4) = (Op.and).eval [high.w1, 4294967295#64]
  row_5 : v (n+5) = (Op.lsr 32).eval [high.w1]
  row_6 : v (n+6) = (Op.mul).eval [v n, v (n+4)]
  row_7 : v (n+7) = (Op.mul).eval [v n, v (n+5)]
  row_8 : v (n+8) = (Op.add).eval [v (n+7), v (n+4)]
  row_9 : v (n+9) = (Op.add).eval [v (n+8), 0#64]
  row_10 : v (n+10) = (Op.lsl 32).eval [v (n+9)]
  row_11 : v (n+11) = (Op.add3).eval [v (n+6), v (n+10), 0#64]
  row_12 : v (n+12) = (Op.add).eval [v (n+11), 0#64]
  row_13 : v (n+13) = (Op.lsl 32).eval [v (n+9)]
  row_15 : v (n+15) = (Op.add).eval [v (n+14), 0#64]
  row_16 : v (n+16) = (Op.lsl 32).eval [v (n+9)]
  row_18 : v (n+18) = (Op.add).eval [v (n+17), 0#64]
  row_19 : v (n+19) = (Op.lsl 32).eval [v (n+9)]
  row_20 : v (n+20) = (Op.carry3).eval [v (n+6), v (n+19), 0#64]
  row_21 : v (n+21) = (Op.add).eval [v (n+20), 0#64]
  row_22 : v (n+22) = (Op.lsl 32).eval [v (n+9)]
  row_24 : v (n+24) = (Op.add).eval [v (n+23), 0#64]
  row_25 : v (n+25) = (Op.lsr 32).eval [v (n+9)]
  row_26 : v (n+26) = (Op.add3).eval [v (n+5), v (n+25), v (n+21)]
  row_27 : v (n+27) = (Op.mul).eval [v (n+1), high.w2]
  row_28 : v (n+28) = (Op.umulh).eval [v (n+1), high.w2]
  row_29 : v (n+29) = (Op.and).eval [high.w3, 4294967295#64]
  row_30 : v (n+30) = (Op.lsr 32).eval [high.w3]
  row_31 : v (n+31) = (Op.mul).eval [v n, v (n+29)]
  row_32 : v (n+32) = (Op.mul).eval [v n, v (n+30)]
  row_33 : v (n+33) = (Op.add).eval [v (n+32), v (n+29)]
  row_34 : v (n+34) = (Op.add).eval [v (n+33), 0#64]
  row_35 : v (n+35) = (Op.lsl 32).eval [v (n+34)]
  row_36 : v (n+36) = (Op.add3).eval [v (n+31), v (n+35), 0#64]
  row_37 : v (n+37) = (Op.add).eval [v (n+36), 0#64]
  row_38 : v (n+38) = (Op.lsl 32).eval [v (n+34)]
  row_40 : v (n+40) = (Op.add).eval [v (n+39), 0#64]
  row_41 : v (n+41) = (Op.lsl 32).eval [v (n+34)]
  row_43 : v (n+43) = (Op.add).eval [v (n+42), 0#64]
  row_44 : v (n+44) = (Op.lsl 32).eval [v (n+34)]
  row_45 : v (n+45) = (Op.carry3).eval [v (n+31), v (n+44), 0#64]
  row_46 : v (n+46) = (Op.add).eval [v (n+45), 0#64]
  row_47 : v (n+47) = (Op.lsl 32).eval [v (n+34)]
  row_49 : v (n+49) = (Op.add).eval [v (n+48), 0#64]
  row_50 : v (n+50) = (Op.lsr 32).eval [v (n+34)]
  row_51 : v (n+51) = (Op.add3).eval [v (n+30), v (n+50), v (n+46)]
  row_52 : v (n+52) = (Op.add3).eval [low.w0, v (n+2), 0#64]
  row_55 : v (n+55) = (Op.carry3).eval [low.w0, v (n+2), 0#64]
  row_57 : v (n+57) = (Op.add3).eval [low.w1, v (n+12), v (n+55)]
  row_60 : v (n+60) = (Op.carry3).eval [low.w1, v (n+12), v (n+55)]
  row_62 : v (n+62) = (Op.add3).eval [low.w2, v (n+27), v (n+60)]
  row_65 : v (n+65) = (Op.carry3).eval [low.w2, v (n+27), v (n+60)]
  row_67 : v (n+67) = (Op.add3).eval [low.w3, v (n+37), v (n+65)]
  row_70 : v (n+70) = (Op.carry3).eval [low.w3, v (n+37), v (n+65)]
  row_72 : v (n+72) = (Op.cond 2#4).eval [v (n+68), v (n+69), v (n+70), v (n+71)]
  row_73 : v (n+73) = (Op.add3).eval [v (n+57), v (n+3), 0#64]
  row_76 : v (n+76) = (Op.carry3).eval [v (n+57), v (n+3), 0#64]
  row_78 : v (n+78) = (Op.add3).eval [v (n+62), v (n+26), v (n+76)]
  row_81 : v (n+81) = (Op.carry3).eval [v (n+62), v (n+26), v (n+76)]
  row_83 : v (n+83) = (Op.add3).eval [v (n+67), v (n+28), v (n+81)]
  row_86 : v (n+86) = (Op.carry3).eval [v (n+67), v (n+28), v (n+81)]
  row_88 : v (n+88) = (Op.add3).eval [v (n+72), v (n+51), v (n+86)]
  row_89 : v (n+89) = (Op.add).eval [v (n+88), 1#64]
  row_90 : v (n+90) = (Op.mul).eval [v n, v (n+89)]
  row_91 : v (n+91) = (Op.lsr 32).eval [v (n+89)]
  row_92 : v (n+92) = (Op.lsl 32).eval [v (n+89)]
  row_93 : v (n+93) = (Op.add3).eval [v (n+90), v (n+92), 0#64]
  row_94 : v (n+94) = (Op.add).eval [v (n+93), 0#64]
  row_95 : v (n+95) = (Op.lsl 32).eval [v (n+89)]
  row_97 : v (n+97) = (Op.add).eval [v (n+96), 0#64]
  row_98 : v (n+98) = (Op.lsl 32).eval [v (n+89)]
  row_100 : v (n+100) = (Op.add).eval [v (n+99), 0#64]
  row_101 : v (n+101) = (Op.lsl 32).eval [v (n+89)]
  row_102 : v (n+102) = (Op.carry3).eval [v (n+90), v (n+101), 0#64]
  row_103 : v (n+103) = (Op.add).eval [v (n+102), 0#64]
  row_104 : v (n+104) = (Op.lsl 32).eval [v (n+89)]
  row_106 : v (n+106) = (Op.add).eval [v (n+105), 0#64]
  row_107 : v (n+107) = (Op.add3).eval [0#64, v (n+91), v (n+103)]
  row_108 : v (n+108) = (Op.add3).eval [v (n+52), v (n+94), 0#64]
  row_111 : v (n+111) = (Op.carry3).eval [v (n+52), v (n+94), 0#64]
  row_113 : v (n+113) = (Op.add3).eval [v (n+73), v (n+107), v (n+111)]
  row_116 : v (n+116) = (Op.carry3).eval [v (n+73), v (n+107), v (n+111)]
  row_118 : v (n+118) = (Op.add3).eval [v (n+78), 0#64, v (n+116)]
  row_121 : v (n+121) = (Op.carry3).eval [v (n+78), 0#64, v (n+116)]
  row_123 : v (n+123) = (Op.add3).eval [v (n+83), 0#64, v (n+121)]
  row_126 : v (n+126) = (Op.carry3).eval [v (n+83), 0#64, v (n+121)]
  row_128 : v (n+128) = (Op.cselc 3#4).eval [v (n+124), v (n+125), v (n+126), v (n+127), v (n+1), 0#64]
  row_129 : v (n+129) = (Op.sbc3).eval [v (n+108), v (n+128), 1#64]
  row_132 : v (n+132) = (Op.sbc3C).eval [v (n+108), v (n+128), 1#64]
  row_134 : v (n+134) = (Op.sbc3).eval [v (n+113), 0#64, v (n+132)]
  row_137 : v (n+137) = (Op.sbc3C).eval [v (n+113), 0#64, v (n+132)]
  row_139 : v (n+139) = (Op.sbc3).eval [v (n+118), 0#64, v (n+137)]
  row_142 : v (n+142) = (Op.sbc3C).eval [v (n+118), 0#64, v (n+137)]
  row_144 : v (n+144) = (Op.sbc3).eval [v (n+123), 0#64, v (n+142)]

def first (v : Nat → BitVec 64) (n : Nat) : WideWords :=
  ⟨⟨v (n+52),v (n+73),v (n+78),v (n+83)⟩,v (n+88)⟩
def resultWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+129),v (n+134),v (n+139),v (n+144)⟩

theorem materialized_constant (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords)
    (rows : Equations v n low high) : v (n+1) = BitVec.ofNat 64 correction := by
  rw [rows.row_1,rows.row_0]
  decide

private theorem half_products (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords)
    (rows : Equations v n low high) :
    v (n+12) = HalfWord.correctionLow high.w1 ∧
    v (n+26) = HalfWord.correctionHigh high.w1 ∧
    v (n+37) = HalfWord.correctionLow high.w3 ∧
    v (n+51) = HalfWord.correctionHigh high.w3 := by
  constructor
  · simp only [rows.row_12, rows.row_11, rows.row_10, rows.row_9, rows.row_8, rows.row_7, rows.row_6, rows.row_5, rows.row_4, rows.row_0, HalfWord.correctionLow, HalfWord.correctionMiddle,
      HalfWord.correctionCarry, HalfWord.low32, HalfWord.high32, HalfWord.add_zero] <;> rfl
  constructor
  · simp only [rows.row_26, rows.row_25, rows.row_21, rows.row_20, rows.row_19, rows.row_9, rows.row_8, rows.row_7, rows.row_6, rows.row_5, rows.row_4, rows.row_0, HalfWord.correctionHigh, HalfWord.correctionMiddle,
      HalfWord.correctionCarry, HalfWord.low32, HalfWord.high32, HalfWord.add_zero] <;> rfl
  constructor
  · simp only [rows.row_37, rows.row_36, rows.row_35, rows.row_34, rows.row_33, rows.row_32, rows.row_31, rows.row_30, rows.row_29, rows.row_0, HalfWord.correctionLow, HalfWord.correctionMiddle,
      HalfWord.correctionCarry, HalfWord.low32, HalfWord.high32, HalfWord.add_zero] <;> rfl
  · simp only [rows.row_51, rows.row_50, rows.row_46, rows.row_45, rows.row_44, rows.row_34, rows.row_33, rows.row_32, rows.row_31, rows.row_30, rows.row_29, rows.row_0, HalfWord.correctionHigh, HalfWord.correctionMiddle,
      HalfWord.correctionCarry, HalfWord.low32, HalfWord.high32, HalfWord.add_zero] <;> rfl

theorem first_computed (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords)
    (rows : Equations v n low high) :
    WordMulAdd.mulAdd4 low (BitVec.ofNat 64 correction) high = first v n := by
  have halfs := half_products v n low high rows
  have p1 := HalfWord.correction_pair high.w1
  rw [← halfs.1,← halfs.2.1] at p1
  have p1lo := congrArg Prod.fst p1
  have p1hi := congrArg Prod.snd p1
  have p3 := HalfWord.correction_pair high.w3
  rw [← halfs.2.2.1,← halfs.2.2.2] at p3
  have p3lo := congrArg Prod.fst p3
  have p3hi := congrArg Prod.snd p3
  simp only [Prod.fst,Prod.snd] at p1lo p1hi p3lo p3hi
  rw [← materialized_constant v n low high rows] at p1lo p1hi p3lo p3hi
  have flagBound : (v (n+70)).toNat ≤ 1 := by
    rw [rows.row_70]
    exact Addition.carry3_le_one ..
  have selected : v (n+72) = v (n+70) := by
    rw [rows.row_72]
    exact WordMulAdd.condition_carry _ _ _ _ flagBound
  have top : Op.add3.eval [v (n+51),v (n+70),v (n+86)] = v (n+88) := by
    rw [rows.row_88,selected]
    exact WordMulAdd.add_swap _ _ _
  simp only [WordMulAdd.mulAdd4,WordMulAdd.lowProducts,WordMulAdd.highProducts,
    Addition.coreChain4,first,← p1lo,← p1hi,← p3lo,← p3hi,
    ← materialized_constant v n low high rows,
    ← rows.row_2, ← rows.row_3, ← rows.row_27, ← rows.row_28, ← rows.row_52, ← rows.row_55, ← rows.row_57, ← rows.row_60, ← rows.row_62, ← rows.row_65, ← rows.row_67, ← rows.row_70, ← rows.row_73, ← rows.row_76, ← rows.row_78, ← rows.row_81, ← rows.row_83, ← rows.row_86, ← rows.row_88, WordMulAdd.add_zero,WordMulAdd.carry_zero,top]

theorem first_balance (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords)
    (rows : Equations v n low high) :
    (first v n).value = low.value+correction*high.value := by
  rw [← first_computed v n low high rows,WordMulAdd.mulAdd4_correct]
  rfl
#print axioms first_computed
#print axioms first_balance
theorem first_fold_eq (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords)
    (rows : Equations v n low high) :
    (first v n).value = WideReduction.firstFold (low.value+radix*high.value) := by
  have lowBound := low.value_lt
  have parts : (low.value+radix*high.value)%radix = low.value ∧
      (low.value+radix*high.value)/radix = high.value := by
    simp only [radix] at *
    omega
  rw [first_balance v n low high rows]
  simp only [WideReduction.firstFold,parts.1,parts.2]

theorem first_bound (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords)
    (rows : Equations v n low high) :
    (first v n).value < (limbRadix-1)*modulus := by
  rw [first_fold_eq v n low high rows]
  apply WideReduction.firstFold_bound
  have lowBound := low.value_lt
  have highBound := high.value_lt
  simp only [radix] at *
  omega

private theorem quotient_fit (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords)
    (rows : Equations v n low high) : 977*(v (n+89)).toNat < limbRadix := by
  have balanced := first_balance v n low high rows
  have lowBound := low.value_lt
  have highBound := high.value_lt
  have parts := (first v n).parts.2
  have fit := ConstantMultiply.quotient_fits _ (first_bound v n low high rows)
  unfold ConstantMultiply.quotient at fit
  rw [← parts] at fit
  have qnat := CoreConstantMultiply.quotientWord_toNat (first v n) fit
  change (Op.add.eval [v (n+88),1#64]).toNat = (v (n+88)).toNat+1 at qnat
  rw [← rows.row_89] at qnat
  have totalParts := (first v n).parts
  simp only [first,WideWords.value,radix,limbRadix,correction] at balanced lowBound highBound fit qnat ⊢
  have firstLowBound := (first v n).low.value_lt
  simp only [radix] at firstLowBound
  omega

theorem quotient_fold (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords)
    (rows : Equations v n low high) :
    WideWordReduce.foldedChain (first v n) =
      (⟨v (n+108),v (n+113),v (n+118),v (n+123)⟩,v (n+126)) := by
  have optimized : (v (n+94),v (n+107)) =
      (HalfWord.quotientLow (v (n+89)),HalfWord.quotientHigh (v (n+89))) := by
    simp only [rows.row_107,rows.row_103,rows.row_102,rows.row_101,rows.row_94,rows.row_93,
      rows.row_92,rows.row_91,rows.row_90,rows.row_0,
      HalfWord.quotientLow,HalfWord.quotientHigh,HalfWord.quotientCarry,HalfWord.high32,HalfWord.add_zero]
  have products := optimized.trans (HalfWord.quotient_pair (v (n+89)) (quotient_fit v n low high rows))
  have p0 := congrArg Prod.fst products
  have p1 := congrArg Prod.snd products
  simp only [Prod.fst,Prod.snd] at p0 p1
  simp only [WideWordReduce.foldedChain,CoreConstantMultiply.quotientWord,first,
    CoreConstantMultiply.correctionProduct,Addition.coreChain4,
    ← rows.row_89,← p0,← p1,← rows.row_108,← rows.row_111,
    ← rows.row_113,← rows.row_116,← rows.row_118,← rows.row_121,
    ← rows.row_123,← rows.row_126]

theorem selected_value (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords)
    (rows : Equations v n low high) :
    v (n+128) = if v (n+126) == 0#64 then BitVec.ofNat 64 correction else 0#64 := by
  rw [rows.row_128,materialized_constant v n low high rows]
  exact SubSSA.select_correction _ _ _ _

theorem rows_reduce4 (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords)
    (rows : Equations v n low high) : resultWords v n = WideWordReduce.reduce4 (first v n) := by
  unfold WideWordReduce.reduce4
  rw [quotient_fold v n low high rows]
  simp only [SecpMath.coreChain4,correctionWords,← selected_value v n low high rows,
    ← rows.row_129,← rows.row_132,← rows.row_134,← rows.row_137,
    ← rows.row_139,← rows.row_142,← rows.row_144,resultWords]

theorem correct (v : Nat → BitVec 64) (n : Nat) (low high : LimbWords)
    (rows : Equations v n low high) :
    (resultWords v n).value < modulus ∧
      (resultWords v n).value = (low.value+radix*high.value)%modulus := by
  rw [rows_reduce4 v n low high rows]
  have reduced := WideWordReduce.reduce4_correct (first v n) (first_bound v n low high rows)
  rw [first_fold_eq v n low high rows] at reduced
  exact ⟨reduced.1,reduced.2.trans (WideReduction.firstFold_mod _)⟩
#print axioms first_fold_eq
#print axioms first_bound
#print axioms quotient_fit
#print axioms quotient_fold
#print axioms rows_reduce4
#print axioms correct

end SecpMath.MainReduction
