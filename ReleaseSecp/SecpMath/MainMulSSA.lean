import SecpMath.MainMulRows
import SecpMath.KaratsubaWord
import SecpMath.MainReduction
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
namespace SecpMath.MainMulSSA
open ArmCertValue SecpMath.Addition SecpMath.Product

def productLow (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+4),v (n+55),v (n+289),v (n+295)⟩
def productHigh (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+301),v (n+307),v (n+312),v (n+317)⟩
def resultWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+447),v (n+452),v (n+457),v (n+462)⟩

private theorem core_low (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    (⟨(v (n+4)),(v (n+55)),(v (n+61)),(v (n+66))⟩ : LimbWords) = KaratsubaWord.core128 (v n) (v (n+1)) (v (n+2)) (v (n+3)) := by
  have absA : (v (n+16)) = KaratsubaWord.magnitudeWord (v (n+1)) (v n) := by
    simp only [rows.row_16,rows.row_15,rows.row_13,rows.row_14,rows.row_8,rows.row_11,HalfWord.add_zero]
    exact KaratsubaWord.magnitude_control (v (n+1)) (v n) (v (n+9)) (v (n+10)) (v (n+12))
  have absB : (v (n+32)) = KaratsubaWord.magnitudeWord (v (n+2)) (v (n+3)) := by
    simp only [rows.row_32,rows.row_31,rows.row_29,rows.row_30,rows.row_24,rows.row_27,HalfWord.add_zero]
    exact KaratsubaWord.magnitude_control (v (n+2)) (v (n+3)) (v (n+25)) (v (n+26)) (v (n+28))
  have mask : (v (n+36)) = KaratsubaWord.signMask (v n) (v (n+1)) (v (n+2)) (v (n+3)) := by
    simp only [rows.row_36,rows.row_35,rows.row_33,rows.row_34,rows.row_17,rows.row_11,rows.row_27,HalfWord.add_zero]
    exact KaratsubaWord.sign_control (v n) (v (n+1)) (v (n+2)) (v (n+3)) (v (n+9)) (v (n+10)) (v (n+12)) (v (n+25)) (v (n+26)) (v (n+28))
  have base : (KaratsubaWord.diagonalWords (v (n+4)) (v (n+5)) (v (n+6)) (v (n+7))).1 =
      (⟨(v (n+4)),(v (n+39)),(v (n+44)),(v (n+49))⟩ : LimbWords) := by
    simp only [KaratsubaWord.diagonalWords,← rows.row_18,← rows.row_21,← rows.row_23,← rows.row_39,← rows.row_42,← rows.row_44,← rows.row_47,← rows.row_49]
  symm
  simp only [KaratsubaWord.core128,← rows.row_4,← rows.row_5,← rows.row_6,← rows.row_7,base,← absA,← absB,
    ← rows.row_37,← rows.row_38,← mask,KaratsubaWord.signedWords,
    ← rows.row_52,← rows.row_54,← rows.row_55,← rows.row_58,← rows.row_60,← rows.row_61,← rows.row_64,← rows.row_66]

private theorem product_low (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    (⟨(v (n+4)),(v (n+55)),(v (n+61)),(v (n+66))⟩ : LimbWords).value =
      ((v n).toNat+limbRadix*(v (n+1)).toNat)*((v (n+2)).toNat+limbRadix*(v (n+3)).toNat) := by
  rw [core_low v n rows]
  exact KaratsubaWord.core128_correct (v n) (v (n+1)) (v (n+2)) (v (n+3))
#print axioms product_low

private theorem core_high (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    (⟨(v (n+71)),(v (n+122)),(v (n+128)),(v (n+133))⟩ : LimbWords) = KaratsubaWord.core128 (v (n+67)) (v (n+68)) (v (n+69)) (v (n+70)) := by
  have absA : (v (n+83)) = KaratsubaWord.magnitudeWord (v (n+68)) (v (n+67)) := by
    simp only [rows.row_83,rows.row_82,rows.row_80,rows.row_81,rows.row_75,rows.row_78,HalfWord.add_zero]
    exact KaratsubaWord.magnitude_control (v (n+68)) (v (n+67)) (v (n+76)) (v (n+77)) (v (n+79))
  have absB : (v (n+99)) = KaratsubaWord.magnitudeWord (v (n+69)) (v (n+70)) := by
    simp only [rows.row_99,rows.row_98,rows.row_96,rows.row_97,rows.row_91,rows.row_94,HalfWord.add_zero]
    exact KaratsubaWord.magnitude_control (v (n+69)) (v (n+70)) (v (n+92)) (v (n+93)) (v (n+95))
  have mask : (v (n+103)) = KaratsubaWord.signMask (v (n+67)) (v (n+68)) (v (n+69)) (v (n+70)) := by
    simp only [rows.row_103,rows.row_102,rows.row_100,rows.row_101,rows.row_84,rows.row_78,rows.row_94,HalfWord.add_zero]
    exact KaratsubaWord.sign_control (v (n+67)) (v (n+68)) (v (n+69)) (v (n+70)) (v (n+76)) (v (n+77)) (v (n+79)) (v (n+92)) (v (n+93)) (v (n+95))
  have base : (KaratsubaWord.diagonalWords (v (n+71)) (v (n+72)) (v (n+73)) (v (n+74))).1 =
      (⟨(v (n+71)),(v (n+106)),(v (n+111)),(v (n+116))⟩ : LimbWords) := by
    simp only [KaratsubaWord.diagonalWords,← rows.row_85,← rows.row_88,← rows.row_90,← rows.row_106,← rows.row_109,← rows.row_111,← rows.row_114,← rows.row_116]
  symm
  simp only [KaratsubaWord.core128,← rows.row_71,← rows.row_72,← rows.row_73,← rows.row_74,base,← absA,← absB,
    ← rows.row_104,← rows.row_105,← mask,KaratsubaWord.signedWords,
    ← rows.row_119,← rows.row_121,← rows.row_122,← rows.row_125,← rows.row_127,← rows.row_128,← rows.row_131,← rows.row_133]

private theorem product_high (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    (⟨(v (n+71)),(v (n+122)),(v (n+128)),(v (n+133))⟩ : LimbWords).value =
      ((v (n+67)).toNat+limbRadix*(v (n+68)).toNat)*((v (n+69)).toNat+limbRadix*(v (n+70)).toNat) := by
  rw [core_high v n rows]
  exact KaratsubaWord.core128_correct (v (n+67)) (v (n+68)) (v (n+69)) (v (n+70))
#print axioms product_high

private theorem core_cross (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    (⟨(v (n+195)),(v (n+246)),(v (n+252)),(v (n+257))⟩ : LimbWords) = KaratsubaWord.core128 (v (n+163)) (v (n+169)) (v (n+171)) (v (n+177)) := by
  have absA : (v (n+207)) = KaratsubaWord.magnitudeWord (v (n+169)) (v (n+163)) := by
    simp only [rows.row_207,rows.row_206,rows.row_204,rows.row_205,rows.row_199,rows.row_202,HalfWord.add_zero]
    exact KaratsubaWord.magnitude_control (v (n+169)) (v (n+163)) (v (n+200)) (v (n+201)) (v (n+203))
  have absB : (v (n+223)) = KaratsubaWord.magnitudeWord (v (n+171)) (v (n+177)) := by
    simp only [rows.row_223,rows.row_222,rows.row_220,rows.row_221,rows.row_215,rows.row_218,HalfWord.add_zero]
    exact KaratsubaWord.magnitude_control (v (n+171)) (v (n+177)) (v (n+216)) (v (n+217)) (v (n+219))
  have mask : (v (n+227)) = KaratsubaWord.signMask (v (n+163)) (v (n+169)) (v (n+171)) (v (n+177)) := by
    simp only [rows.row_227,rows.row_226,rows.row_224,rows.row_225,rows.row_208,rows.row_202,rows.row_218,HalfWord.add_zero]
    exact KaratsubaWord.sign_control (v (n+163)) (v (n+169)) (v (n+171)) (v (n+177)) (v (n+200)) (v (n+201)) (v (n+203)) (v (n+216)) (v (n+217)) (v (n+219))
  have base : (KaratsubaWord.diagonalWords (v (n+195)) (v (n+196)) (v (n+197)) (v (n+198))).1 =
      (⟨(v (n+195)),(v (n+230)),(v (n+235)),(v (n+240))⟩ : LimbWords) := by
    simp only [KaratsubaWord.diagonalWords,← rows.row_209,← rows.row_212,← rows.row_214,← rows.row_230,← rows.row_233,← rows.row_235,← rows.row_238,← rows.row_240]
  symm
  simp only [KaratsubaWord.core128,← rows.row_195,← rows.row_196,← rows.row_197,← rows.row_198,base,← absA,← absB,
    ← rows.row_228,← rows.row_229,← mask,KaratsubaWord.signedWords,
    ← rows.row_243,← rows.row_245,← rows.row_246,← rows.row_249,← rows.row_251,← rows.row_252,← rows.row_255,← rows.row_257]

private theorem product_cross (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    (⟨(v (n+195)),(v (n+246)),(v (n+252)),(v (n+257))⟩ : LimbWords).value =
      ((v (n+163)).toNat+limbRadix*(v (n+169)).toNat)*((v (n+171)).toNat+limbRadix*(v (n+177)).toNat) := by
  rw [core_cross v n rows]
  exact KaratsubaWord.core128_correct (v (n+163)) (v (n+169)) (v (n+171)) (v (n+177))
#print axioms product_cross
structure LoadsAgree (v : Nat → BitVec 64) (n : Nat) : Prop where
  xHigh0 : v (n+134) = v (n+67)
  xHigh1 : v (n+135) = v (n+68)
  xLow0 : v (n+136) = v n
  xLow1 : v (n+137) = v (n+1)
  yLow0 : v (n+149) = v (n+2)
  yLow1 : v (n+150) = v (n+3)

private theorem cross_words_x (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    (v (n+163),v (n+169)) = HalfWord.abs2 (v (n+134),v (n+135)) (v (n+136),v (n+137)) := by
  simp only [rows.row_169,rows.row_168,rows.row_166,rows.row_163,rows.row_162,
    rows.row_148,rows.row_146,rows.row_143,rows.row_141,rows.row_138,
    HalfWord.abs2,HalfWord.sub2,HalfWord.negate2,HalfWord.mask_carry] <;> rfl

private theorem cross_words_y (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    (v (n+171),v (n+177)) = HalfWord.abs2 (v (n+149),v (n+150)) (v (n+69),v (n+70)) := by
  simp only [rows.row_177,rows.row_176,rows.row_174,rows.row_171,rows.row_170,
    rows.row_161,rows.row_159,rows.row_156,rows.row_154,rows.row_151,
    HalfWord.abs2,HalfWord.sub2,HalfWord.negate2,HalfWord.mask_carry] <;> rfl

private theorem outer_mask (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n)
    (loads : LoadsAgree v n) :
    v (n+178) = if ((HalfWord.pairValue (v n,v (n+1)) ≤ HalfWord.pairValue (v (n+67),v (n+68))) ↔
      (HalfWord.pairValue (v (n+69),v (n+70)) ≤ HalfWord.pairValue (v (n+2),v (n+3))))
      then 0#64 else 18446744073709551615#64 := by
  have actual : v (n+178) =
      if ((HalfWord.pairValue (v (n+136),v (n+137)) ≤ HalfWord.pairValue (v (n+134),v (n+135))) ↔
        (HalfWord.pairValue (v (n+69),v (n+70)) ≤ HalfWord.pairValue (v (n+149),v (n+150))))
        then 0#64 else 18446744073709551615#64 := by
    rw [rows.row_178,rows.row_161,rows.row_148,rows.row_159,rows.row_154,rows.row_146,rows.row_141]
    simpa only [HalfWord.sub2] using KaratsubaWord.pair_sign_control
      (v (n+136),v (n+137)) (v (n+134),v (n+135)) (v (n+149),v (n+150)) (v (n+69),v (n+70))
      (v (n+144)) (v (n+145)) (v (n+147)) (v (n+157)) (v (n+158)) (v (n+160))
  simpa only [loads.xHigh0,loads.xHigh1,loads.xLow0,loads.xLow1,loads.yLow0,loads.yLow1] using actual
#print axioms cross_words_x
#print axioms cross_words_y
#print axioms outer_mask

private theorem duplicate_inputs (inputs : List (BitVec 64)) (defs : List Def) (n xs ys : Nat)
    (lengthEq : inputs.length = n) (pos : LoadPositions defs xs ys)
    (insideX : xs+32 ≤ n) (insideY : ys+32 ≤ n) :
    LoadsAgree (fun i => (evalDefs inputs defs).getD i 0) n := by
  constructor
  · have first := SubSSA.loaded_input_word inputs defs 134 (xs+16) pos.load_134 (by omega)
    have second := SubSSA.loaded_input_word inputs defs 67 (xs+16) pos.load_67 (by omega)
    simpa only [lengthEq,Nat.add_zero] using first.trans second.symm
  · have first := SubSSA.loaded_input_word inputs defs 135 (xs+24) pos.load_135 (by omega)
    have second := SubSSA.loaded_input_word inputs defs 68 (xs+24) pos.load_68 (by omega)
    simpa only [lengthEq,Nat.add_zero] using first.trans second.symm
  · have first := SubSSA.loaded_input_word inputs defs 136 xs pos.load_136 (by omega)
    have second := SubSSA.loaded_input_word inputs defs 0 xs pos.load_0 (by omega)
    simpa only [lengthEq,Nat.add_zero] using first.trans second.symm
  · have first := SubSSA.loaded_input_word inputs defs 137 (xs+8) pos.load_137 (by omega)
    have second := SubSSA.loaded_input_word inputs defs 1 (xs+8) pos.load_1 (by omega)
    simpa only [lengthEq,Nat.add_zero] using first.trans second.symm
  · have first := SubSSA.loaded_input_word inputs defs 149 ys pos.load_149 (by omega)
    have second := SubSSA.loaded_input_word inputs defs 2 ys pos.load_2 (by omega)
    simpa only [lengthEq,Nat.add_zero] using first.trans second.symm
  · have first := SubSSA.loaded_input_word inputs defs 150 (ys+8) pos.load_150 (by omega)
    have second := SubSSA.loaded_input_word inputs defs 3 (ys+8) pos.load_3 (by omega)
    simpa only [lengthEq,Nat.add_zero] using first.trans second.symm
#print axioms duplicate_inputs


private def pairValueAt (v : Nat → BitVec 64) (n i j : Nat) : Nat :=
  HalfWord.pairValue (v (n + i),v (n + j))
private def leftValue (v : Nat → BitVec 64) (n : Nat) : Nat :=
  (⟨v (n+4),v (n+55),v (n+61),v (n+66)⟩ : LimbWords).value
private def rightValue (v : Nat → BitVec 64) (n : Nat) : Nat :=
  (⟨v (n+71),v (n+122),v (n+128),v (n+133)⟩ : LimbWords).value
private def middleValue (v : Nat → BitVec 64) (n : Nat) : Nat :=
  (⟨v (n+195),v (n+246),v (n+252),v (n+257)⟩ : LimbWords).value
private def diagonalValue (v : Nat → BitVec 64) (n : Nat) : Nat :=
  pairValueAt v n 4 55+2^128*pairValueAt v n 258 263+
    2^256*pairValueAt v n 268 273+2^384*pairValueAt v n 278 283

private theorem diagonal_current (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n)
    (upperBound : rightValue v n+pairValueAt v n 61 66 < 2^256) :
    ∃ carry : Nat, diagonalValue v n+2^512*carry =
      leftValue v n+2^128*(leftValue v n+rightValue v n)+2^256*rightValue v n := by
  have groupedBound : pairValueAt v n 71 122+2^128*pairValueAt v n 128 133+
      pairValueAt v n 61 66 < 2^256 := by
    simp only [rightValue,pairValueAt,HalfWord.pairValue,LimbWords.value,pack4,limbRadix] at upperBound ⊢
    omega
  have balance_179 := Product.add_balance (v (n+71)) (v (n+61)) (0#64) (by decide)
  rw [← rows.row_179,← rows.row_182] at balance_179
  have balance_184 := Product.add_balance (v (n+122)) (v (n+66)) (v (n+182)) (by rw [rows.row_182]; exact Addition.carry3_le_one ..)
  rw [← rows.row_184,← rows.row_187] at balance_184
  have balance_189 := Product.add_balance (v (n+128)) (0#64) (v (n+187)) (by rw [rows.row_187]; exact Addition.carry3_le_one ..)
  rw [← rows.row_189,← rows.row_192] at balance_189
  have balance_194 := Product.add_balance (v (n+133)) (0#64) (v (n+192)) (by rw [rows.row_192]; exact Addition.carry3_le_one ..)
  rw [← rows.row_194] at balance_194
  generalize overflow_eq_194 : (Op.carry3.eval [v (n+133),0#64,v (n+192)]).toNat = overflow_194 at balance_194
  clear overflow_eq_194
  have balance_258 := Product.add_balance (v (n+179)) (v (n+4)) (0#64) (by decide)
  rw [← rows.row_258,← rows.row_261] at balance_258
  have balance_263 := Product.add_balance (v (n+184)) (v (n+55)) (v (n+261)) (by rw [rows.row_261]; exact Addition.carry3_le_one ..)
  rw [← rows.row_263,← rows.row_266] at balance_263
  have balance_268 := Product.add_balance (v (n+189)) (v (n+179)) (v (n+266)) (by rw [rows.row_266]; exact Addition.carry3_le_one ..)
  rw [← rows.row_268,← rows.row_271] at balance_268
  have balance_273 := Product.add_balance (v (n+194)) (v (n+184)) (v (n+271)) (by rw [rows.row_271]; exact Addition.carry3_le_one ..)
  rw [← rows.row_273,← rows.row_276] at balance_273
  have balance_278 := Product.add_balance (v (n+189)) (0#64) (v (n+276)) (by rw [rows.row_276]; exact Addition.carry3_le_one ..)
  rw [← rows.row_278,← rows.row_281] at balance_278
  have balance_283 := Product.add_balance (v (n+194)) (0#64) (v (n+281)) (by rw [rows.row_281]; exact Addition.carry3_le_one ..)
  rw [← rows.row_283] at balance_283
  generalize overflow_eq_283 : (Op.carry3.eval [v (n+194),0#64,v (n+281)]).toNat = overflow_283 at balance_283
  clear overflow_eq_283
  have chunk0 := KaratsubaWord.pair_add_balance ((v (n+71)).toNat) ((v (n+122)).toNat) ((v (n+61)).toNat) ((v (n+66)).toNat) ((v (n+179)).toNat) ((v (n+184)).toNat) (0) ((v (n+182)).toNat) ((v (n+187)).toNat)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_179)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_184)
  have chunk1 := KaratsubaWord.pair_add_balance ((v (n+128)).toNat) ((v (n+133)).toNat) (0) (0) ((v (n+189)).toNat) ((v (n+194)).toNat) ((v (n+187)).toNat) ((v (n+192)).toNat) (overflow_194)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_189)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_194)
  have chunk2 := KaratsubaWord.pair_add_balance ((v (n+179)).toNat) ((v (n+184)).toNat) ((v (n+4)).toNat) ((v (n+55)).toNat) ((v (n+258)).toNat) ((v (n+263)).toNat) (0) ((v (n+261)).toNat) ((v (n+266)).toNat)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_258)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_263)
  have chunk3 := KaratsubaWord.pair_add_balance ((v (n+189)).toNat) ((v (n+194)).toNat) ((v (n+179)).toNat) ((v (n+184)).toNat) ((v (n+268)).toNat) ((v (n+273)).toNat) ((v (n+266)).toNat) ((v (n+271)).toNat) ((v (n+276)).toNat)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_268)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_273)
  have chunk4 := KaratsubaWord.pair_add_balance ((v (n+189)).toNat) ((v (n+194)).toNat) (0) (0) ((v (n+278)).toNat) ((v (n+283)).toNat) ((v (n+276)).toNat) ((v (n+281)).toNat) (overflow_283)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_278)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_283)
  have balanced := Karatsuba.Carry128.diagonal_balance
    (pairValueAt v n 4 55) (pairValueAt v n 61 66) (pairValueAt v n 71 122) (pairValueAt v n 128 133)
    (pairValueAt v n 179 184) (pairValueAt v n 189 194)
    (pairValueAt v n 258 263) (pairValueAt v n 268 273) (pairValueAt v n 278 283)
    (v (n+187)).toNat overflow_194 (v (n+266)).toNat (v (n+276)).toNat overflow_283
    groupedBound
    (by simpa only [pairValueAt,HalfWord.pairValue,limbRadix,Nat.add_zero] using chunk0)
    (by simpa only [pairValueAt,HalfWord.pairValue,limbRadix,Nat.mul_zero,Nat.add_zero,Nat.zero_add] using chunk1)
    (by simpa only [pairValueAt,HalfWord.pairValue,limbRadix,Nat.add_zero,Nat.zero_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using chunk2)
    (by simpa only [pairValueAt,HalfWord.pairValue,limbRadix,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using chunk3)
    (by simpa only [pairValueAt,HalfWord.pairValue,limbRadix,Nat.mul_zero,Nat.add_zero,Nat.zero_add] using chunk4)
  refine ⟨overflow_283,?_⟩
  have exactBalance := balanced.2
  clear rows upperBound groupedBound balanced balance_179 balance_184 balance_189 balance_194 balance_258 balance_263 balance_268 balance_273 balance_278 balance_283 chunk0 chunk1 chunk2 chunk3 chunk4 overflow_194
  simp only [leftValue,rightValue,diagonalValue,pairValueAt,HalfWord.pairValue,LimbWords.value,pack4,limbRadix] at exactBalance ⊢
  omega
#print axioms diagonal_current

private theorem signed_positive_current (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n)
    (mask : v (n+178) = 0#64) :
    ∃ carry : Nat, (productLow v n).value+radix*(productHigh v n).value+2^512*carry = diagonalValue v n+2^128*middleValue v n := by
  have balance_289 := Product.add_balance (v (n+288)) (v (n+258)) (v (n+286)) (by rw [rows.row_286]; exact Addition.carry3_le_one ..)
  rw [← rows.row_289,← rows.row_292] at balance_289
  have balance_295 := Product.add_balance (v (n+294)) (v (n+263)) (v (n+292)) (by rw [rows.row_292]; exact Addition.carry3_le_one ..)
  rw [← rows.row_295,← rows.row_298] at balance_295
  have balance_301 := Product.add_balance (v (n+300)) (v (n+268)) (v (n+298)) (by rw [rows.row_298]; exact Addition.carry3_le_one ..)
  rw [← rows.row_301,← rows.row_304] at balance_301
  have balance_307 := Product.add_balance (v (n+306)) (v (n+273)) (v (n+304)) (by rw [rows.row_304]; exact Addition.carry3_le_one ..)
  rw [← rows.row_307,← rows.row_310] at balance_307
  have balance_312 := Product.add_balance (v (n+278)) (v (n+178)) (v (n+310)) (by rw [rows.row_310]; exact Addition.carry3_le_one ..)
  rw [← rows.row_312,← rows.row_315] at balance_312
  have balance_317 := Product.add_balance (v (n+283)) (v (n+178)) (v (n+315)) (by rw [rows.row_315]; exact Addition.carry3_le_one ..)
  rw [← rows.row_317] at balance_317
  generalize overflow_eq_317 : (Op.carry3.eval [v (n+283),v (n+178),v (n+315)]).toNat = overflow_317 at balance_317
  clear overflow_eq_317
  have start : v (n+286) = 0#64 := by
    rw [rows.row_286,mask]
    exact KaratsubaWord.zero_carry
  have xor_288 : v (n+288) = v (n+195) := by
    rw [rows.row_288,mask]
    exact KaratsubaWord.xor_zero _
  have xor_294 : v (n+294) = v (n+246) := by
    rw [rows.row_294,mask]
    exact KaratsubaWord.xor_zero _
  have xor_300 : v (n+300) = v (n+252) := by
    rw [rows.row_300,mask]
    exact KaratsubaWord.xor_zero _
  have xor_306 : v (n+306) = v (n+257) := by
    rw [rows.row_306,mask]
    exact KaratsubaWord.xor_zero _
  simp only [mask,start,xor_288,xor_294,xor_300,xor_306,BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] at balance_289 balance_295 balance_301 balance_307 balance_312 balance_317
  have chunk0 := KaratsubaWord.pair_add_balance ((v (n+195)).toNat) ((v (n+246)).toNat) ((v (n+258)).toNat) ((v (n+263)).toNat) ((v (n+289)).toNat) ((v (n+295)).toNat) (0) ((v (n+292)).toNat) ((v (n+298)).toNat)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_289)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_295)
  have chunk1 := KaratsubaWord.pair_add_balance ((v (n+252)).toNat) ((v (n+257)).toNat) ((v (n+268)).toNat) ((v (n+273)).toNat) ((v (n+301)).toNat) ((v (n+307)).toNat) ((v (n+298)).toNat) ((v (n+304)).toNat) ((v (n+310)).toNat)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_301)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_307)
  have chunk2 := KaratsubaWord.pair_add_balance ((v (n+278)).toNat) ((v (n+283)).toNat) (0) (0) ((v (n+312)).toNat) ((v (n+317)).toNat) ((v (n+310)).toNat) ((v (n+315)).toNat) (overflow_317)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_312)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_317)
  have balanced := Karatsuba.Carry128.positive_balance
    (pairValueAt v n 4 55) (pairValueAt v n 258 263) (pairValueAt v n 268 273) (pairValueAt v n 278 283)
    (pairValueAt v n 195 246) (pairValueAt v n 252 257)
    (pairValueAt v n 289 295) (pairValueAt v n 301 307) (pairValueAt v n 312 317)
    (v (n+298)).toNat (v (n+310)).toNat overflow_317
    (by simpa only [pairValueAt,HalfWord.pairValue,limbRadix,Nat.add_zero] using chunk0)
    (by simpa only [pairValueAt,HalfWord.pairValue,limbRadix] using chunk1)
    (by simpa only [pairValueAt,HalfWord.pairValue,limbRadix,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using chunk2)
  clear balance_289 balance_295 balance_301 balance_307 balance_312 balance_317 chunk0 chunk1 chunk2 mask start xor_288 xor_294 xor_300 xor_306
  refine ⟨overflow_317,?_⟩
  clear rows
  simp only [productLow,productHigh,diagonalValue,middleValue,pairValueAt,HalfWord.pairValue,LimbWords.value,pack4,radix,limbRadix] at balanced ⊢
  omega
#print axioms signed_positive_current

private theorem signed_negative_current (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n)
    (mask : v (n+178) = 18446744073709551615#64) :
    ∃ carry : Nat, (productLow v n).value+radix*(productHigh v n).value+2^512*carry+2^128*middleValue v n = diagonalValue v n+2^512 := by
  have balance_289 := Product.add_balance (v (n+288)) (v (n+258)) (v (n+286)) (by rw [rows.row_286]; exact Addition.carry3_le_one ..)
  rw [← rows.row_289,← rows.row_292] at balance_289
  have balance_295 := Product.add_balance (v (n+294)) (v (n+263)) (v (n+292)) (by rw [rows.row_292]; exact Addition.carry3_le_one ..)
  rw [← rows.row_295,← rows.row_298] at balance_295
  have balance_301 := Product.add_balance (v (n+300)) (v (n+268)) (v (n+298)) (by rw [rows.row_298]; exact Addition.carry3_le_one ..)
  rw [← rows.row_301,← rows.row_304] at balance_301
  have balance_307 := Product.add_balance (v (n+306)) (v (n+273)) (v (n+304)) (by rw [rows.row_304]; exact Addition.carry3_le_one ..)
  rw [← rows.row_307,← rows.row_310] at balance_307
  have balance_312 := Product.add_balance (v (n+278)) (v (n+178)) (v (n+310)) (by rw [rows.row_310]; exact Addition.carry3_le_one ..)
  rw [← rows.row_312,← rows.row_315] at balance_312
  have balance_317 := Product.add_balance (v (n+283)) (v (n+178)) (v (n+315)) (by rw [rows.row_315]; exact Addition.carry3_le_one ..)
  rw [← rows.row_317] at balance_317
  generalize overflow_eq_317 : (Op.carry3.eval [v (n+283),v (n+178),v (n+315)]).toNat = overflow_317 at balance_317
  clear overflow_eq_317
  have start : v (n+286) = 1#64 := by
    rw [rows.row_286,mask]
    exact KaratsubaWord.ones_carry
  have xor_288 : v (n+288) = ~~~(v (n+195)) := by
    rw [rows.row_288,mask]
    exact KaratsubaWord.xor_ones _
  have xor_294 : v (n+294) = ~~~(v (n+246)) := by
    rw [rows.row_294,mask]
    exact KaratsubaWord.xor_ones _
  have xor_300 : v (n+300) = ~~~(v (n+252)) := by
    rw [rows.row_300,mask]
    exact KaratsubaWord.xor_ones _
  have xor_306 : v (n+306) = ~~~(v (n+257)) := by
    rw [rows.row_306,mask]
    exact KaratsubaWord.xor_ones _
  simp only [mask,start,xor_288,xor_294,xor_300,xor_306,BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] at balance_289 balance_295 balance_301 balance_307 balance_312 balance_317
  have chunk0 := KaratsubaWord.pair_add_balance ((~~~(v (n+195))).toNat) ((~~~(v (n+246))).toNat) ((v (n+258)).toNat) ((v (n+263)).toNat) ((v (n+289)).toNat) ((v (n+295)).toNat) (1) ((v (n+292)).toNat) ((v (n+298)).toNat)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_289)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_295)
  have chunk1 := KaratsubaWord.pair_add_balance ((~~~(v (n+252))).toNat) ((~~~(v (n+257))).toNat) ((v (n+268)).toNat) ((v (n+273)).toNat) ((v (n+301)).toNat) ((v (n+307)).toNat) ((v (n+298)).toNat) ((v (n+304)).toNat) ((v (n+310)).toNat)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_301)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_307)
  have chunk2 := KaratsubaWord.pair_add_balance ((v (n+278)).toNat) ((v (n+283)).toNat) (18446744073709551615) (18446744073709551615) ((v (n+312)).toNat) ((v (n+317)).toNat) ((v (n+310)).toNat) ((v (n+315)).toNat) (overflow_317)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_312)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] using balance_317)
  have complement0 := KaratsubaWord.pair_complement (v (n+195),v (n+246))
  have complement1 := KaratsubaWord.pair_complement (v (n+252),v (n+257))
  have first := KaratsubaWord.negative_chunk_first _ _ _ _ _ chunk0 complement0
  have second := KaratsubaWord.negative_chunk_next _ _ _ _ _ _ chunk1 complement1
  have balanced := Karatsuba.Carry128.negative_balance
    (pairValueAt v n 4 55) (pairValueAt v n 258 263) (pairValueAt v n 268 273) (pairValueAt v n 278 283)
    (pairValueAt v n 195 246) (pairValueAt v n 252 257)
    (pairValueAt v n 289 295) (pairValueAt v n 301 307) (pairValueAt v n 312 317)
    (v (n+298)).toNat (v (n+310)).toNat overflow_317
    (by simpa only [pairValueAt,HalfWord.pairValue,limbRadix,Nat.add_zero] using first)
    (by simpa only [pairValueAt,HalfWord.pairValue,limbRadix] using second)
    (by simpa only [pairValueAt,HalfWord.pairValue,limbRadix,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using chunk2)
  clear balance_289 balance_295 balance_301 balance_307 balance_312 balance_317 chunk0 chunk1 chunk2 mask start xor_288 xor_294 xor_300 xor_306
  clear complement0 complement1 first second
  refine ⟨overflow_317,?_⟩
  clear rows
  simp only [productLow,productHigh,diagonalValue,middleValue,pairValueAt,HalfWord.pairValue,LimbWords.value,pack4,radix,limbRadix] at balanced ⊢
  omega
#print axioms signed_negative_current
theorem product_balance (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n)
    (loads : LoadsAgree v n) :
    (productLow v n).value+radix*(productHigh v n).value = (loadedX v n).value*(loadedY v n).value := by
  let xlo := HalfWord.pairValue (v n,v (n+1))
  let xhi := HalfWord.pairValue (v (n+67),v (n+68))
  let ylo := HalfWord.pairValue (v (n+2),v (n+3))
  let yhi := HalfWord.pairValue (v (n+69),v (n+70))
  have leftEq : leftValue v n = xlo*ylo := product_low v n rows
  have rightEq : rightValue v n = xhi*yhi := product_high v n rows
  have xParts : (loadedX v n).value = xlo+2^128*xhi := by
    simp only [loadedX,LimbWords.value,pack4,xlo,xhi,HalfWord.pairValue,limbRadix]
    omega
  have yParts : (loadedY v n).value = ylo+2^128*yhi := by
    simp only [loadedY,LimbWords.value,pack4,ylo,yhi,HalfWord.pairValue,limbRadix]
    omega
  have highProductBound := Nat.mul_le_mul
    (Nat.le_sub_one_of_lt (HalfWord.pair_bound (v (n+67),v (n+68))))
    (Nat.le_sub_one_of_lt (HalfWord.pair_bound (v (n+69),v (n+70))))
  have upperBound : rightValue v n+pairValueAt v n 61 66 < 2^256 := by
    apply KaratsubaWord.diagonal_upper_bound
    · rw [rightEq]
      exact highProductBound
    · exact HalfWord.pair_bound (v (n+61),v (n+66))
  obtain ⟨diagonalCarry,diagonalEq⟩ := diagonal_current v n rows upperBound
  have ma := KaratsubaWord.abs2_nat (v (n+134),v (n+135)) (v (n+136),v (n+137))
  rw [← cross_words_x v n rows] at ma
  simp only [loads.xHigh0,loads.xHigh1,loads.xLow0,loads.xLow1] at ma
  have mb := KaratsubaWord.abs2_nat (v (n+149),v (n+150)) (v (n+69),v (n+70))
  rw [← cross_words_y v n rows] at mb
  simp only [loads.yLow0,loads.yLow1] at mb
  have crossEq : middleValue v n =
      Karatsuba.Signs.magnitude xhi xlo*Karatsuba.Signs.magnitude ylo yhi := by
    have actual := product_cross v n rows
    change middleValue v n = HalfWord.pairValue (v (n+163),v (n+169))*
      HalfWord.pairValue (v (n+171),v (n+177)) at actual
    rw [ma,mb] at actual
    exact actual
  have algebra := Karatsuba.Signs.recombine xlo xhi ylo yhi (2^128)
  unfold Karatsuba.Signs.diagonal at algebra
  rw [← leftEq,← rightEq,← crossEq,← xParts,← yParts] at algebra
  have mask := outer_mask v n rows loads
  change v (n+178) = if ((xlo ≤ xhi) ↔ (yhi ≤ ylo)) then 0#64 else 18446744073709551615#64 at mask
  have productBound : (loadedX v n).value*(loadedY v n).value < 2^512 := by
    have actual := Nat.mul_lt_mul_of_lt_of_lt (loadedX v n).value_lt (loadedY v n).value_lt
    simpa only [radix] using actual
  have outputBound : (productLow v n).value+radix*(productHigh v n).value < 2^512 :=
    HalfWord.wide_bound _ _ (productLow v n).value_lt (productHigh v n).value_lt
  by_cases positive : ((xlo ≤ xhi) ↔ (yhi ≤ ylo))
  · simp only [positive,↓reduceIte] at algebra
    have signEq : v (n+178) = 0#64 := by simpa only [positive,↓reduceIte] using mask
    obtain ⟨lastCarry,lastEq⟩ := signed_positive_current v n rows signEq
    have diagonalPositive : diagonalValue v n+2^512*diagonalCarry+2^128*middleValue v n =
        (loadedX v n).value*(loadedY v n).value := by
      rw [diagonalEq]
      exact algebra
    exact Karatsuba.Carry128.bounded_positive_finish _ _ _ _ _ _ productBound diagonalPositive lastEq
  · simp only [positive,↓reduceIte] at algebra
    have signEq : v (n+178) = 18446744073709551615#64 := by simpa only [positive,↓reduceIte] using mask
    obtain ⟨lastCarry,lastEq⟩ := signed_negative_current v n rows signEq
    have diagonalNegative : diagonalValue v n+2^512*diagonalCarry =
        (loadedX v n).value*(loadedY v n).value+2^128*middleValue v n := diagonalEq.trans algebra.symm
    exact Karatsuba.Carry128.bounded_finish _ _ _ _ _ _ outputBound productBound diagonalNegative lastEq
#print axioms product_balance

theorem reduction_rows (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    MainReduction.Equations v (n+318) (productLow v n) (productHigh v n) := by
  constructor
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_318
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_319
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_320
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_321
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_322
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_323
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_324
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_325
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_326
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_327
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_328
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_329
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_330
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_331
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_333
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_334
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_336
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_337
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_338
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_339
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_340
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_342
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_343
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_344
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_345
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_346
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_347
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_348
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_349
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_350
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_351
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_352
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_353
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_354
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_355
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_356
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_358
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_359
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_361
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_362
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_363
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_364
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_365
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_367
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_368
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_369
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_370
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_373
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_375
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_378
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_380
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_383
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_385
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_388
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_390
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_391
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_394
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_396
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_399
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_401
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_404
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_406
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_407
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_408
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_409
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_410
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_411
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_412
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_413
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_415
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_416
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_418
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_419
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_420
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_421
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_422
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_424
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_425
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_426
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_429
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_431
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_434
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_436
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_439
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_441
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_444
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_446
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_447
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_450
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_452
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_455
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_457
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_460
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_462
theorem table_correct (inputs : List (BitVec 64)) (defs : List Def) (n xs ys : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n) (loads : LoadPositions defs xs ys)
    (insideX : xs+32 ≤ n) (insideY : ys+32 ≤ n) :
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value < modulus ∧
      (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value =
        ((SubSSA.inputLimbs inputs xs).value*(SubSSA.inputLimbs inputs ys).value)%modulus := by
  let v := fun i => (evalDefs inputs defs).getD i 0
  have equations := equations_of_positions inputs defs n lengthEq pos
  have duplicateLoads := duplicate_inputs inputs defs n xs ys lengthEq loads insideX insideY
  have originalLoads := loaded_inputs inputs defs n xs ys lengthEq loads insideX insideY
  have result := MainReduction.correct v (n+318) (productLow v n) (productHigh v n)
    (reduction_rows v n equations)
  have projected : (resultWords v n).value < modulus ∧
      (resultWords v n).value = ((productLow v n).value+radix*(productHigh v n).value)%modulus := by
    simpa only [MainReduction.resultWords,resultWords,Nat.add_assoc,Nat.reduceAdd] using result
  rw [product_balance v n equations duplicateLoads,originalLoads.1,originalLoads.2] at projected
  exact projected
#print axioms reduction_rows
#print axioms table_correct

end SecpMath.MainMulSSA
