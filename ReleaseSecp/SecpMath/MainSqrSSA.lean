import SecpMath.MainSqrRows
import SecpMath.MainReduction
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
namespace SecpMath.MainSqrSSA
open ArmCertValue SecpMath.Addition SecpMath.Product
private theorem square_low (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    pack4 (v (n+22)).toNat (v (n+83)).toNat (v (n+88)).toNat (v (n+93)).toNat =
      ((v n).toNat+limbRadix*(v (n+1)).toNat)*((v n).toNat+limbRadix*(v (n+1)).toNat) := by
  have square_0 := HalfWord.square64_correct (v n)
  have lo_0 : (v (n+22)) = HalfWord.squareLow (v n) := by
    simp only [rows.row_36, rows.row_35, rows.row_31, rows.row_30, rows.row_29, rows.row_22, rows.row_21, rows.row_20, rows.row_19, rows.row_18, rows.row_17, rows.row_16, rows.row_15, rows.row_14, rows.row_13, rows.row_12, rows.row_11, rows.row_10, rows.row_9, rows.row_8, rows.row_7, rows.row_6, rows.row_5, rows.row_4, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  have hi_0 : (v (n+36)) = HalfWord.squareHigh (v n) := by
    simp only [rows.row_36, rows.row_35, rows.row_31, rows.row_30, rows.row_29, rows.row_22, rows.row_21, rows.row_20, rows.row_19, rows.row_18, rows.row_17, rows.row_16, rows.row_15, rows.row_14, rows.row_13, rows.row_12, rows.row_11, rows.row_10, rows.row_9, rows.row_8, rows.row_7, rows.row_6, rows.row_5, rows.row_4, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  rw [← lo_0, ← hi_0] at square_0
  have square_1 := HalfWord.square64_correct (v (n+1))
  have lo_1 : (v (n+57)) = HalfWord.squareLow (v (n+1)) := by
    simp only [rows.row_71, rows.row_70, rows.row_66, rows.row_65, rows.row_64, rows.row_57, rows.row_56, rows.row_55, rows.row_52, rows.row_51, rows.row_50, rows.row_49, rows.row_48, rows.row_47, rows.row_46, rows.row_45, rows.row_44, rows.row_43, rows.row_42, rows.row_41, rows.row_40, rows.row_39, rows.row_38, rows.row_37, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  have hi_1 : (v (n+71)) = HalfWord.squareHigh (v (n+1)) := by
    simp only [rows.row_71, rows.row_70, rows.row_66, rows.row_65, rows.row_64, rows.row_57, rows.row_56, rows.row_55, rows.row_52, rows.row_51, rows.row_50, rows.row_49, rows.row_48, rows.row_47, rows.row_46, rows.row_45, rows.row_44, rows.row_43, rows.row_42, rows.row_41, rows.row_40, rows.row_39, rows.row_38, rows.row_37, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  rw [← lo_1, ← hi_1] at square_1
  have product := Product.mul_balance (v n) (v (n+1))
  rw [← rows.row_53, ← rows.row_54] at product
  have balance_72 := Product.add_balance (v (n+53)) (v (n+53)) (0#64) (by decide)
  rw [← rows.row_72, ← rows.row_75] at balance_72
  have balance_77 := Product.add_balance (v (n+54)) (v (n+54)) (v (n+75)) (by rw [rows.row_75]; exact Addition.carry3_le_one ..)
  rw [← rows.row_77, ← rows.row_80] at balance_77
  have balance_82 := Product.add_balance (v (n+71)) (0#64) (v (n+80)) (by rw [rows.row_80]; exact Addition.carry3_le_one ..)
  rw [← rows.row_82] at balance_82
  generalize overflow_eq_82 : (Op.carry3.eval [v (n+71),0#64,v (n+80)]).toNat = overflow_82 at balance_82
  clear overflow_eq_82
  have balance_83 := Product.add_balance (v (n+36)) (v (n+72)) (0#64) (by decide)
  rw [← rows.row_83, ← rows.row_86] at balance_83
  have balance_88 := Product.add_balance (v (n+57)) (v (n+77)) (v (n+86)) (by rw [rows.row_86]; exact Addition.carry3_le_one ..)
  rw [← rows.row_88, ← rows.row_91] at balance_88
  have balance_93 := Product.add_balance (v (n+82)) (0#64) (v (n+91)) (by rw [rows.row_91]; exact Addition.carry3_le_one ..)
  rw [← rows.row_93] at balance_93
  generalize overflow_eq_93 : (Op.carry3.eval [v (n+82),0#64,v (n+91)]).toNat = overflow_93 at balance_93
  clear overflow_eq_93
  have inputBound : (v n).toNat+limbRadix*(v (n+1)).toNat ≤ limbRadix^2-1 := by
    have first := (v n).isLt
    have second := (v (n+1)).isLt
    simp only [limbRadix] at *
    omega
  have productBound := Nat.mul_le_mul inputBound inputBound
  clear rows lo_0 hi_0 lo_1 hi_1
  simp only [pack4, limbRadix, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at *
  grind only
#print axioms square_low

private theorem square_high (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    pack4 (v (n+112)).toNat (v (n+173)).toNat (v (n+178)).toNat (v (n+183)).toNat =
      ((v (n+2)).toNat+limbRadix*(v (n+3)).toNat)*((v (n+2)).toNat+limbRadix*(v (n+3)).toNat) := by
  have square_2 := HalfWord.square64_correct (v (n+2))
  have lo_2 : (v (n+112)) = HalfWord.squareLow (v (n+2)) := by
    simp only [rows.row_126, rows.row_125, rows.row_121, rows.row_120, rows.row_119, rows.row_112, rows.row_111, rows.row_110, rows.row_109, rows.row_108, rows.row_107, rows.row_106, rows.row_105, rows.row_104, rows.row_103, rows.row_102, rows.row_101, rows.row_100, rows.row_99, rows.row_98, rows.row_97, rows.row_96, rows.row_95, rows.row_94, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  have hi_2 : (v (n+126)) = HalfWord.squareHigh (v (n+2)) := by
    simp only [rows.row_126, rows.row_125, rows.row_121, rows.row_120, rows.row_119, rows.row_112, rows.row_111, rows.row_110, rows.row_109, rows.row_108, rows.row_107, rows.row_106, rows.row_105, rows.row_104, rows.row_103, rows.row_102, rows.row_101, rows.row_100, rows.row_99, rows.row_98, rows.row_97, rows.row_96, rows.row_95, rows.row_94, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  rw [← lo_2, ← hi_2] at square_2
  have square_3 := HalfWord.square64_correct (v (n+3))
  have lo_3 : (v (n+147)) = HalfWord.squareLow (v (n+3)) := by
    simp only [rows.row_161, rows.row_160, rows.row_156, rows.row_155, rows.row_154, rows.row_147, rows.row_146, rows.row_145, rows.row_142, rows.row_141, rows.row_140, rows.row_139, rows.row_138, rows.row_137, rows.row_136, rows.row_135, rows.row_134, rows.row_133, rows.row_132, rows.row_131, rows.row_130, rows.row_129, rows.row_128, rows.row_127, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  have hi_3 : (v (n+161)) = HalfWord.squareHigh (v (n+3)) := by
    simp only [rows.row_161, rows.row_160, rows.row_156, rows.row_155, rows.row_154, rows.row_147, rows.row_146, rows.row_145, rows.row_142, rows.row_141, rows.row_140, rows.row_139, rows.row_138, rows.row_137, rows.row_136, rows.row_135, rows.row_134, rows.row_133, rows.row_132, rows.row_131, rows.row_130, rows.row_129, rows.row_128, rows.row_127, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  rw [← lo_3, ← hi_3] at square_3
  have product := Product.mul_balance (v (n+2)) (v (n+3))
  rw [← rows.row_143, ← rows.row_144] at product
  have balance_162 := Product.add_balance (v (n+143)) (v (n+143)) (0#64) (by decide)
  rw [← rows.row_162, ← rows.row_165] at balance_162
  have balance_167 := Product.add_balance (v (n+144)) (v (n+144)) (v (n+165)) (by rw [rows.row_165]; exact Addition.carry3_le_one ..)
  rw [← rows.row_167, ← rows.row_170] at balance_167
  have balance_172 := Product.add_balance (v (n+161)) (0#64) (v (n+170)) (by rw [rows.row_170]; exact Addition.carry3_le_one ..)
  rw [← rows.row_172] at balance_172
  generalize overflow_eq_172 : (Op.carry3.eval [v (n+161),0#64,v (n+170)]).toNat = overflow_172 at balance_172
  clear overflow_eq_172
  have balance_173 := Product.add_balance (v (n+126)) (v (n+162)) (0#64) (by decide)
  rw [← rows.row_173, ← rows.row_176] at balance_173
  have balance_178 := Product.add_balance (v (n+147)) (v (n+167)) (v (n+176)) (by rw [rows.row_176]; exact Addition.carry3_le_one ..)
  rw [← rows.row_178, ← rows.row_181] at balance_178
  have balance_183 := Product.add_balance (v (n+172)) (0#64) (v (n+181)) (by rw [rows.row_181]; exact Addition.carry3_le_one ..)
  rw [← rows.row_183] at balance_183
  generalize overflow_eq_183 : (Op.carry3.eval [v (n+172),0#64,v (n+181)]).toNat = overflow_183 at balance_183
  clear overflow_eq_183
  have inputBound : (v (n+2)).toNat+limbRadix*(v (n+3)).toNat ≤ limbRadix^2-1 := by
    have first := (v (n+2)).isLt
    have second := (v (n+3)).isLt
    simp only [limbRadix] at *
    omega
  have productBound := Nat.mul_le_mul inputBound inputBound
  clear rows lo_2 hi_2 lo_3 hi_3
  simp only [pack4, limbRadix, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at *
  grind only
#print axioms square_high

private theorem square_difference (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    pack4 (v (n+237)).toNat (v (n+298)).toNat (v (n+303)).toNat (v (n+308)).toNat =
      ((v (n+196)).toNat+limbRadix*(v (n+202)).toNat)*((v (n+196)).toNat+limbRadix*(v (n+202)).toNat) := by
  have square_196 := HalfWord.square64_correct (v (n+196))
  have lo_196 : (v (n+237)) = HalfWord.squareLow (v (n+196)) := by
    simp only [rows.row_251, rows.row_250, rows.row_246, rows.row_245, rows.row_244, rows.row_237, rows.row_236, rows.row_235, rows.row_234, rows.row_233, rows.row_232, rows.row_231, rows.row_230, rows.row_229, rows.row_228, rows.row_227, rows.row_226, rows.row_225, rows.row_224, rows.row_223, rows.row_222, rows.row_221, rows.row_220, rows.row_219, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  have hi_196 : (v (n+251)) = HalfWord.squareHigh (v (n+196)) := by
    simp only [rows.row_251, rows.row_250, rows.row_246, rows.row_245, rows.row_244, rows.row_237, rows.row_236, rows.row_235, rows.row_234, rows.row_233, rows.row_232, rows.row_231, rows.row_230, rows.row_229, rows.row_228, rows.row_227, rows.row_226, rows.row_225, rows.row_224, rows.row_223, rows.row_222, rows.row_221, rows.row_220, rows.row_219, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  rw [← lo_196, ← hi_196] at square_196
  have square_202 := HalfWord.square64_correct (v (n+202))
  have lo_202 : (v (n+272)) = HalfWord.squareLow (v (n+202)) := by
    simp only [rows.row_286, rows.row_285, rows.row_281, rows.row_280, rows.row_279, rows.row_272, rows.row_271, rows.row_270, rows.row_267, rows.row_266, rows.row_265, rows.row_264, rows.row_263, rows.row_262, rows.row_261, rows.row_260, rows.row_259, rows.row_258, rows.row_257, rows.row_256, rows.row_255, rows.row_254, rows.row_253, rows.row_252, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  have hi_202 : (v (n+286)) = HalfWord.squareHigh (v (n+202)) := by
    simp only [rows.row_286, rows.row_285, rows.row_281, rows.row_280, rows.row_279, rows.row_272, rows.row_271, rows.row_270, rows.row_267, rows.row_266, rows.row_265, rows.row_264, rows.row_263, rows.row_262, rows.row_261, rows.row_260, rows.row_259, rows.row_258, rows.row_257, rows.row_256, rows.row_255, rows.row_254, rows.row_253, rows.row_252, HalfWord.squareLow, HalfWord.squareHigh, HalfWord.squareCross,
      HalfWord.squareCarry, HalfWord.mul32, HalfWord.low32, HalfWord.high32, HalfWord.add_zero]
  rw [← lo_202, ← hi_202] at square_202
  have product := Product.mul_balance (v (n+196)) (v (n+202))
  rw [← rows.row_268, ← rows.row_269] at product
  have balance_287 := Product.add_balance (v (n+268)) (v (n+268)) (0#64) (by decide)
  rw [← rows.row_287, ← rows.row_290] at balance_287
  have balance_292 := Product.add_balance (v (n+269)) (v (n+269)) (v (n+290)) (by rw [rows.row_290]; exact Addition.carry3_le_one ..)
  rw [← rows.row_292, ← rows.row_295] at balance_292
  have balance_297 := Product.add_balance (v (n+286)) (0#64) (v (n+295)) (by rw [rows.row_295]; exact Addition.carry3_le_one ..)
  rw [← rows.row_297] at balance_297
  generalize overflow_eq_297 : (Op.carry3.eval [v (n+286),0#64,v (n+295)]).toNat = overflow_297 at balance_297
  clear overflow_eq_297
  have balance_298 := Product.add_balance (v (n+251)) (v (n+287)) (0#64) (by decide)
  rw [← rows.row_298, ← rows.row_301] at balance_298
  have balance_303 := Product.add_balance (v (n+272)) (v (n+292)) (v (n+301)) (by rw [rows.row_301]; exact Addition.carry3_le_one ..)
  rw [← rows.row_303, ← rows.row_306] at balance_303
  have balance_308 := Product.add_balance (v (n+297)) (0#64) (v (n+306)) (by rw [rows.row_306]; exact Addition.carry3_le_one ..)
  rw [← rows.row_308] at balance_308
  generalize overflow_eq_308 : (Op.carry3.eval [v (n+297),0#64,v (n+306)]).toNat = overflow_308 at balance_308
  clear overflow_eq_308
  have inputBound : (v (n+196)).toNat+limbRadix*(v (n+202)).toNat ≤ limbRadix^2-1 := by
    have first := (v (n+196)).isLt
    have second := (v (n+202)).isLt
    simp only [limbRadix] at *
    omega
  have productBound := Nat.mul_le_mul inputBound inputBound
  clear rows lo_196 hi_196 lo_202 hi_202
  simp only [pack4, limbRadix, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at *
  grind only
#print axioms square_difference

def loadedX (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v n,v (n+1),v (n+2),v (n+3)⟩
def productLow (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+22),v (n+83),v (n+330),v (n+335)⟩
def productHigh (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+340),v (n+345),v (n+350),v (n+355)⟩

private theorem absolute_words (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) : (v (n+196),v (n+202)) = HalfWord.abs2 (v n,v (n+1)) (v (n+2),v (n+3)) := by
  simp only [rows.row_202, rows.row_201, rows.row_199, rows.row_196, rows.row_195, rows.row_194, rows.row_192, rows.row_189, rows.row_187, rows.row_184, HalfWord.abs2, HalfWord.sub2, HalfWord.negate2, HalfWord.mask_carry] <;> rfl

set_option maxHeartbeats 200000 in
theorem product_balance (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    (productLow v n).value+radix*(productHigh v n).value =
      (loadedX v n).value*(loadedX v n).value := by
  have low := square_low v n rows
  have high := square_high v n rows
  have difference := square_difference v n rows
  have absoluteWords := absolute_words v n rows
  have absolute := HalfWord.abs2_correct (v n,v (n+1)) (v (n+2),v (n+3))
  rw [← absoluteWords] at absolute
  have balance_203 := Product.add_balance (v (n+112)) (v (n+88)) (0#64) (by decide)
  rw [← rows.row_203, ← rows.row_206] at balance_203
  have balance_208 := Product.add_balance (v (n+173)) (v (n+93)) (v (n+206)) (by rw [rows.row_206]; exact Addition.carry3_le_one ..)
  rw [← rows.row_208, ← rows.row_211] at balance_208
  have balance_213 := Product.add_balance (v (n+178)) (0#64) (v (n+211)) (by rw [rows.row_211]; exact Addition.carry3_le_one ..)
  rw [← rows.row_213, ← rows.row_216] at balance_213
  have balance_218 := Product.add_balance (v (n+183)) (0#64) (v (n+216)) (by rw [rows.row_216]; exact Addition.carry3_le_one ..)
  rw [← rows.row_218] at balance_218
  generalize overflow_eq_218 : (Op.carry3.eval [v (n+183),0#64,v (n+216)]).toNat = overflow_218 at balance_218
  clear overflow_eq_218
  have balance_309 := Product.add_balance (v (n+22)) (v (n+203)) (0#64) (by decide)
  rw [← rows.row_309, ← rows.row_312] at balance_309
  have balance_314 := Product.add_balance (v (n+83)) (v (n+208)) (v (n+312)) (by rw [rows.row_312]; exact Addition.carry3_le_one ..)
  rw [← rows.row_314, ← rows.row_317] at balance_314
  have balance_319 := Product.add_balance (v (n+203)) (v (n+213)) (v (n+317)) (by rw [rows.row_317]; exact Addition.carry3_le_one ..)
  rw [← rows.row_319, ← rows.row_322] at balance_319
  have balance_324 := Product.add_balance (v (n+208)) (v (n+218)) (v (n+322)) (by rw [rows.row_322]; exact Addition.carry3_le_one ..)
  rw [← rows.row_324, ← rows.row_327] at balance_324
  have balance_350 := Product.add_balance (v (n+213)) (v (n+329)) (v (n+348)) (by rw [rows.row_348]; exact SecpMath.sbc3C_le_one ..)
  rw [← rows.row_350, ← rows.row_353] at balance_350
  have balance_355 := Product.add_balance (v (n+218)) (v (n+329)) (v (n+353)) (by rw [rows.row_353]; exact Addition.carry3_le_one ..)
  rw [← rows.row_355] at balance_355
  generalize overflow_eq_355 : (Op.carry3.eval [v (n+218),v (n+329),v (n+353)]).toNat = overflow_355 at balance_355
  clear overflow_eq_355
  have subtract_330 := HalfWord.sub_balance_additive (v (n+309)) (v (n+237)) (1#64) (by decide)
  rw [← rows.row_330, ← rows.row_333] at subtract_330
  have flag_333 : (v (n+333)).toNat ≤ 1 := by rw [rows.row_333]; exact SecpMath.sbc3C_le_one ..
  have subtract_335 := HalfWord.sub_balance_additive (v (n+314)) (v (n+298)) (v (n+333)) (by rw [rows.row_333]; exact SecpMath.sbc3C_le_one ..)
  rw [← rows.row_335, ← rows.row_338] at subtract_335
  have flag_338 : (v (n+338)).toNat ≤ 1 := by rw [rows.row_338]; exact SecpMath.sbc3C_le_one ..
  have subtract_340 := HalfWord.sub_balance_additive (v (n+319)) (v (n+303)) (v (n+338)) (by rw [rows.row_338]; exact SecpMath.sbc3C_le_one ..)
  rw [← rows.row_340, ← rows.row_343] at subtract_340
  have flag_343 : (v (n+343)).toNat ≤ 1 := by rw [rows.row_343]; exact SecpMath.sbc3C_le_one ..
  have subtract_345 := HalfWord.sub_balance_additive (v (n+324)) (v (n+308)) (v (n+343)) (by rw [rows.row_343]; exact SecpMath.sbc3C_le_one ..)
  rw [← rows.row_345, ← rows.row_348] at subtract_345
  have flag_348 : (v (n+348)).toNat ≤ 1 := by rw [rows.row_348]; exact SecpMath.sbc3C_le_one ..
  have mask := HalfWord.mask_balance (v (n+325)) (v (n+326)) (v (n+327)) (v (n+328)) (by rw [rows.row_327]; exact Addition.carry3_le_one ..)
  rw [← rows.row_329] at mask
  have inputBound := (loadedX v n).value_lt
  have productBound := Nat.mul_le_mul (Nat.le_sub_one_of_lt inputBound) (Nat.le_sub_one_of_lt inputBound)
  have outputLow := (productLow v n).value_lt
  have outputHigh := (productHigh v n).value_lt
  have highInputBound : (v (n+2)).toNat+limbRadix*(v (n+3)).toNat ≤ limbRadix^2-1 := by
    have first := (v (n+2)).isLt
    have second := (v (n+3)).isLt
    simp only [limbRadix] at *
    omega
  have highProductBound := Nat.mul_le_mul highInputBound highInputBound
  have lowUpperBound := HalfWord.pair_bound (v (n+88),v (n+93))
  clear rows absoluteWords
  have sumBalance := Addition.packed_balance
    (v (n+112)).toNat (v (n+173)).toNat (v (n+178)).toNat (v (n+183)).toNat
    (v (n+88)).toNat (v (n+93)).toNat 0 0
    (v (n+203)).toNat (v (n+208)).toNat (v (n+213)).toNat (v (n+218)).toNat
    (v (n+206)).toNat (v (n+211)).toNat (v (n+216)).toNat overflow_218
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero] using balance_203)
    balance_208
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod] using balance_213)
    (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod] using balance_218)
  have highNatural := high
  rw [highNatural] at sumBalance
  simp only [pack4,Nat.mul_zero,Nat.add_zero] at sumBalance
  have overflowZero := HalfWord.upper_square_carry _ _ _ _ highProductBound lowUpperBound sumBalance
  simp only [productLow,productHigh,loadedX,LimbWords.value,pack4,HalfWord.pairValue,
    radix,limbRadix,BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.zero_add] at *
  have combined :
      (productLow v n).value+radix*(productHigh v n).value +
        radix^2*overflow_355+(limbRadix^6+radix^2)*overflow_218+
        radix^2*(v (n+327)).toNat =
      (loadedX v n).value*(loadedX v n).value+radix^2 := by
    simp only [productLow,productHigh,loadedX,LimbWords.value,pack4,radix,limbRadix]
    rcases absolute with forward | backward <;> grind -lia only
  have finalBound := HalfWord.wide_bound (productLow v n).value (productHigh v n).value
    (productLow v n).value_lt (productHigh v n).value_lt
  have targetBound : (loadedX v n).value*(loadedX v n).value < radix^2 := by
    simpa only [Nat.pow_two] using Nat.mul_lt_mul_of_lt_of_lt (loadedX v n).value_lt (loadedX v n).value_lt
  apply HalfWord.bounded512 _ _ (overflow_355+(v (n+327)).toNat) 1 finalBound targetBound
  simpa only [overflowZero,Nat.mul_zero,Nat.add_zero,Nat.mul_add,Nat.mul_one,Nat.add_assoc] using combined
#print axioms product_balance

def resultWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+485),v (n+490),v (n+495),v (n+500)⟩

theorem loaded_inputs (inputs : List (BitVec 64)) (defs : List Def) (n xs : Nat)
    (lengthEq : inputs.length = n) (pos : LoadPositions defs xs) (inside : xs+32 ≤ n) :
    loadedX (fun i => (evalDefs inputs defs).getD i 0) n = SubSSA.inputLimbs inputs xs := by
  subst n
  have first := SubSSA.loaded_input_word inputs defs 0 xs pos.x0 (by omega)
  simp only [Nat.add_zero] at first
  simp only [loadedX,SubSSA.inputLimbs,first,
    SubSSA.loaded_input_word inputs defs 1 (xs+8) pos.x1 (by omega),
    SubSSA.loaded_input_word inputs defs 2 (xs+16) pos.x2 (by omega),
    SubSSA.loaded_input_word inputs defs 3 (xs+24) pos.x3 (by omega)]

theorem reduction_rows (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    MainReduction.Equations v (n+356) (productLow v n) (productHigh v n) := by
  constructor
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_356
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_357
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_358
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_359
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_360
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_361
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_362
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_363
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_364
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_365
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_366
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_367
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_368
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_369
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_371
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_372
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_374
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_375
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_376
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_377
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_378
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_380
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_381
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_382
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_383
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_384
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_385
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_386
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_387
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_388
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_389
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_390
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_391
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_392
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_393
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_394
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_396
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_397
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_399
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_400
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_401
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_402
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_403
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_405
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_406
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_407
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_408
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_411
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_413
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_416
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_418
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_421
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_423
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_426
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_428
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_429
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_432
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_434
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_437
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_439
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_442
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_444
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_445
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_446
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_447
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_448
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_449
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_450
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_451
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_453
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_454
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_456
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_457
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_458
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_459
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_460
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_462
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_463
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_464
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_467
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_469
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_472
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_474
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_477
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_479
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_482
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_484
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_485
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_488
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_490
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_493
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_495
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_498
  · simpa only [Nat.add_assoc,Nat.reduceAdd,productLow,productHigh] using rows.row_500

theorem table_correct (inputs : List (BitVec 64)) (defs : List Def) (n xs : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n) (loads : LoadPositions defs xs)
    (inside : xs+32 ≤ n) :
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value < modulus ∧
      (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value =
        ((SubSSA.inputLimbs inputs xs).value*(SubSSA.inputLimbs inputs xs).value)%modulus := by
  let v := fun i => (evalDefs inputs defs).getD i 0
  have equations := equations_of_positions inputs defs n lengthEq pos
  have result := MainReduction.correct v (n+356) (productLow v n) (productHigh v n)
    (reduction_rows v n equations)
  have projected : (resultWords v n).value < modulus ∧
      (resultWords v n).value = ((productLow v n).value+radix*(productHigh v n).value)%modulus := by
    simpa only [MainReduction.resultWords,resultWords,Nat.add_assoc,Nat.reduceAdd] using result
  rw [product_balance v n equations,loaded_inputs inputs defs n xs lengthEq loads inside] at projected
  exact projected
#print axioms reduction_rows
#print axioms table_correct
end SecpMath.MainSqrSSA
