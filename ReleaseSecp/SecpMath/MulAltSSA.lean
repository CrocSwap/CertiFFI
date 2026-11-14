import SecpMath.WordMulAdd
import SecpMath.WideWordReduce
import SecpMath.SubSSA
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
namespace SecpMath.MulAltSSA
open ArmCertValue SecpMath.Addition SecpMath.Product
open SecpMath.SubSSA (inputWordDef inputLimbs loaded_input_word)

def loadedX (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v n, v (n+1), v (n+30), v (n+31)⟩
def loadedY (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+2), v (n+3), v (n+13), v (n+14)⟩
def productLow (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+4), v (n+33), v (n+78), v (n+123)⟩
def productHigh (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+149), v (n+155), v (n+161), v (n+166)⟩
def resultWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+238), v (n+243), v (n+248), v (n+253)⟩

structure LoadPositions (defs : List Def) (xs ys : Nat) : Prop where
  x0 : defs[0]? = some (inputWordDef xs)
  x1 : defs[1]? = some (inputWordDef (xs+8))
  x2 : defs[30]? = some (inputWordDef (xs+16))
  x3 : defs[31]? = some (inputWordDef (xs+24))
  y0 : defs[2]? = some (inputWordDef ys)
  y1 : defs[3]? = some (inputWordDef (ys+8))
  y2 : defs[13]? = some (inputWordDef (ys+16))
  y3 : defs[14]? = some (inputWordDef (ys+24))

theorem loaded_inputs (inputs : List (BitVec 64)) (defs : List Def) (n xs ys : Nat)
    (lengthEq : inputs.length = n) (pos : LoadPositions defs xs ys)
    (xInside : xs+32 ≤ n) (yInside : ys+32 ≤ n) :
    loadedX (fun i => (evalDefs inputs defs).getD i 0) n = inputLimbs inputs xs ∧
    loadedY (fun i => (evalDefs inputs defs).getD i 0) n = inputLimbs inputs ys := by
  subst n
  have first := loaded_input_word inputs defs 0 xs pos.x0 (by omega)
  simp only [Nat.add_zero] at first
  constructor
  · simp only [loadedX, inputLimbs, first,
      loaded_input_word inputs defs 1 (xs+8) pos.x1 (by omega),
      loaded_input_word inputs defs 30 (xs+16) pos.x2 (by omega),
      loaded_input_word inputs defs 31 (xs+24) pos.x3 (by omega)]
  · simp only [loadedY, inputLimbs,
      loaded_input_word inputs defs 2 ys pos.y0 (by omega),
      loaded_input_word inputs defs 3 (ys+8) pos.y1 (by omega),
      loaded_input_word inputs defs 13 (ys+16) pos.y2 (by omega),
      loaded_input_word inputs defs 14 (ys+24) pos.y3 (by omega)]

private theorem const_eval (values : List (BitVec 64)) (c : BitVec 64) :
    Def.eval values ⟨.const c, []⟩ = c := rfl

structure Equations (v : Nat → BitVec 64) (n : Nat) : Prop where
  row_4 : v (n+4) = (Op.mul).eval [v n, v (n+2)]
  row_5 : v (n+5) = (Op.umulh).eval [v n, v (n+2)]
  row_6 : v (n+6) = (Op.mul).eval [v n, v (n+3)]
  row_7 : v (n+7) = (Op.umulh).eval [v n, v (n+3)]
  row_8 : v (n+8) = (Op.add3).eval [v (n+5), v (n+6), 0#64]
  row_11 : v (n+11) = (Op.carry3).eval [v (n+5), v (n+6), 0#64]
  row_15 : v (n+15) = (Op.mul).eval [v n, v (n+13)]
  row_16 : v (n+16) = (Op.umulh).eval [v n, v (n+13)]
  row_17 : v (n+17) = (Op.add3).eval [v (n+7), v (n+15), v (n+11)]
  row_20 : v (n+20) = (Op.carry3).eval [v (n+7), v (n+15), v (n+11)]
  row_22 : v (n+22) = (Op.mul).eval [v n, v (n+14)]
  row_23 : v (n+23) = (Op.umulh).eval [v n, v (n+14)]
  row_24 : v (n+24) = (Op.add3).eval [v (n+16), v (n+22), v (n+20)]
  row_27 : v (n+27) = (Op.carry3).eval [v (n+16), v (n+22), v (n+20)]
  row_29 : v (n+29) = (Op.add3).eval [v (n+23), 0#64, v (n+27)]
  row_32 : v (n+32) = (Op.mul).eval [v (n+1), v (n+2)]
  row_33 : v (n+33) = (Op.add3).eval [v (n+8), v (n+32), 0#64]
  row_36 : v (n+36) = (Op.carry3).eval [v (n+8), v (n+32), 0#64]
  row_38 : v (n+38) = (Op.mul).eval [v (n+1), v (n+3)]
  row_39 : v (n+39) = (Op.add3).eval [v (n+17), v (n+38), v (n+36)]
  row_42 : v (n+42) = (Op.carry3).eval [v (n+17), v (n+38), v (n+36)]
  row_44 : v (n+44) = (Op.mul).eval [v (n+1), v (n+13)]
  row_45 : v (n+45) = (Op.add3).eval [v (n+24), v (n+44), v (n+42)]
  row_48 : v (n+48) = (Op.carry3).eval [v (n+24), v (n+44), v (n+42)]
  row_50 : v (n+50) = (Op.mul).eval [v (n+1), v (n+14)]
  row_51 : v (n+51) = (Op.add3).eval [v (n+29), v (n+50), v (n+48)]
  row_54 : v (n+54) = (Op.carry3).eval [v (n+29), v (n+50), v (n+48)]
  row_56 : v (n+56) = (Op.umulh).eval [v (n+1), v (n+14)]
  row_57 : v (n+57) = (Op.add3).eval [v (n+56), 0#64, v (n+54)]
  row_58 : v (n+58) = (Op.umulh).eval [v (n+1), v (n+2)]
  row_59 : v (n+59) = (Op.add3).eval [v (n+39), v (n+58), 0#64]
  row_62 : v (n+62) = (Op.carry3).eval [v (n+39), v (n+58), 0#64]
  row_64 : v (n+64) = (Op.umulh).eval [v (n+1), v (n+3)]
  row_65 : v (n+65) = (Op.add3).eval [v (n+45), v (n+64), v (n+62)]
  row_68 : v (n+68) = (Op.carry3).eval [v (n+45), v (n+64), v (n+62)]
  row_70 : v (n+70) = (Op.umulh).eval [v (n+1), v (n+13)]
  row_71 : v (n+71) = (Op.add3).eval [v (n+51), v (n+70), v (n+68)]
  row_74 : v (n+74) = (Op.carry3).eval [v (n+51), v (n+70), v (n+68)]
  row_76 : v (n+76) = (Op.add3).eval [v (n+57), 0#64, v (n+74)]
  row_77 : v (n+77) = (Op.mul).eval [v (n+30), v (n+2)]
  row_78 : v (n+78) = (Op.add3).eval [v (n+59), v (n+77), 0#64]
  row_81 : v (n+81) = (Op.carry3).eval [v (n+59), v (n+77), 0#64]
  row_83 : v (n+83) = (Op.mul).eval [v (n+30), v (n+3)]
  row_84 : v (n+84) = (Op.add3).eval [v (n+65), v (n+83), v (n+81)]
  row_87 : v (n+87) = (Op.carry3).eval [v (n+65), v (n+83), v (n+81)]
  row_89 : v (n+89) = (Op.mul).eval [v (n+30), v (n+13)]
  row_90 : v (n+90) = (Op.add3).eval [v (n+71), v (n+89), v (n+87)]
  row_93 : v (n+93) = (Op.carry3).eval [v (n+71), v (n+89), v (n+87)]
  row_95 : v (n+95) = (Op.mul).eval [v (n+30), v (n+14)]
  row_96 : v (n+96) = (Op.add3).eval [v (n+76), v (n+95), v (n+93)]
  row_99 : v (n+99) = (Op.carry3).eval [v (n+76), v (n+95), v (n+93)]
  row_101 : v (n+101) = (Op.umulh).eval [v (n+30), v (n+14)]
  row_102 : v (n+102) = (Op.add3).eval [v (n+101), 0#64, v (n+99)]
  row_103 : v (n+103) = (Op.umulh).eval [v (n+30), v (n+2)]
  row_104 : v (n+104) = (Op.add3).eval [v (n+84), v (n+103), 0#64]
  row_107 : v (n+107) = (Op.carry3).eval [v (n+84), v (n+103), 0#64]
  row_109 : v (n+109) = (Op.umulh).eval [v (n+30), v (n+3)]
  row_110 : v (n+110) = (Op.add3).eval [v (n+90), v (n+109), v (n+107)]
  row_113 : v (n+113) = (Op.carry3).eval [v (n+90), v (n+109), v (n+107)]
  row_115 : v (n+115) = (Op.umulh).eval [v (n+30), v (n+13)]
  row_116 : v (n+116) = (Op.add3).eval [v (n+96), v (n+115), v (n+113)]
  row_119 : v (n+119) = (Op.carry3).eval [v (n+96), v (n+115), v (n+113)]
  row_121 : v (n+121) = (Op.add3).eval [v (n+102), 0#64, v (n+119)]
  row_122 : v (n+122) = (Op.mul).eval [v (n+31), v (n+2)]
  row_123 : v (n+123) = (Op.add3).eval [v (n+104), v (n+122), 0#64]
  row_126 : v (n+126) = (Op.carry3).eval [v (n+104), v (n+122), 0#64]
  row_128 : v (n+128) = (Op.mul).eval [v (n+31), v (n+3)]
  row_129 : v (n+129) = (Op.add3).eval [v (n+110), v (n+128), v (n+126)]
  row_132 : v (n+132) = (Op.carry3).eval [v (n+110), v (n+128), v (n+126)]
  row_134 : v (n+134) = (Op.mul).eval [v (n+31), v (n+13)]
  row_135 : v (n+135) = (Op.add3).eval [v (n+116), v (n+134), v (n+132)]
  row_138 : v (n+138) = (Op.carry3).eval [v (n+116), v (n+134), v (n+132)]
  row_140 : v (n+140) = (Op.mul).eval [v (n+31), v (n+14)]
  row_141 : v (n+141) = (Op.add3).eval [v (n+121), v (n+140), v (n+138)]
  row_144 : v (n+144) = (Op.carry3).eval [v (n+121), v (n+140), v (n+138)]
  row_146 : v (n+146) = (Op.umulh).eval [v (n+31), v (n+14)]
  row_147 : v (n+147) = (Op.add3).eval [v (n+146), 0#64, v (n+144)]
  row_148 : v (n+148) = (Op.umulh).eval [v (n+31), v (n+2)]
  row_149 : v (n+149) = (Op.add3).eval [v (n+129), v (n+148), 0#64]
  row_152 : v (n+152) = (Op.carry3).eval [v (n+129), v (n+148), 0#64]
  row_154 : v (n+154) = (Op.umulh).eval [v (n+31), v (n+3)]
  row_155 : v (n+155) = (Op.add3).eval [v (n+135), v (n+154), v (n+152)]
  row_158 : v (n+158) = (Op.carry3).eval [v (n+135), v (n+154), v (n+152)]
  row_160 : v (n+160) = (Op.umulh).eval [v (n+31), v (n+13)]
  row_161 : v (n+161) = (Op.add3).eval [v (n+141), v (n+160), v (n+158)]
  row_164 : v (n+164) = (Op.carry3).eval [v (n+141), v (n+160), v (n+158)]
  row_166 : v (n+166) = (Op.add3).eval [v (n+147), 0#64, v (n+164)]
  row_167 : v (n+167) = 977#64
  row_168 : v (n+168) = (Op.orr).eval [v (n+167), 4294967296#64]
  row_169 : v (n+169) = (Op.mul).eval [v (n+168), v (n+149)]
  row_170 : v (n+170) = (Op.umulh).eval [v (n+168), v (n+149)]
  row_171 : v (n+171) = (Op.add3).eval [v (n+4), v (n+169), 0#64]
  row_174 : v (n+174) = (Op.carry3).eval [v (n+4), v (n+169), 0#64]
  row_176 : v (n+176) = (Op.mul).eval [v (n+168), v (n+155)]
  row_177 : v (n+177) = (Op.umulh).eval [v (n+168), v (n+155)]
  row_178 : v (n+178) = (Op.add3).eval [v (n+33), v (n+176), v (n+174)]
  row_181 : v (n+181) = (Op.carry3).eval [v (n+33), v (n+176), v (n+174)]
  row_183 : v (n+183) = (Op.mul).eval [v (n+168), v (n+161)]
  row_184 : v (n+184) = (Op.umulh).eval [v (n+168), v (n+161)]
  row_185 : v (n+185) = (Op.add3).eval [v (n+78), v (n+183), v (n+181)]
  row_188 : v (n+188) = (Op.carry3).eval [v (n+78), v (n+183), v (n+181)]
  row_190 : v (n+190) = (Op.mul).eval [v (n+168), v (n+166)]
  row_191 : v (n+191) = (Op.umulh).eval [v (n+168), v (n+166)]
  row_192 : v (n+192) = (Op.add3).eval [v (n+123), v (n+190), v (n+188)]
  row_195 : v (n+195) = (Op.carry3).eval [v (n+123), v (n+190), v (n+188)]
  row_197 : v (n+197) = (Op.cond 2#4).eval [v (n+193), v (n+194), v (n+195), v (n+196)]
  row_198 : v (n+198) = (Op.add3).eval [v (n+178), v (n+170), 0#64]
  row_201 : v (n+201) = (Op.carry3).eval [v (n+178), v (n+170), 0#64]
  row_203 : v (n+203) = (Op.add3).eval [v (n+185), v (n+177), v (n+201)]
  row_206 : v (n+206) = (Op.carry3).eval [v (n+185), v (n+177), v (n+201)]
  row_208 : v (n+208) = (Op.add3).eval [v (n+192), v (n+184), v (n+206)]
  row_211 : v (n+211) = (Op.carry3).eval [v (n+192), v (n+184), v (n+206)]
  row_213 : v (n+213) = (Op.add3).eval [v (n+197), v (n+191), v (n+211)]
  row_214 : v (n+214) = (Op.add).eval [v (n+213), 1#64]
  row_215 : v (n+215) = (Op.mul).eval [v (n+168), v (n+214)]
  row_216 : v (n+216) = (Op.umulh).eval [v (n+168), v (n+214)]
  row_217 : v (n+217) = (Op.add3).eval [v (n+171), v (n+215), 0#64]
  row_220 : v (n+220) = (Op.carry3).eval [v (n+171), v (n+215), 0#64]
  row_222 : v (n+222) = (Op.add3).eval [v (n+198), v (n+216), v (n+220)]
  row_225 : v (n+225) = (Op.carry3).eval [v (n+198), v (n+216), v (n+220)]
  row_227 : v (n+227) = (Op.add3).eval [v (n+203), 0#64, v (n+225)]
  row_230 : v (n+230) = (Op.carry3).eval [v (n+203), 0#64, v (n+225)]
  row_232 : v (n+232) = (Op.add3).eval [v (n+208), 0#64, v (n+230)]
  row_235 : v (n+235) = (Op.carry3).eval [v (n+208), 0#64, v (n+230)]
  row_237 : v (n+237) = (Op.cselc 3#4).eval [v (n+233), v (n+234), v (n+235), v (n+236), v (n+168), 0#64]
  row_238 : v (n+238) = (Op.sbc3).eval [v (n+217), v (n+237), 1#64]
  row_241 : v (n+241) = (Op.sbc3C).eval [v (n+217), v (n+237), 1#64]
  row_243 : v (n+243) = (Op.sbc3).eval [v (n+222), 0#64, v (n+241)]
  row_246 : v (n+246) = (Op.sbc3C).eval [v (n+222), 0#64, v (n+241)]
  row_248 : v (n+248) = (Op.sbc3).eval [v (n+227), 0#64, v (n+246)]
  row_251 : v (n+251) = (Op.sbc3C).eval [v (n+227), 0#64, v (n+246)]
  row_253 : v (n+253) = (Op.sbc3).eval [v (n+232), 0#64, v (n+251)]

structure RowPositions (defs : List Def) (n : Nat) : Prop where
  row_4 : defs[4]? = some (⟨.mul, [.id n, .id (n+2)]⟩ : Def)
  row_5 : defs[5]? = some (⟨.umulh, [.id n, .id (n+2)]⟩ : Def)
  row_6 : defs[6]? = some (⟨.mul, [.id n, .id (n+3)]⟩ : Def)
  row_7 : defs[7]? = some (⟨.umulh, [.id n, .id (n+3)]⟩ : Def)
  row_8 : defs[8]? = some (⟨.add3, [.id (n+5), .id (n+6), .imm 0#64]⟩ : Def)
  row_11 : defs[11]? = some (⟨.carry3, [.id (n+5), .id (n+6), .imm 0#64]⟩ : Def)
  row_15 : defs[15]? = some (⟨.mul, [.id n, .id (n+13)]⟩ : Def)
  row_16 : defs[16]? = some (⟨.umulh, [.id n, .id (n+13)]⟩ : Def)
  row_17 : defs[17]? = some (⟨.add3, [.id (n+7), .id (n+15), .id (n+11)]⟩ : Def)
  row_20 : defs[20]? = some (⟨.carry3, [.id (n+7), .id (n+15), .id (n+11)]⟩ : Def)
  row_22 : defs[22]? = some (⟨.mul, [.id n, .id (n+14)]⟩ : Def)
  row_23 : defs[23]? = some (⟨.umulh, [.id n, .id (n+14)]⟩ : Def)
  row_24 : defs[24]? = some (⟨.add3, [.id (n+16), .id (n+22), .id (n+20)]⟩ : Def)
  row_27 : defs[27]? = some (⟨.carry3, [.id (n+16), .id (n+22), .id (n+20)]⟩ : Def)
  row_29 : defs[29]? = some (⟨.add3, [.id (n+23), .imm 0#64, .id (n+27)]⟩ : Def)
  row_32 : defs[32]? = some (⟨.mul, [.id (n+1), .id (n+2)]⟩ : Def)
  row_33 : defs[33]? = some (⟨.add3, [.id (n+8), .id (n+32), .imm 0#64]⟩ : Def)
  row_36 : defs[36]? = some (⟨.carry3, [.id (n+8), .id (n+32), .imm 0#64]⟩ : Def)
  row_38 : defs[38]? = some (⟨.mul, [.id (n+1), .id (n+3)]⟩ : Def)
  row_39 : defs[39]? = some (⟨.add3, [.id (n+17), .id (n+38), .id (n+36)]⟩ : Def)
  row_42 : defs[42]? = some (⟨.carry3, [.id (n+17), .id (n+38), .id (n+36)]⟩ : Def)
  row_44 : defs[44]? = some (⟨.mul, [.id (n+1), .id (n+13)]⟩ : Def)
  row_45 : defs[45]? = some (⟨.add3, [.id (n+24), .id (n+44), .id (n+42)]⟩ : Def)
  row_48 : defs[48]? = some (⟨.carry3, [.id (n+24), .id (n+44), .id (n+42)]⟩ : Def)
  row_50 : defs[50]? = some (⟨.mul, [.id (n+1), .id (n+14)]⟩ : Def)
  row_51 : defs[51]? = some (⟨.add3, [.id (n+29), .id (n+50), .id (n+48)]⟩ : Def)
  row_54 : defs[54]? = some (⟨.carry3, [.id (n+29), .id (n+50), .id (n+48)]⟩ : Def)
  row_56 : defs[56]? = some (⟨.umulh, [.id (n+1), .id (n+14)]⟩ : Def)
  row_57 : defs[57]? = some (⟨.add3, [.id (n+56), .imm 0#64, .id (n+54)]⟩ : Def)
  row_58 : defs[58]? = some (⟨.umulh, [.id (n+1), .id (n+2)]⟩ : Def)
  row_59 : defs[59]? = some (⟨.add3, [.id (n+39), .id (n+58), .imm 0#64]⟩ : Def)
  row_62 : defs[62]? = some (⟨.carry3, [.id (n+39), .id (n+58), .imm 0#64]⟩ : Def)
  row_64 : defs[64]? = some (⟨.umulh, [.id (n+1), .id (n+3)]⟩ : Def)
  row_65 : defs[65]? = some (⟨.add3, [.id (n+45), .id (n+64), .id (n+62)]⟩ : Def)
  row_68 : defs[68]? = some (⟨.carry3, [.id (n+45), .id (n+64), .id (n+62)]⟩ : Def)
  row_70 : defs[70]? = some (⟨.umulh, [.id (n+1), .id (n+13)]⟩ : Def)
  row_71 : defs[71]? = some (⟨.add3, [.id (n+51), .id (n+70), .id (n+68)]⟩ : Def)
  row_74 : defs[74]? = some (⟨.carry3, [.id (n+51), .id (n+70), .id (n+68)]⟩ : Def)
  row_76 : defs[76]? = some (⟨.add3, [.id (n+57), .imm 0#64, .id (n+74)]⟩ : Def)
  row_77 : defs[77]? = some (⟨.mul, [.id (n+30), .id (n+2)]⟩ : Def)
  row_78 : defs[78]? = some (⟨.add3, [.id (n+59), .id (n+77), .imm 0#64]⟩ : Def)
  row_81 : defs[81]? = some (⟨.carry3, [.id (n+59), .id (n+77), .imm 0#64]⟩ : Def)
  row_83 : defs[83]? = some (⟨.mul, [.id (n+30), .id (n+3)]⟩ : Def)
  row_84 : defs[84]? = some (⟨.add3, [.id (n+65), .id (n+83), .id (n+81)]⟩ : Def)
  row_87 : defs[87]? = some (⟨.carry3, [.id (n+65), .id (n+83), .id (n+81)]⟩ : Def)
  row_89 : defs[89]? = some (⟨.mul, [.id (n+30), .id (n+13)]⟩ : Def)
  row_90 : defs[90]? = some (⟨.add3, [.id (n+71), .id (n+89), .id (n+87)]⟩ : Def)
  row_93 : defs[93]? = some (⟨.carry3, [.id (n+71), .id (n+89), .id (n+87)]⟩ : Def)
  row_95 : defs[95]? = some (⟨.mul, [.id (n+30), .id (n+14)]⟩ : Def)
  row_96 : defs[96]? = some (⟨.add3, [.id (n+76), .id (n+95), .id (n+93)]⟩ : Def)
  row_99 : defs[99]? = some (⟨.carry3, [.id (n+76), .id (n+95), .id (n+93)]⟩ : Def)
  row_101 : defs[101]? = some (⟨.umulh, [.id (n+30), .id (n+14)]⟩ : Def)
  row_102 : defs[102]? = some (⟨.add3, [.id (n+101), .imm 0#64, .id (n+99)]⟩ : Def)
  row_103 : defs[103]? = some (⟨.umulh, [.id (n+30), .id (n+2)]⟩ : Def)
  row_104 : defs[104]? = some (⟨.add3, [.id (n+84), .id (n+103), .imm 0#64]⟩ : Def)
  row_107 : defs[107]? = some (⟨.carry3, [.id (n+84), .id (n+103), .imm 0#64]⟩ : Def)
  row_109 : defs[109]? = some (⟨.umulh, [.id (n+30), .id (n+3)]⟩ : Def)
  row_110 : defs[110]? = some (⟨.add3, [.id (n+90), .id (n+109), .id (n+107)]⟩ : Def)
  row_113 : defs[113]? = some (⟨.carry3, [.id (n+90), .id (n+109), .id (n+107)]⟩ : Def)
  row_115 : defs[115]? = some (⟨.umulh, [.id (n+30), .id (n+13)]⟩ : Def)
  row_116 : defs[116]? = some (⟨.add3, [.id (n+96), .id (n+115), .id (n+113)]⟩ : Def)
  row_119 : defs[119]? = some (⟨.carry3, [.id (n+96), .id (n+115), .id (n+113)]⟩ : Def)
  row_121 : defs[121]? = some (⟨.add3, [.id (n+102), .imm 0#64, .id (n+119)]⟩ : Def)
  row_122 : defs[122]? = some (⟨.mul, [.id (n+31), .id (n+2)]⟩ : Def)
  row_123 : defs[123]? = some (⟨.add3, [.id (n+104), .id (n+122), .imm 0#64]⟩ : Def)
  row_126 : defs[126]? = some (⟨.carry3, [.id (n+104), .id (n+122), .imm 0#64]⟩ : Def)
  row_128 : defs[128]? = some (⟨.mul, [.id (n+31), .id (n+3)]⟩ : Def)
  row_129 : defs[129]? = some (⟨.add3, [.id (n+110), .id (n+128), .id (n+126)]⟩ : Def)
  row_132 : defs[132]? = some (⟨.carry3, [.id (n+110), .id (n+128), .id (n+126)]⟩ : Def)
  row_134 : defs[134]? = some (⟨.mul, [.id (n+31), .id (n+13)]⟩ : Def)
  row_135 : defs[135]? = some (⟨.add3, [.id (n+116), .id (n+134), .id (n+132)]⟩ : Def)
  row_138 : defs[138]? = some (⟨.carry3, [.id (n+116), .id (n+134), .id (n+132)]⟩ : Def)
  row_140 : defs[140]? = some (⟨.mul, [.id (n+31), .id (n+14)]⟩ : Def)
  row_141 : defs[141]? = some (⟨.add3, [.id (n+121), .id (n+140), .id (n+138)]⟩ : Def)
  row_144 : defs[144]? = some (⟨.carry3, [.id (n+121), .id (n+140), .id (n+138)]⟩ : Def)
  row_146 : defs[146]? = some (⟨.umulh, [.id (n+31), .id (n+14)]⟩ : Def)
  row_147 : defs[147]? = some (⟨.add3, [.id (n+146), .imm 0#64, .id (n+144)]⟩ : Def)
  row_148 : defs[148]? = some (⟨.umulh, [.id (n+31), .id (n+2)]⟩ : Def)
  row_149 : defs[149]? = some (⟨.add3, [.id (n+129), .id (n+148), .imm 0#64]⟩ : Def)
  row_152 : defs[152]? = some (⟨.carry3, [.id (n+129), .id (n+148), .imm 0#64]⟩ : Def)
  row_154 : defs[154]? = some (⟨.umulh, [.id (n+31), .id (n+3)]⟩ : Def)
  row_155 : defs[155]? = some (⟨.add3, [.id (n+135), .id (n+154), .id (n+152)]⟩ : Def)
  row_158 : defs[158]? = some (⟨.carry3, [.id (n+135), .id (n+154), .id (n+152)]⟩ : Def)
  row_160 : defs[160]? = some (⟨.umulh, [.id (n+31), .id (n+13)]⟩ : Def)
  row_161 : defs[161]? = some (⟨.add3, [.id (n+141), .id (n+160), .id (n+158)]⟩ : Def)
  row_164 : defs[164]? = some (⟨.carry3, [.id (n+141), .id (n+160), .id (n+158)]⟩ : Def)
  row_166 : defs[166]? = some (⟨.add3, [.id (n+147), .imm 0#64, .id (n+164)]⟩ : Def)
  row_167 : defs[167]? = some (⟨.const 977#64, []⟩ : Def)
  row_168 : defs[168]? = some (⟨.orr, [.id (n+167), .imm 4294967296#64]⟩ : Def)
  row_169 : defs[169]? = some (⟨.mul, [.id (n+168), .id (n+149)]⟩ : Def)
  row_170 : defs[170]? = some (⟨.umulh, [.id (n+168), .id (n+149)]⟩ : Def)
  row_171 : defs[171]? = some (⟨.add3, [.id (n+4), .id (n+169), .imm 0#64]⟩ : Def)
  row_174 : defs[174]? = some (⟨.carry3, [.id (n+4), .id (n+169), .imm 0#64]⟩ : Def)
  row_176 : defs[176]? = some (⟨.mul, [.id (n+168), .id (n+155)]⟩ : Def)
  row_177 : defs[177]? = some (⟨.umulh, [.id (n+168), .id (n+155)]⟩ : Def)
  row_178 : defs[178]? = some (⟨.add3, [.id (n+33), .id (n+176), .id (n+174)]⟩ : Def)
  row_181 : defs[181]? = some (⟨.carry3, [.id (n+33), .id (n+176), .id (n+174)]⟩ : Def)
  row_183 : defs[183]? = some (⟨.mul, [.id (n+168), .id (n+161)]⟩ : Def)
  row_184 : defs[184]? = some (⟨.umulh, [.id (n+168), .id (n+161)]⟩ : Def)
  row_185 : defs[185]? = some (⟨.add3, [.id (n+78), .id (n+183), .id (n+181)]⟩ : Def)
  row_188 : defs[188]? = some (⟨.carry3, [.id (n+78), .id (n+183), .id (n+181)]⟩ : Def)
  row_190 : defs[190]? = some (⟨.mul, [.id (n+168), .id (n+166)]⟩ : Def)
  row_191 : defs[191]? = some (⟨.umulh, [.id (n+168), .id (n+166)]⟩ : Def)
  row_192 : defs[192]? = some (⟨.add3, [.id (n+123), .id (n+190), .id (n+188)]⟩ : Def)
  row_195 : defs[195]? = some (⟨.carry3, [.id (n+123), .id (n+190), .id (n+188)]⟩ : Def)
  row_197 : defs[197]? = some (⟨.cond 2#4, [.id (n+193), .id (n+194), .id (n+195), .id (n+196)]⟩ : Def)
  row_198 : defs[198]? = some (⟨.add3, [.id (n+178), .id (n+170), .imm 0#64]⟩ : Def)
  row_201 : defs[201]? = some (⟨.carry3, [.id (n+178), .id (n+170), .imm 0#64]⟩ : Def)
  row_203 : defs[203]? = some (⟨.add3, [.id (n+185), .id (n+177), .id (n+201)]⟩ : Def)
  row_206 : defs[206]? = some (⟨.carry3, [.id (n+185), .id (n+177), .id (n+201)]⟩ : Def)
  row_208 : defs[208]? = some (⟨.add3, [.id (n+192), .id (n+184), .id (n+206)]⟩ : Def)
  row_211 : defs[211]? = some (⟨.carry3, [.id (n+192), .id (n+184), .id (n+206)]⟩ : Def)
  row_213 : defs[213]? = some (⟨.add3, [.id (n+197), .id (n+191), .id (n+211)]⟩ : Def)
  row_214 : defs[214]? = some (⟨.add, [.id (n+213), .imm 1#64]⟩ : Def)
  row_215 : defs[215]? = some (⟨.mul, [.id (n+168), .id (n+214)]⟩ : Def)
  row_216 : defs[216]? = some (⟨.umulh, [.id (n+168), .id (n+214)]⟩ : Def)
  row_217 : defs[217]? = some (⟨.add3, [.id (n+171), .id (n+215), .imm 0#64]⟩ : Def)
  row_220 : defs[220]? = some (⟨.carry3, [.id (n+171), .id (n+215), .imm 0#64]⟩ : Def)
  row_222 : defs[222]? = some (⟨.add3, [.id (n+198), .id (n+216), .id (n+220)]⟩ : Def)
  row_225 : defs[225]? = some (⟨.carry3, [.id (n+198), .id (n+216), .id (n+220)]⟩ : Def)
  row_227 : defs[227]? = some (⟨.add3, [.id (n+203), .imm 0#64, .id (n+225)]⟩ : Def)
  row_230 : defs[230]? = some (⟨.carry3, [.id (n+203), .imm 0#64, .id (n+225)]⟩ : Def)
  row_232 : defs[232]? = some (⟨.add3, [.id (n+208), .imm 0#64, .id (n+230)]⟩ : Def)
  row_235 : defs[235]? = some (⟨.carry3, [.id (n+208), .imm 0#64, .id (n+230)]⟩ : Def)
  row_237 : defs[237]? = some (⟨.cselc 3#4, [.id (n+233), .id (n+234), .id (n+235), .id (n+236), .id (n+168), .imm 0#64]⟩ : Def)
  row_238 : defs[238]? = some (⟨.sbc3, [.id (n+217), .id (n+237), .imm 1#64]⟩ : Def)
  row_241 : defs[241]? = some (⟨.sbc3C, [.id (n+217), .id (n+237), .imm 1#64]⟩ : Def)
  row_243 : defs[243]? = some (⟨.sbc3, [.id (n+222), .imm 0#64, .id (n+241)]⟩ : Def)
  row_246 : defs[246]? = some (⟨.sbc3C, [.id (n+222), .imm 0#64, .id (n+241)]⟩ : Def)
  row_248 : defs[248]? = some (⟨.sbc3, [.id (n+227), .imm 0#64, .id (n+246)]⟩ : Def)
  row_251 : defs[251]? = some (⟨.sbc3C, [.id (n+227), .imm 0#64, .id (n+246)]⟩ : Def)
  row_253 : defs[253]? = some (⟨.sbc3, [.id (n+232), .imm 0#64, .id (n+251)]⟩ : Def)

def compilerRows (n xs ys : Nat) : List Def := [
  inputWordDef (xs),
  inputWordDef (xs+8),
  inputWordDef (ys),
  inputWordDef (ys+8),
  (⟨.mul, [.id n, .id (n+2)]⟩ : Def),
  (⟨.umulh, [.id n, .id (n+2)]⟩ : Def),
  (⟨.mul, [.id n, .id (n+3)]⟩ : Def),
  (⟨.umulh, [.id n, .id (n+3)]⟩ : Def),
  (⟨.add3, [.id (n+5), .id (n+6), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+5), .id (n+6), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+5), .id (n+6), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+5), .id (n+6), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+5), .id (n+6), .imm 0#64]⟩ : Def),
  inputWordDef (ys+16),
  inputWordDef (ys+24),
  (⟨.mul, [.id n, .id (n+13)]⟩ : Def),
  (⟨.umulh, [.id n, .id (n+13)]⟩ : Def),
  (⟨.add3, [.id (n+7), .id (n+15), .id (n+11)]⟩ : Def),
  (⟨.add3N, [.id (n+7), .id (n+15), .id (n+11)]⟩ : Def),
  (⟨.add3Z, [.id (n+7), .id (n+15), .id (n+11)]⟩ : Def),
  (⟨.carry3, [.id (n+7), .id (n+15), .id (n+11)]⟩ : Def),
  (⟨.ovf3, [.id (n+7), .id (n+15), .id (n+11)]⟩ : Def),
  (⟨.mul, [.id n, .id (n+14)]⟩ : Def),
  (⟨.umulh, [.id n, .id (n+14)]⟩ : Def),
  (⟨.add3, [.id (n+16), .id (n+22), .id (n+20)]⟩ : Def),
  (⟨.add3N, [.id (n+16), .id (n+22), .id (n+20)]⟩ : Def),
  (⟨.add3Z, [.id (n+16), .id (n+22), .id (n+20)]⟩ : Def),
  (⟨.carry3, [.id (n+16), .id (n+22), .id (n+20)]⟩ : Def),
  (⟨.ovf3, [.id (n+16), .id (n+22), .id (n+20)]⟩ : Def),
  (⟨.add3, [.id (n+23), .imm 0#64, .id (n+27)]⟩ : Def),
  inputWordDef (xs+16),
  inputWordDef (xs+24),
  (⟨.mul, [.id (n+1), .id (n+2)]⟩ : Def),
  (⟨.add3, [.id (n+8), .id (n+32), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+8), .id (n+32), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+8), .id (n+32), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+8), .id (n+32), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+8), .id (n+32), .imm 0#64]⟩ : Def),
  (⟨.mul, [.id (n+1), .id (n+3)]⟩ : Def),
  (⟨.add3, [.id (n+17), .id (n+38), .id (n+36)]⟩ : Def),
  (⟨.add3N, [.id (n+17), .id (n+38), .id (n+36)]⟩ : Def),
  (⟨.add3Z, [.id (n+17), .id (n+38), .id (n+36)]⟩ : Def),
  (⟨.carry3, [.id (n+17), .id (n+38), .id (n+36)]⟩ : Def),
  (⟨.ovf3, [.id (n+17), .id (n+38), .id (n+36)]⟩ : Def),
  (⟨.mul, [.id (n+1), .id (n+13)]⟩ : Def),
  (⟨.add3, [.id (n+24), .id (n+44), .id (n+42)]⟩ : Def),
  (⟨.add3N, [.id (n+24), .id (n+44), .id (n+42)]⟩ : Def),
  (⟨.add3Z, [.id (n+24), .id (n+44), .id (n+42)]⟩ : Def),
  (⟨.carry3, [.id (n+24), .id (n+44), .id (n+42)]⟩ : Def),
  (⟨.ovf3, [.id (n+24), .id (n+44), .id (n+42)]⟩ : Def),
  (⟨.mul, [.id (n+1), .id (n+14)]⟩ : Def),
  (⟨.add3, [.id (n+29), .id (n+50), .id (n+48)]⟩ : Def),
  (⟨.add3N, [.id (n+29), .id (n+50), .id (n+48)]⟩ : Def),
  (⟨.add3Z, [.id (n+29), .id (n+50), .id (n+48)]⟩ : Def),
  (⟨.carry3, [.id (n+29), .id (n+50), .id (n+48)]⟩ : Def),
  (⟨.ovf3, [.id (n+29), .id (n+50), .id (n+48)]⟩ : Def),
  (⟨.umulh, [.id (n+1), .id (n+14)]⟩ : Def),
  (⟨.add3, [.id (n+56), .imm 0#64, .id (n+54)]⟩ : Def),
  (⟨.umulh, [.id (n+1), .id (n+2)]⟩ : Def),
  (⟨.add3, [.id (n+39), .id (n+58), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+39), .id (n+58), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+39), .id (n+58), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+39), .id (n+58), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+39), .id (n+58), .imm 0#64]⟩ : Def),
  (⟨.umulh, [.id (n+1), .id (n+3)]⟩ : Def),
  (⟨.add3, [.id (n+45), .id (n+64), .id (n+62)]⟩ : Def),
  (⟨.add3N, [.id (n+45), .id (n+64), .id (n+62)]⟩ : Def),
  (⟨.add3Z, [.id (n+45), .id (n+64), .id (n+62)]⟩ : Def),
  (⟨.carry3, [.id (n+45), .id (n+64), .id (n+62)]⟩ : Def),
  (⟨.ovf3, [.id (n+45), .id (n+64), .id (n+62)]⟩ : Def),
  (⟨.umulh, [.id (n+1), .id (n+13)]⟩ : Def),
  (⟨.add3, [.id (n+51), .id (n+70), .id (n+68)]⟩ : Def),
  (⟨.add3N, [.id (n+51), .id (n+70), .id (n+68)]⟩ : Def),
  (⟨.add3Z, [.id (n+51), .id (n+70), .id (n+68)]⟩ : Def),
  (⟨.carry3, [.id (n+51), .id (n+70), .id (n+68)]⟩ : Def),
  (⟨.ovf3, [.id (n+51), .id (n+70), .id (n+68)]⟩ : Def),
  (⟨.add3, [.id (n+57), .imm 0#64, .id (n+74)]⟩ : Def),
  (⟨.mul, [.id (n+30), .id (n+2)]⟩ : Def),
  (⟨.add3, [.id (n+59), .id (n+77), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+59), .id (n+77), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+59), .id (n+77), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+59), .id (n+77), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+59), .id (n+77), .imm 0#64]⟩ : Def),
  (⟨.mul, [.id (n+30), .id (n+3)]⟩ : Def),
  (⟨.add3, [.id (n+65), .id (n+83), .id (n+81)]⟩ : Def),
  (⟨.add3N, [.id (n+65), .id (n+83), .id (n+81)]⟩ : Def),
  (⟨.add3Z, [.id (n+65), .id (n+83), .id (n+81)]⟩ : Def),
  (⟨.carry3, [.id (n+65), .id (n+83), .id (n+81)]⟩ : Def),
  (⟨.ovf3, [.id (n+65), .id (n+83), .id (n+81)]⟩ : Def),
  (⟨.mul, [.id (n+30), .id (n+13)]⟩ : Def),
  (⟨.add3, [.id (n+71), .id (n+89), .id (n+87)]⟩ : Def),
  (⟨.add3N, [.id (n+71), .id (n+89), .id (n+87)]⟩ : Def),
  (⟨.add3Z, [.id (n+71), .id (n+89), .id (n+87)]⟩ : Def),
  (⟨.carry3, [.id (n+71), .id (n+89), .id (n+87)]⟩ : Def),
  (⟨.ovf3, [.id (n+71), .id (n+89), .id (n+87)]⟩ : Def),
  (⟨.mul, [.id (n+30), .id (n+14)]⟩ : Def),
  (⟨.add3, [.id (n+76), .id (n+95), .id (n+93)]⟩ : Def),
  (⟨.add3N, [.id (n+76), .id (n+95), .id (n+93)]⟩ : Def),
  (⟨.add3Z, [.id (n+76), .id (n+95), .id (n+93)]⟩ : Def),
  (⟨.carry3, [.id (n+76), .id (n+95), .id (n+93)]⟩ : Def),
  (⟨.ovf3, [.id (n+76), .id (n+95), .id (n+93)]⟩ : Def),
  (⟨.umulh, [.id (n+30), .id (n+14)]⟩ : Def),
  (⟨.add3, [.id (n+101), .imm 0#64, .id (n+99)]⟩ : Def),
  (⟨.umulh, [.id (n+30), .id (n+2)]⟩ : Def),
  (⟨.add3, [.id (n+84), .id (n+103), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+84), .id (n+103), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+84), .id (n+103), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+84), .id (n+103), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+84), .id (n+103), .imm 0#64]⟩ : Def),
  (⟨.umulh, [.id (n+30), .id (n+3)]⟩ : Def),
  (⟨.add3, [.id (n+90), .id (n+109), .id (n+107)]⟩ : Def),
  (⟨.add3N, [.id (n+90), .id (n+109), .id (n+107)]⟩ : Def),
  (⟨.add3Z, [.id (n+90), .id (n+109), .id (n+107)]⟩ : Def),
  (⟨.carry3, [.id (n+90), .id (n+109), .id (n+107)]⟩ : Def),
  (⟨.ovf3, [.id (n+90), .id (n+109), .id (n+107)]⟩ : Def),
  (⟨.umulh, [.id (n+30), .id (n+13)]⟩ : Def),
  (⟨.add3, [.id (n+96), .id (n+115), .id (n+113)]⟩ : Def),
  (⟨.add3N, [.id (n+96), .id (n+115), .id (n+113)]⟩ : Def),
  (⟨.add3Z, [.id (n+96), .id (n+115), .id (n+113)]⟩ : Def),
  (⟨.carry3, [.id (n+96), .id (n+115), .id (n+113)]⟩ : Def),
  (⟨.ovf3, [.id (n+96), .id (n+115), .id (n+113)]⟩ : Def),
  (⟨.add3, [.id (n+102), .imm 0#64, .id (n+119)]⟩ : Def),
  (⟨.mul, [.id (n+31), .id (n+2)]⟩ : Def),
  (⟨.add3, [.id (n+104), .id (n+122), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+104), .id (n+122), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+104), .id (n+122), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+104), .id (n+122), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+104), .id (n+122), .imm 0#64]⟩ : Def),
  (⟨.mul, [.id (n+31), .id (n+3)]⟩ : Def),
  (⟨.add3, [.id (n+110), .id (n+128), .id (n+126)]⟩ : Def),
  (⟨.add3N, [.id (n+110), .id (n+128), .id (n+126)]⟩ : Def),
  (⟨.add3Z, [.id (n+110), .id (n+128), .id (n+126)]⟩ : Def),
  (⟨.carry3, [.id (n+110), .id (n+128), .id (n+126)]⟩ : Def),
  (⟨.ovf3, [.id (n+110), .id (n+128), .id (n+126)]⟩ : Def),
  (⟨.mul, [.id (n+31), .id (n+13)]⟩ : Def),
  (⟨.add3, [.id (n+116), .id (n+134), .id (n+132)]⟩ : Def),
  (⟨.add3N, [.id (n+116), .id (n+134), .id (n+132)]⟩ : Def),
  (⟨.add3Z, [.id (n+116), .id (n+134), .id (n+132)]⟩ : Def),
  (⟨.carry3, [.id (n+116), .id (n+134), .id (n+132)]⟩ : Def),
  (⟨.ovf3, [.id (n+116), .id (n+134), .id (n+132)]⟩ : Def),
  (⟨.mul, [.id (n+31), .id (n+14)]⟩ : Def),
  (⟨.add3, [.id (n+121), .id (n+140), .id (n+138)]⟩ : Def),
  (⟨.add3N, [.id (n+121), .id (n+140), .id (n+138)]⟩ : Def),
  (⟨.add3Z, [.id (n+121), .id (n+140), .id (n+138)]⟩ : Def),
  (⟨.carry3, [.id (n+121), .id (n+140), .id (n+138)]⟩ : Def),
  (⟨.ovf3, [.id (n+121), .id (n+140), .id (n+138)]⟩ : Def),
  (⟨.umulh, [.id (n+31), .id (n+14)]⟩ : Def),
  (⟨.add3, [.id (n+146), .imm 0#64, .id (n+144)]⟩ : Def),
  (⟨.umulh, [.id (n+31), .id (n+2)]⟩ : Def),
  (⟨.add3, [.id (n+129), .id (n+148), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+129), .id (n+148), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+129), .id (n+148), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+129), .id (n+148), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+129), .id (n+148), .imm 0#64]⟩ : Def),
  (⟨.umulh, [.id (n+31), .id (n+3)]⟩ : Def),
  (⟨.add3, [.id (n+135), .id (n+154), .id (n+152)]⟩ : Def),
  (⟨.add3N, [.id (n+135), .id (n+154), .id (n+152)]⟩ : Def),
  (⟨.add3Z, [.id (n+135), .id (n+154), .id (n+152)]⟩ : Def),
  (⟨.carry3, [.id (n+135), .id (n+154), .id (n+152)]⟩ : Def),
  (⟨.ovf3, [.id (n+135), .id (n+154), .id (n+152)]⟩ : Def),
  (⟨.umulh, [.id (n+31), .id (n+13)]⟩ : Def),
  (⟨.add3, [.id (n+141), .id (n+160), .id (n+158)]⟩ : Def),
  (⟨.add3N, [.id (n+141), .id (n+160), .id (n+158)]⟩ : Def),
  (⟨.add3Z, [.id (n+141), .id (n+160), .id (n+158)]⟩ : Def),
  (⟨.carry3, [.id (n+141), .id (n+160), .id (n+158)]⟩ : Def),
  (⟨.ovf3, [.id (n+141), .id (n+160), .id (n+158)]⟩ : Def),
  (⟨.add3, [.id (n+147), .imm 0#64, .id (n+164)]⟩ : Def),
  (⟨.const 977#64, []⟩ : Def),
  (⟨.orr, [.id (n+167), .imm 4294967296#64]⟩ : Def),
  (⟨.mul, [.id (n+168), .id (n+149)]⟩ : Def),
  (⟨.umulh, [.id (n+168), .id (n+149)]⟩ : Def),
  (⟨.add3, [.id (n+4), .id (n+169), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+4), .id (n+169), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+4), .id (n+169), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+4), .id (n+169), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+4), .id (n+169), .imm 0#64]⟩ : Def),
  (⟨.mul, [.id (n+168), .id (n+155)]⟩ : Def),
  (⟨.umulh, [.id (n+168), .id (n+155)]⟩ : Def),
  (⟨.add3, [.id (n+33), .id (n+176), .id (n+174)]⟩ : Def),
  (⟨.add3N, [.id (n+33), .id (n+176), .id (n+174)]⟩ : Def),
  (⟨.add3Z, [.id (n+33), .id (n+176), .id (n+174)]⟩ : Def),
  (⟨.carry3, [.id (n+33), .id (n+176), .id (n+174)]⟩ : Def),
  (⟨.ovf3, [.id (n+33), .id (n+176), .id (n+174)]⟩ : Def),
  (⟨.mul, [.id (n+168), .id (n+161)]⟩ : Def),
  (⟨.umulh, [.id (n+168), .id (n+161)]⟩ : Def),
  (⟨.add3, [.id (n+78), .id (n+183), .id (n+181)]⟩ : Def),
  (⟨.add3N, [.id (n+78), .id (n+183), .id (n+181)]⟩ : Def),
  (⟨.add3Z, [.id (n+78), .id (n+183), .id (n+181)]⟩ : Def),
  (⟨.carry3, [.id (n+78), .id (n+183), .id (n+181)]⟩ : Def),
  (⟨.ovf3, [.id (n+78), .id (n+183), .id (n+181)]⟩ : Def),
  (⟨.mul, [.id (n+168), .id (n+166)]⟩ : Def),
  (⟨.umulh, [.id (n+168), .id (n+166)]⟩ : Def),
  (⟨.add3, [.id (n+123), .id (n+190), .id (n+188)]⟩ : Def),
  (⟨.add3N, [.id (n+123), .id (n+190), .id (n+188)]⟩ : Def),
  (⟨.add3Z, [.id (n+123), .id (n+190), .id (n+188)]⟩ : Def),
  (⟨.carry3, [.id (n+123), .id (n+190), .id (n+188)]⟩ : Def),
  (⟨.ovf3, [.id (n+123), .id (n+190), .id (n+188)]⟩ : Def),
  (⟨.cond 2#4, [.id (n+193), .id (n+194), .id (n+195), .id (n+196)]⟩ : Def),
  (⟨.add3, [.id (n+178), .id (n+170), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+178), .id (n+170), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+178), .id (n+170), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+178), .id (n+170), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+178), .id (n+170), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+185), .id (n+177), .id (n+201)]⟩ : Def),
  (⟨.add3N, [.id (n+185), .id (n+177), .id (n+201)]⟩ : Def),
  (⟨.add3Z, [.id (n+185), .id (n+177), .id (n+201)]⟩ : Def),
  (⟨.carry3, [.id (n+185), .id (n+177), .id (n+201)]⟩ : Def),
  (⟨.ovf3, [.id (n+185), .id (n+177), .id (n+201)]⟩ : Def),
  (⟨.add3, [.id (n+192), .id (n+184), .id (n+206)]⟩ : Def),
  (⟨.add3N, [.id (n+192), .id (n+184), .id (n+206)]⟩ : Def),
  (⟨.add3Z, [.id (n+192), .id (n+184), .id (n+206)]⟩ : Def),
  (⟨.carry3, [.id (n+192), .id (n+184), .id (n+206)]⟩ : Def),
  (⟨.ovf3, [.id (n+192), .id (n+184), .id (n+206)]⟩ : Def),
  (⟨.add3, [.id (n+197), .id (n+191), .id (n+211)]⟩ : Def),
  (⟨.add, [.id (n+213), .imm 1#64]⟩ : Def),
  (⟨.mul, [.id (n+168), .id (n+214)]⟩ : Def),
  (⟨.umulh, [.id (n+168), .id (n+214)]⟩ : Def),
  (⟨.add3, [.id (n+171), .id (n+215), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+171), .id (n+215), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+171), .id (n+215), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+171), .id (n+215), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+171), .id (n+215), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+198), .id (n+216), .id (n+220)]⟩ : Def),
  (⟨.add3N, [.id (n+198), .id (n+216), .id (n+220)]⟩ : Def),
  (⟨.add3Z, [.id (n+198), .id (n+216), .id (n+220)]⟩ : Def),
  (⟨.carry3, [.id (n+198), .id (n+216), .id (n+220)]⟩ : Def),
  (⟨.ovf3, [.id (n+198), .id (n+216), .id (n+220)]⟩ : Def),
  (⟨.add3, [.id (n+203), .imm 0#64, .id (n+225)]⟩ : Def),
  (⟨.add3N, [.id (n+203), .imm 0#64, .id (n+225)]⟩ : Def),
  (⟨.add3Z, [.id (n+203), .imm 0#64, .id (n+225)]⟩ : Def),
  (⟨.carry3, [.id (n+203), .imm 0#64, .id (n+225)]⟩ : Def),
  (⟨.ovf3, [.id (n+203), .imm 0#64, .id (n+225)]⟩ : Def),
  (⟨.add3, [.id (n+208), .imm 0#64, .id (n+230)]⟩ : Def),
  (⟨.add3N, [.id (n+208), .imm 0#64, .id (n+230)]⟩ : Def),
  (⟨.add3Z, [.id (n+208), .imm 0#64, .id (n+230)]⟩ : Def),
  (⟨.carry3, [.id (n+208), .imm 0#64, .id (n+230)]⟩ : Def),
  (⟨.ovf3, [.id (n+208), .imm 0#64, .id (n+230)]⟩ : Def),
  (⟨.cselc 3#4, [.id (n+233), .id (n+234), .id (n+235), .id (n+236), .id (n+168), .imm 0#64]⟩ : Def),
  (⟨.sbc3, [.id (n+217), .id (n+237), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+217), .id (n+237), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+217), .id (n+237), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+217), .id (n+237), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+217), .id (n+237), .imm 1#64]⟩ : Def),
  (⟨.sbc3, [.id (n+222), .imm 0#64, .id (n+241)]⟩ : Def),
  (⟨.sbc3N, [.id (n+222), .imm 0#64, .id (n+241)]⟩ : Def),
  (⟨.sbc3Z, [.id (n+222), .imm 0#64, .id (n+241)]⟩ : Def),
  (⟨.sbc3C, [.id (n+222), .imm 0#64, .id (n+241)]⟩ : Def),
  (⟨.sbc3V, [.id (n+222), .imm 0#64, .id (n+241)]⟩ : Def),
  (⟨.sbc3, [.id (n+227), .imm 0#64, .id (n+246)]⟩ : Def),
  (⟨.sbc3N, [.id (n+227), .imm 0#64, .id (n+246)]⟩ : Def),
  (⟨.sbc3Z, [.id (n+227), .imm 0#64, .id (n+246)]⟩ : Def),
  (⟨.sbc3C, [.id (n+227), .imm 0#64, .id (n+246)]⟩ : Def),
  (⟨.sbc3V, [.id (n+227), .imm 0#64, .id (n+246)]⟩ : Def),
  (⟨.sbc3, [.id (n+232), .imm 0#64, .id (n+251)]⟩ : Def)]

theorem row_positions (n xs ys : Nat) : RowPositions (compilerRows n xs ys) n := by
  constructor <;> rfl

theorem load_positions (n xs ys : Nat) : LoadPositions (compilerRows n xs ys) xs ys := by
  constructor <;> rfl

theorem equations_of_positions (inputs : List (BitVec 64)) (defs : List Def) (n : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n) :
    Equations (fun i => (evalDefs inputs defs).getD i 0) n := by
  constructor
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 4 (⟨.mul, [.id n, .id (n+2)]⟩ : Def) pos.row_4
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 5 (⟨.umulh, [.id n, .id (n+2)]⟩ : Def) pos.row_5
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 6 (⟨.mul, [.id n, .id (n+3)]⟩ : Def) pos.row_6
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 7 (⟨.umulh, [.id n, .id (n+3)]⟩ : Def) pos.row_7
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 8 (⟨.add3, [.id (n+5), .id (n+6), .imm 0#64]⟩ : Def) pos.row_8
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 11 (⟨.carry3, [.id (n+5), .id (n+6), .imm 0#64]⟩ : Def) pos.row_11
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 15 (⟨.mul, [.id n, .id (n+13)]⟩ : Def) pos.row_15
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 16 (⟨.umulh, [.id n, .id (n+13)]⟩ : Def) pos.row_16
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 17 (⟨.add3, [.id (n+7), .id (n+15), .id (n+11)]⟩ : Def) pos.row_17
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 20 (⟨.carry3, [.id (n+7), .id (n+15), .id (n+11)]⟩ : Def) pos.row_20
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 22 (⟨.mul, [.id n, .id (n+14)]⟩ : Def) pos.row_22
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 23 (⟨.umulh, [.id n, .id (n+14)]⟩ : Def) pos.row_23
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 24 (⟨.add3, [.id (n+16), .id (n+22), .id (n+20)]⟩ : Def) pos.row_24
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 27 (⟨.carry3, [.id (n+16), .id (n+22), .id (n+20)]⟩ : Def) pos.row_27
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 29 (⟨.add3, [.id (n+23), .imm 0#64, .id (n+27)]⟩ : Def) pos.row_29
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 32 (⟨.mul, [.id (n+1), .id (n+2)]⟩ : Def) pos.row_32
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 33 (⟨.add3, [.id (n+8), .id (n+32), .imm 0#64]⟩ : Def) pos.row_33
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 36 (⟨.carry3, [.id (n+8), .id (n+32), .imm 0#64]⟩ : Def) pos.row_36
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 38 (⟨.mul, [.id (n+1), .id (n+3)]⟩ : Def) pos.row_38
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 39 (⟨.add3, [.id (n+17), .id (n+38), .id (n+36)]⟩ : Def) pos.row_39
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 42 (⟨.carry3, [.id (n+17), .id (n+38), .id (n+36)]⟩ : Def) pos.row_42
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 44 (⟨.mul, [.id (n+1), .id (n+13)]⟩ : Def) pos.row_44
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 45 (⟨.add3, [.id (n+24), .id (n+44), .id (n+42)]⟩ : Def) pos.row_45
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 48 (⟨.carry3, [.id (n+24), .id (n+44), .id (n+42)]⟩ : Def) pos.row_48
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 50 (⟨.mul, [.id (n+1), .id (n+14)]⟩ : Def) pos.row_50
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 51 (⟨.add3, [.id (n+29), .id (n+50), .id (n+48)]⟩ : Def) pos.row_51
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 54 (⟨.carry3, [.id (n+29), .id (n+50), .id (n+48)]⟩ : Def) pos.row_54
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 56 (⟨.umulh, [.id (n+1), .id (n+14)]⟩ : Def) pos.row_56
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 57 (⟨.add3, [.id (n+56), .imm 0#64, .id (n+54)]⟩ : Def) pos.row_57
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 58 (⟨.umulh, [.id (n+1), .id (n+2)]⟩ : Def) pos.row_58
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 59 (⟨.add3, [.id (n+39), .id (n+58), .imm 0#64]⟩ : Def) pos.row_59
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 62 (⟨.carry3, [.id (n+39), .id (n+58), .imm 0#64]⟩ : Def) pos.row_62
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 64 (⟨.umulh, [.id (n+1), .id (n+3)]⟩ : Def) pos.row_64
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 65 (⟨.add3, [.id (n+45), .id (n+64), .id (n+62)]⟩ : Def) pos.row_65
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 68 (⟨.carry3, [.id (n+45), .id (n+64), .id (n+62)]⟩ : Def) pos.row_68
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 70 (⟨.umulh, [.id (n+1), .id (n+13)]⟩ : Def) pos.row_70
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 71 (⟨.add3, [.id (n+51), .id (n+70), .id (n+68)]⟩ : Def) pos.row_71
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 74 (⟨.carry3, [.id (n+51), .id (n+70), .id (n+68)]⟩ : Def) pos.row_74
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 76 (⟨.add3, [.id (n+57), .imm 0#64, .id (n+74)]⟩ : Def) pos.row_76
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 77 (⟨.mul, [.id (n+30), .id (n+2)]⟩ : Def) pos.row_77
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 78 (⟨.add3, [.id (n+59), .id (n+77), .imm 0#64]⟩ : Def) pos.row_78
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 81 (⟨.carry3, [.id (n+59), .id (n+77), .imm 0#64]⟩ : Def) pos.row_81
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 83 (⟨.mul, [.id (n+30), .id (n+3)]⟩ : Def) pos.row_83
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 84 (⟨.add3, [.id (n+65), .id (n+83), .id (n+81)]⟩ : Def) pos.row_84
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 87 (⟨.carry3, [.id (n+65), .id (n+83), .id (n+81)]⟩ : Def) pos.row_87
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 89 (⟨.mul, [.id (n+30), .id (n+13)]⟩ : Def) pos.row_89
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 90 (⟨.add3, [.id (n+71), .id (n+89), .id (n+87)]⟩ : Def) pos.row_90
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 93 (⟨.carry3, [.id (n+71), .id (n+89), .id (n+87)]⟩ : Def) pos.row_93
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 95 (⟨.mul, [.id (n+30), .id (n+14)]⟩ : Def) pos.row_95
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 96 (⟨.add3, [.id (n+76), .id (n+95), .id (n+93)]⟩ : Def) pos.row_96
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 99 (⟨.carry3, [.id (n+76), .id (n+95), .id (n+93)]⟩ : Def) pos.row_99
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 101 (⟨.umulh, [.id (n+30), .id (n+14)]⟩ : Def) pos.row_101
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 102 (⟨.add3, [.id (n+101), .imm 0#64, .id (n+99)]⟩ : Def) pos.row_102
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 103 (⟨.umulh, [.id (n+30), .id (n+2)]⟩ : Def) pos.row_103
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 104 (⟨.add3, [.id (n+84), .id (n+103), .imm 0#64]⟩ : Def) pos.row_104
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 107 (⟨.carry3, [.id (n+84), .id (n+103), .imm 0#64]⟩ : Def) pos.row_107
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 109 (⟨.umulh, [.id (n+30), .id (n+3)]⟩ : Def) pos.row_109
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 110 (⟨.add3, [.id (n+90), .id (n+109), .id (n+107)]⟩ : Def) pos.row_110
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 113 (⟨.carry3, [.id (n+90), .id (n+109), .id (n+107)]⟩ : Def) pos.row_113
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 115 (⟨.umulh, [.id (n+30), .id (n+13)]⟩ : Def) pos.row_115
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 116 (⟨.add3, [.id (n+96), .id (n+115), .id (n+113)]⟩ : Def) pos.row_116
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 119 (⟨.carry3, [.id (n+96), .id (n+115), .id (n+113)]⟩ : Def) pos.row_119
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 121 (⟨.add3, [.id (n+102), .imm 0#64, .id (n+119)]⟩ : Def) pos.row_121
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 122 (⟨.mul, [.id (n+31), .id (n+2)]⟩ : Def) pos.row_122
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 123 (⟨.add3, [.id (n+104), .id (n+122), .imm 0#64]⟩ : Def) pos.row_123
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 126 (⟨.carry3, [.id (n+104), .id (n+122), .imm 0#64]⟩ : Def) pos.row_126
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 128 (⟨.mul, [.id (n+31), .id (n+3)]⟩ : Def) pos.row_128
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 129 (⟨.add3, [.id (n+110), .id (n+128), .id (n+126)]⟩ : Def) pos.row_129
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 132 (⟨.carry3, [.id (n+110), .id (n+128), .id (n+126)]⟩ : Def) pos.row_132
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 134 (⟨.mul, [.id (n+31), .id (n+13)]⟩ : Def) pos.row_134
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 135 (⟨.add3, [.id (n+116), .id (n+134), .id (n+132)]⟩ : Def) pos.row_135
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 138 (⟨.carry3, [.id (n+116), .id (n+134), .id (n+132)]⟩ : Def) pos.row_138
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 140 (⟨.mul, [.id (n+31), .id (n+14)]⟩ : Def) pos.row_140
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 141 (⟨.add3, [.id (n+121), .id (n+140), .id (n+138)]⟩ : Def) pos.row_141
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 144 (⟨.carry3, [.id (n+121), .id (n+140), .id (n+138)]⟩ : Def) pos.row_144
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 146 (⟨.umulh, [.id (n+31), .id (n+14)]⟩ : Def) pos.row_146
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 147 (⟨.add3, [.id (n+146), .imm 0#64, .id (n+144)]⟩ : Def) pos.row_147
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 148 (⟨.umulh, [.id (n+31), .id (n+2)]⟩ : Def) pos.row_148
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 149 (⟨.add3, [.id (n+129), .id (n+148), .imm 0#64]⟩ : Def) pos.row_149
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 152 (⟨.carry3, [.id (n+129), .id (n+148), .imm 0#64]⟩ : Def) pos.row_152
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 154 (⟨.umulh, [.id (n+31), .id (n+3)]⟩ : Def) pos.row_154
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 155 (⟨.add3, [.id (n+135), .id (n+154), .id (n+152)]⟩ : Def) pos.row_155
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 158 (⟨.carry3, [.id (n+135), .id (n+154), .id (n+152)]⟩ : Def) pos.row_158
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 160 (⟨.umulh, [.id (n+31), .id (n+13)]⟩ : Def) pos.row_160
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 161 (⟨.add3, [.id (n+141), .id (n+160), .id (n+158)]⟩ : Def) pos.row_161
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 164 (⟨.carry3, [.id (n+141), .id (n+160), .id (n+158)]⟩ : Def) pos.row_164
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 166 (⟨.add3, [.id (n+147), .imm 0#64, .id (n+164)]⟩ : Def) pos.row_166
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · have h := TableEval.evalDefs_row inputs defs 167 (⟨.const 977#64, []⟩ : Def) pos.row_167
      (by rw [lengthEq]; simp [Def.Below, Arg.Below])
    rw [lengthEq, const_eval] at h
    exact h
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 168 (⟨.orr, [.id (n+167), .imm 4294967296#64]⟩ : Def) pos.row_168
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 169 (⟨.mul, [.id (n+168), .id (n+149)]⟩ : Def) pos.row_169
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 170 (⟨.umulh, [.id (n+168), .id (n+149)]⟩ : Def) pos.row_170
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 171 (⟨.add3, [.id (n+4), .id (n+169), .imm 0#64]⟩ : Def) pos.row_171
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 174 (⟨.carry3, [.id (n+4), .id (n+169), .imm 0#64]⟩ : Def) pos.row_174
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 176 (⟨.mul, [.id (n+168), .id (n+155)]⟩ : Def) pos.row_176
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 177 (⟨.umulh, [.id (n+168), .id (n+155)]⟩ : Def) pos.row_177
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 178 (⟨.add3, [.id (n+33), .id (n+176), .id (n+174)]⟩ : Def) pos.row_178
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 181 (⟨.carry3, [.id (n+33), .id (n+176), .id (n+174)]⟩ : Def) pos.row_181
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 183 (⟨.mul, [.id (n+168), .id (n+161)]⟩ : Def) pos.row_183
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 184 (⟨.umulh, [.id (n+168), .id (n+161)]⟩ : Def) pos.row_184
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 185 (⟨.add3, [.id (n+78), .id (n+183), .id (n+181)]⟩ : Def) pos.row_185
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 188 (⟨.carry3, [.id (n+78), .id (n+183), .id (n+181)]⟩ : Def) pos.row_188
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 190 (⟨.mul, [.id (n+168), .id (n+166)]⟩ : Def) pos.row_190
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 191 (⟨.umulh, [.id (n+168), .id (n+166)]⟩ : Def) pos.row_191
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 192 (⟨.add3, [.id (n+123), .id (n+190), .id (n+188)]⟩ : Def) pos.row_192
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 195 (⟨.carry3, [.id (n+123), .id (n+190), .id (n+188)]⟩ : Def) pos.row_195
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 197 (⟨.cond 2#4, [.id (n+193), .id (n+194), .id (n+195), .id (n+196)]⟩ : Def) pos.row_197
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 198 (⟨.add3, [.id (n+178), .id (n+170), .imm 0#64]⟩ : Def) pos.row_198
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 201 (⟨.carry3, [.id (n+178), .id (n+170), .imm 0#64]⟩ : Def) pos.row_201
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 203 (⟨.add3, [.id (n+185), .id (n+177), .id (n+201)]⟩ : Def) pos.row_203
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 206 (⟨.carry3, [.id (n+185), .id (n+177), .id (n+201)]⟩ : Def) pos.row_206
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 208 (⟨.add3, [.id (n+192), .id (n+184), .id (n+206)]⟩ : Def) pos.row_208
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 211 (⟨.carry3, [.id (n+192), .id (n+184), .id (n+206)]⟩ : Def) pos.row_211
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 213 (⟨.add3, [.id (n+197), .id (n+191), .id (n+211)]⟩ : Def) pos.row_213
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 214 (⟨.add, [.id (n+213), .imm 1#64]⟩ : Def) pos.row_214
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 215 (⟨.mul, [.id (n+168), .id (n+214)]⟩ : Def) pos.row_215
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 216 (⟨.umulh, [.id (n+168), .id (n+214)]⟩ : Def) pos.row_216
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 217 (⟨.add3, [.id (n+171), .id (n+215), .imm 0#64]⟩ : Def) pos.row_217
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 220 (⟨.carry3, [.id (n+171), .id (n+215), .imm 0#64]⟩ : Def) pos.row_220
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 222 (⟨.add3, [.id (n+198), .id (n+216), .id (n+220)]⟩ : Def) pos.row_222
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 225 (⟨.carry3, [.id (n+198), .id (n+216), .id (n+220)]⟩ : Def) pos.row_225
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 227 (⟨.add3, [.id (n+203), .imm 0#64, .id (n+225)]⟩ : Def) pos.row_227
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 230 (⟨.carry3, [.id (n+203), .imm 0#64, .id (n+225)]⟩ : Def) pos.row_230
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 232 (⟨.add3, [.id (n+208), .imm 0#64, .id (n+230)]⟩ : Def) pos.row_232
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 235 (⟨.carry3, [.id (n+208), .imm 0#64, .id (n+230)]⟩ : Def) pos.row_235
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 237 (⟨.cselc 3#4, [.id (n+233), .id (n+234), .id (n+235), .id (n+236), .id (n+168), .imm 0#64]⟩ : Def) pos.row_237
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 238 (⟨.sbc3, [.id (n+217), .id (n+237), .imm 1#64]⟩ : Def) pos.row_238
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 241 (⟨.sbc3C, [.id (n+217), .id (n+237), .imm 1#64]⟩ : Def) pos.row_241
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 243 (⟨.sbc3, [.id (n+222), .imm 0#64, .id (n+241)]⟩ : Def) pos.row_243
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 246 (⟨.sbc3C, [.id (n+222), .imm 0#64, .id (n+241)]⟩ : Def) pos.row_246
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 248 (⟨.sbc3, [.id (n+227), .imm 0#64, .id (n+246)]⟩ : Def) pos.row_248
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 251 (⟨.sbc3C, [.id (n+227), .imm 0#64, .id (n+246)]⟩ : Def) pos.row_251
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 253 (⟨.sbc3, [.id (n+232), .imm 0#64, .id (n+251)]⟩ : Def) pos.row_253
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))

theorem product_parts (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    coreMultiplyWord (v n) (loadedY v n) =
      ⟨⟨v (n+4),v (n+8),v (n+17),v (n+24)⟩,v (n+29)⟩ := by
  have d1 : Op.add3.eval [v (n+6),v (n+5),0#64] = v (n+8) :=
    (WordMulAdd.add_swap _ _ _).trans rows.row_8.symm
  have c1 : Op.carry3.eval [v (n+6),v (n+5),0#64] = v (n+11) :=
    (WordMulAdd.carry_swap _ _ _).trans rows.row_11.symm
  have d2 : Op.add3.eval [v (n+15),v (n+7),v (n+11)] = v (n+17) :=
    (WordMulAdd.add_swap _ _ _).trans rows.row_17.symm
  have c2 : Op.carry3.eval [v (n+15),v (n+7),v (n+11)] = v (n+20) :=
    (WordMulAdd.carry_swap _ _ _).trans rows.row_20.symm
  have d3 : Op.add3.eval [v (n+22),v (n+16),v (n+20)] = v (n+24) :=
    (WordMulAdd.add_swap _ _ _).trans rows.row_24.symm
  have c3 : Op.carry3.eval [v (n+22),v (n+16),v (n+20)] = v (n+27) :=
    (WordMulAdd.carry_swap _ _ _).trans rows.row_27.symm
  simp only [coreMultiplyWord, loadedY, ← rows.row_4, ← rows.row_5, ← rows.row_6, ← rows.row_7,
    ← rows.row_8, ← rows.row_11, ← rows.row_15, ← rows.row_16,
    ← rows.row_17, ← rows.row_20, ← rows.row_22, ← rows.row_23,
    ← rows.row_24, ← rows.row_27, ← rows.row_29, d1,c1,d2,c2,d3,c3]

theorem accumulate_1 (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    WordMulAdd.mulAdd4 ⟨v (n+8),v (n+17),v (n+24),v (n+29)⟩ (v (n+1)) (loadedY v n) =
      ⟨⟨v (n+33),v (n+59),v (n+65),v (n+71)⟩,v (n+76)⟩ := by
  have top : Op.add3.eval [v (n+56),v (n+54),v (n+74)] = v (n+76) := by
    rw [← WordMulAdd.add_top, ← rows.row_57, ← rows.row_76]
  simp only [WordMulAdd.mulAdd4, WordMulAdd.lowProducts, WordMulAdd.highProducts,
    Addition.coreChain4, loadedY, ← rows.row_32, ← rows.row_33, ← rows.row_36, ← rows.row_38,
    ← rows.row_39, ← rows.row_42, ← rows.row_44, ← rows.row_45,
    ← rows.row_48, ← rows.row_50, ← rows.row_51, ← rows.row_54,
    ← rows.row_56, ← rows.row_57, ← rows.row_58, ← rows.row_59,
    ← rows.row_62, ← rows.row_64, ← rows.row_65, ← rows.row_68,
    ← rows.row_70, ← rows.row_71, ← rows.row_74, ← rows.row_76, WordMulAdd.add_zero, WordMulAdd.carry_zero, top]

theorem accumulate_2 (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    WordMulAdd.mulAdd4 ⟨v (n+59),v (n+65),v (n+71),v (n+76)⟩ (v (n+30)) (loadedY v n) =
      ⟨⟨v (n+78),v (n+104),v (n+110),v (n+116)⟩,v (n+121)⟩ := by
  have top : Op.add3.eval [v (n+101),v (n+99),v (n+119)] = v (n+121) := by
    rw [← WordMulAdd.add_top, ← rows.row_102, ← rows.row_121]
  simp only [WordMulAdd.mulAdd4, WordMulAdd.lowProducts, WordMulAdd.highProducts,
    Addition.coreChain4, loadedY, ← rows.row_77, ← rows.row_78, ← rows.row_81, ← rows.row_83,
    ← rows.row_84, ← rows.row_87, ← rows.row_89, ← rows.row_90,
    ← rows.row_93, ← rows.row_95, ← rows.row_96, ← rows.row_99,
    ← rows.row_101, ← rows.row_102, ← rows.row_103, ← rows.row_104,
    ← rows.row_107, ← rows.row_109, ← rows.row_110, ← rows.row_113,
    ← rows.row_115, ← rows.row_116, ← rows.row_119, ← rows.row_121, WordMulAdd.add_zero, WordMulAdd.carry_zero, top]

theorem accumulate_3 (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    WordMulAdd.mulAdd4 ⟨v (n+104),v (n+110),v (n+116),v (n+121)⟩ (v (n+31)) (loadedY v n) =
      ⟨⟨v (n+123),v (n+149),v (n+155),v (n+161)⟩,v (n+166)⟩ := by
  have top : Op.add3.eval [v (n+146),v (n+144),v (n+164)] = v (n+166) := by
    rw [← WordMulAdd.add_top, ← rows.row_147, ← rows.row_166]
  simp only [WordMulAdd.mulAdd4, WordMulAdd.lowProducts, WordMulAdd.highProducts,
    Addition.coreChain4, loadedY, ← rows.row_122, ← rows.row_123, ← rows.row_126, ← rows.row_128,
    ← rows.row_129, ← rows.row_132, ← rows.row_134, ← rows.row_135,
    ← rows.row_138, ← rows.row_140, ← rows.row_141, ← rows.row_144,
    ← rows.row_146, ← rows.row_147, ← rows.row_148, ← rows.row_149,
    ← rows.row_152, ← rows.row_154, ← rows.row_155, ← rows.row_158,
    ← rows.row_160, ← rows.row_161, ← rows.row_164, ← rows.row_166, WordMulAdd.add_zero, WordMulAdd.carry_zero, top]

theorem materialized_constant (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    v (n+168) = BitVec.ofNat 64 correction := by
  rw [rows.row_168, rows.row_167]
  decide

theorem first_fold (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    WordMulAdd.mulAdd4 (productLow v n) (BitVec.ofNat 64 correction) (productHigh v n) =
      ⟨⟨v (n+171),v (n+198),v (n+203),v (n+208)⟩,v (n+213)⟩ := by
  have flagBound : (v (n+195)).toNat ≤ 1 := by
    rw [rows.row_195]; exact Addition.carry3_le_one ..
  have selected : v (n+197) = v (n+195) := by
    rw [rows.row_197]; exact WordMulAdd.condition_carry _ _ _ _ flagBound
  have top : Op.add3.eval [v (n+191),v (n+195),v (n+211)] = v (n+213) := by
    rw [rows.row_213, selected]
    exact WordMulAdd.add_swap _ _ _
  simp only [WordMulAdd.mulAdd4, WordMulAdd.lowProducts, WordMulAdd.highProducts,
    Addition.coreChain4, productLow, productHigh, ← materialized_constant v n rows,
    ← rows.row_169, ← rows.row_170, ← rows.row_171, ← rows.row_174,
    ← rows.row_176, ← rows.row_177, ← rows.row_178, ← rows.row_181,
    ← rows.row_183, ← rows.row_184, ← rows.row_185, ← rows.row_188,
    ← rows.row_190, ← rows.row_191, ← rows.row_192, ← rows.row_195,
    ← rows.row_197, ← rows.row_198, ← rows.row_201, ← rows.row_203,
    ← rows.row_206, ← rows.row_208, ← rows.row_211, ← rows.row_213, WordMulAdd.add_zero, WordMulAdd.carry_zero, top]

theorem quotient_fold (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    WideWordReduce.foldedChain ⟨⟨v (n+171),v (n+198),v (n+203),v (n+208)⟩,v (n+213)⟩ =
      (⟨v (n+217),v (n+222),v (n+227),v (n+232)⟩,v (n+235)) := by
  have p0 : Op.mul.eval [v (n+214),v (n+168)] = v (n+215) :=
    (WordMulAdd.mul_swap _ _).trans rows.row_215.symm
  have p1 : Op.umulh.eval [v (n+214),v (n+168)] = v (n+216) :=
    (WordMulAdd.umulh_swap _ _).trans rows.row_216.symm
  simp only [WideWordReduce.foldedChain, CoreConstantMultiply.quotientWord,
    CoreConstantMultiply.correctionProduct, Addition.coreChain4,
    ← materialized_constant v n rows, ← rows.row_214, ← rows.row_215, ← rows.row_216, ← rows.row_217,
    ← rows.row_220, ← rows.row_222, ← rows.row_225, ← rows.row_227,
    ← rows.row_230, ← rows.row_232, ← rows.row_235, p0,p1]

theorem selected_value (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    v (n+237) = if v (n+235) == 0#64 then BitVec.ofNat 64 correction else 0#64 := by
  rw [rows.row_237, materialized_constant v n rows]
  exact SubSSA.select_correction _ _ _ _

theorem rows_reduceProduct (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    resultWords v n = WideWordReduce.reduceProduct (productLow v n) (productHigh v n) := by
  unfold WideWordReduce.reduceProduct
  rw [first_fold v n rows]
  unfold WideWordReduce.reduce4
  rw [quotient_fold v n rows]
  simp only [SecpMath.coreChain4, correctionWords, ← selected_value v n rows,
    ← rows.row_238, ← rows.row_241, ← rows.row_243, ← rows.row_246,
    ← rows.row_248, ← rows.row_251, ← rows.row_253, resultWords]

theorem product_balance (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    (productLow v n).value + radix*(productHigh v n).value =
      (loadedX v n).value * (loadedY v n).value := by
  have first := Product.coreMultiplyWord_correct (v n) (loadedY v n)
  rw [product_parts v n rows] at first
  have one := WordMulAdd.mulAdd4_correct ⟨v (n+8),v (n+17),v (n+24),v (n+29)⟩ (v (n+1)) (loadedY v n)
  rw [accumulate_1 v n rows] at one
  have two := WordMulAdd.mulAdd4_correct ⟨v (n+59),v (n+65),v (n+71),v (n+76)⟩ (v (n+30)) (loadedY v n)
  rw [accumulate_2 v n rows] at two
  have three := WordMulAdd.mulAdd4_correct ⟨v (n+104),v (n+110),v (n+116),v (n+121)⟩ (v (n+31)) (loadedY v n)
  rw [accumulate_3 v n rows] at three
  have expanded : (loadedX v n).value * (loadedY v n).value =
      (v n).toNat*(loadedY v n).value + limbRadix*((v (n+1)).toNat*(loadedY v n).value) +
      limbRadix^2*((v (n+30)).toNat*(loadedY v n).value) +
      limbRadix^3*((v (n+31)).toNat*(loadedY v n).value) := by
    simp only [loadedX, LimbWords.value, pack4, Nat.add_mul, Nat.mul_assoc]
  rw [expanded]
  simp only [productLow, productHigh, WideWords.value, LimbWords.value, pack4, radix, limbRadix] at *
  omega

theorem table_correct (inputs : List (BitVec 64)) (defs : List Def) (n xs ys : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n) (loads : LoadPositions defs xs ys)
    (xInside : xs+32 ≤ n) (yInside : ys+32 ≤ n) :
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value < modulus ∧
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value =
      ((inputLimbs inputs xs).value*(inputLimbs inputs ys).value)%modulus := by
  have equations := equations_of_positions inputs defs n lengthEq pos
  have loaded := loaded_inputs inputs defs n xs ys lengthEq loads xInside yInside
  rw [rows_reduceProduct _ n equations]
  have result := WideWordReduce.reduceProduct_correct
    (productLow (fun i => (evalDefs inputs defs).getD i 0) n)
    (productHigh (fun i => (evalDefs inputs defs).getD i 0) n)
  rw [product_balance _ n equations, loaded.1, loaded.2] at result
  exact result

#print axioms equations_of_positions
#print axioms product_balance
#print axioms rows_reduceProduct
#print axioms table_correct
end SecpMath.MulAltSSA
