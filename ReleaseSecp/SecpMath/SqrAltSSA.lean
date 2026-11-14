import SecpMath.SquareWord
import SecpMath.WideWordReduce
import SecpMath.SubSSA
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
namespace SecpMath.SqrAltSSA
open ArmCertValue SecpMath.Addition SecpMath.Product
open SecpMath.SubSSA (inputWordDef inputLimbs loaded_input_word)

def loadedX (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v n, v (n+1), v (n+4), v (n+5)⟩
def productLow (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+81), v (n+82), v (n+88), v (n+94)⟩
def productHigh (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+100), v (n+106), v (n+112), v (n+118)⟩
def resultWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+190), v (n+195), v (n+200), v (n+205)⟩

structure LoadPositions (defs : List Def) (xs : Nat) : Prop where
  x0 : defs[0]? = some (inputWordDef xs)
  x1 : defs[1]? = some (inputWordDef (xs+8))
  x2 : defs[4]? = some (inputWordDef (xs+16))
  x3 : defs[5]? = some (inputWordDef (xs+24))

theorem loaded_inputs (inputs : List (BitVec 64)) (defs : List Def) (n xs : Nat)
    (lengthEq : inputs.length = n) (pos : LoadPositions defs xs) (inside : xs+32 ≤ n) :
    loadedX (fun i => (evalDefs inputs defs).getD i 0) n = inputLimbs inputs xs := by
  subst n
  have first := loaded_input_word inputs defs 0 xs pos.x0 (by omega)
  simp only [Nat.add_zero] at first
  simp only [loadedX, inputLimbs, first,
    loaded_input_word inputs defs 1 (xs+8) pos.x1 (by omega),
    loaded_input_word inputs defs 4 (xs+16) pos.x2 (by omega),
    loaded_input_word inputs defs 5 (xs+24) pos.x3 (by omega)]

private theorem const_eval (values : List (BitVec 64)) (c : BitVec 64) :
    Def.eval values ⟨.const c, []⟩ = c := rfl

structure Equations (v : Nat → BitVec 64) (n : Nat) : Prop where
  row_2 : v (n+2) = (Op.mul).eval [v n, v (n+1)]
  row_3 : v (n+3) = (Op.umulh).eval [v n, v (n+1)]
  row_6 : v (n+6) = (Op.mul).eval [v n, v (n+5)]
  row_7 : v (n+7) = (Op.umulh).eval [v n, v (n+5)]
  row_8 : v (n+8) = (Op.mul).eval [v n, v (n+4)]
  row_9 : v (n+9) = (Op.umulh).eval [v n, v (n+4)]
  row_10 : v (n+10) = (Op.add3).eval [v (n+3), v (n+8), 0#64]
  row_13 : v (n+13) = (Op.carry3).eval [v (n+3), v (n+8), 0#64]
  row_15 : v (n+15) = (Op.add3).eval [v (n+6), v (n+9), v (n+13)]
  row_18 : v (n+18) = (Op.carry3).eval [v (n+6), v (n+9), v (n+13)]
  row_20 : v (n+20) = (Op.mul).eval [v (n+1), v (n+4)]
  row_21 : v (n+21) = (Op.umulh).eval [v (n+1), v (n+4)]
  row_22 : v (n+22) = (Op.add3).eval [v (n+21), 0#64, v (n+18)]
  row_23 : v (n+23) = (Op.add3).eval [v (n+15), v (n+20), 0#64]
  row_26 : v (n+26) = (Op.carry3).eval [v (n+15), v (n+20), 0#64]
  row_28 : v (n+28) = (Op.mul).eval [v (n+4), v (n+5)]
  row_29 : v (n+29) = (Op.umulh).eval [v (n+4), v (n+5)]
  row_30 : v (n+30) = (Op.add3).eval [v (n+7), v (n+22), v (n+26)]
  row_33 : v (n+33) = (Op.carry3).eval [v (n+7), v (n+22), v (n+26)]
  row_35 : v (n+35) = (Op.mul).eval [v (n+1), v (n+5)]
  row_36 : v (n+36) = (Op.umulh).eval [v (n+1), v (n+5)]
  row_37 : v (n+37) = (Op.add3).eval [v (n+36), 0#64, v (n+33)]
  row_38 : v (n+38) = (Op.add3).eval [v (n+30), v (n+35), 0#64]
  row_41 : v (n+41) = (Op.carry3).eval [v (n+30), v (n+35), 0#64]
  row_43 : v (n+43) = (Op.add3).eval [v (n+28), v (n+37), v (n+41)]
  row_46 : v (n+46) = (Op.carry3).eval [v (n+28), v (n+37), v (n+41)]
  row_48 : v (n+48) = (Op.add3).eval [v (n+29), 0#64, v (n+46)]
  row_49 : v (n+49) = (Op.add3).eval [v (n+2), v (n+2), 0#64]
  row_52 : v (n+52) = (Op.carry3).eval [v (n+2), v (n+2), 0#64]
  row_54 : v (n+54) = (Op.add3).eval [v (n+10), v (n+10), v (n+52)]
  row_57 : v (n+57) = (Op.carry3).eval [v (n+10), v (n+10), v (n+52)]
  row_59 : v (n+59) = (Op.add3).eval [v (n+23), v (n+23), v (n+57)]
  row_62 : v (n+62) = (Op.carry3).eval [v (n+23), v (n+23), v (n+57)]
  row_64 : v (n+64) = (Op.add3).eval [v (n+38), v (n+38), v (n+62)]
  row_67 : v (n+67) = (Op.carry3).eval [v (n+38), v (n+38), v (n+62)]
  row_69 : v (n+69) = (Op.add3).eval [v (n+43), v (n+43), v (n+67)]
  row_72 : v (n+72) = (Op.carry3).eval [v (n+43), v (n+43), v (n+67)]
  row_74 : v (n+74) = (Op.add3).eval [v (n+48), v (n+48), v (n+72)]
  row_77 : v (n+77) = (Op.carry3).eval [v (n+48), v (n+48), v (n+72)]
  row_79 : v (n+79) = (Op.cond 2#4).eval [v (n+75), v (n+76), v (n+77), v (n+78)]
  row_80 : v (n+80) = (Op.umulh).eval [v n, v n]
  row_81 : v (n+81) = (Op.mul).eval [v n, v n]
  row_82 : v (n+82) = (Op.add3).eval [v (n+49), v (n+80), 0#64]
  row_85 : v (n+85) = (Op.carry3).eval [v (n+49), v (n+80), 0#64]
  row_87 : v (n+87) = (Op.mul).eval [v (n+1), v (n+1)]
  row_88 : v (n+88) = (Op.add3).eval [v (n+54), v (n+87), v (n+85)]
  row_91 : v (n+91) = (Op.carry3).eval [v (n+54), v (n+87), v (n+85)]
  row_93 : v (n+93) = (Op.umulh).eval [v (n+1), v (n+1)]
  row_94 : v (n+94) = (Op.add3).eval [v (n+59), v (n+93), v (n+91)]
  row_97 : v (n+97) = (Op.carry3).eval [v (n+59), v (n+93), v (n+91)]
  row_99 : v (n+99) = (Op.mul).eval [v (n+4), v (n+4)]
  row_100 : v (n+100) = (Op.add3).eval [v (n+64), v (n+99), v (n+97)]
  row_103 : v (n+103) = (Op.carry3).eval [v (n+64), v (n+99), v (n+97)]
  row_105 : v (n+105) = (Op.umulh).eval [v (n+4), v (n+4)]
  row_106 : v (n+106) = (Op.add3).eval [v (n+69), v (n+105), v (n+103)]
  row_109 : v (n+109) = (Op.carry3).eval [v (n+69), v (n+105), v (n+103)]
  row_111 : v (n+111) = (Op.mul).eval [v (n+5), v (n+5)]
  row_112 : v (n+112) = (Op.add3).eval [v (n+74), v (n+111), v (n+109)]
  row_115 : v (n+115) = (Op.carry3).eval [v (n+74), v (n+111), v (n+109)]
  row_117 : v (n+117) = (Op.umulh).eval [v (n+5), v (n+5)]
  row_118 : v (n+118) = (Op.add3).eval [v (n+79), v (n+117), v (n+115)]
  row_119 : v (n+119) = 977#64
  row_120 : v (n+120) = (Op.orr).eval [v (n+119), 4294967296#64]
  row_121 : v (n+121) = (Op.mul).eval [v (n+120), v (n+100)]
  row_122 : v (n+122) = (Op.umulh).eval [v (n+120), v (n+100)]
  row_123 : v (n+123) = (Op.add3).eval [v (n+81), v (n+121), 0#64]
  row_126 : v (n+126) = (Op.carry3).eval [v (n+81), v (n+121), 0#64]
  row_128 : v (n+128) = (Op.mul).eval [v (n+120), v (n+106)]
  row_129 : v (n+129) = (Op.umulh).eval [v (n+120), v (n+106)]
  row_130 : v (n+130) = (Op.add3).eval [v (n+82), v (n+128), v (n+126)]
  row_133 : v (n+133) = (Op.carry3).eval [v (n+82), v (n+128), v (n+126)]
  row_135 : v (n+135) = (Op.mul).eval [v (n+120), v (n+112)]
  row_136 : v (n+136) = (Op.umulh).eval [v (n+120), v (n+112)]
  row_137 : v (n+137) = (Op.add3).eval [v (n+88), v (n+135), v (n+133)]
  row_140 : v (n+140) = (Op.carry3).eval [v (n+88), v (n+135), v (n+133)]
  row_142 : v (n+142) = (Op.mul).eval [v (n+120), v (n+118)]
  row_143 : v (n+143) = (Op.umulh).eval [v (n+120), v (n+118)]
  row_144 : v (n+144) = (Op.add3).eval [v (n+94), v (n+142), v (n+140)]
  row_147 : v (n+147) = (Op.carry3).eval [v (n+94), v (n+142), v (n+140)]
  row_149 : v (n+149) = (Op.cond 2#4).eval [v (n+145), v (n+146), v (n+147), v (n+148)]
  row_150 : v (n+150) = (Op.add3).eval [v (n+130), v (n+122), 0#64]
  row_153 : v (n+153) = (Op.carry3).eval [v (n+130), v (n+122), 0#64]
  row_155 : v (n+155) = (Op.add3).eval [v (n+137), v (n+129), v (n+153)]
  row_158 : v (n+158) = (Op.carry3).eval [v (n+137), v (n+129), v (n+153)]
  row_160 : v (n+160) = (Op.add3).eval [v (n+144), v (n+136), v (n+158)]
  row_163 : v (n+163) = (Op.carry3).eval [v (n+144), v (n+136), v (n+158)]
  row_165 : v (n+165) = (Op.add3).eval [v (n+149), v (n+143), v (n+163)]
  row_166 : v (n+166) = (Op.add).eval [v (n+165), 1#64]
  row_167 : v (n+167) = (Op.mul).eval [v (n+120), v (n+166)]
  row_168 : v (n+168) = (Op.umulh).eval [v (n+120), v (n+166)]
  row_169 : v (n+169) = (Op.add3).eval [v (n+123), v (n+167), 0#64]
  row_172 : v (n+172) = (Op.carry3).eval [v (n+123), v (n+167), 0#64]
  row_174 : v (n+174) = (Op.add3).eval [v (n+150), v (n+168), v (n+172)]
  row_177 : v (n+177) = (Op.carry3).eval [v (n+150), v (n+168), v (n+172)]
  row_179 : v (n+179) = (Op.add3).eval [v (n+155), 0#64, v (n+177)]
  row_182 : v (n+182) = (Op.carry3).eval [v (n+155), 0#64, v (n+177)]
  row_184 : v (n+184) = (Op.add3).eval [v (n+160), 0#64, v (n+182)]
  row_187 : v (n+187) = (Op.carry3).eval [v (n+160), 0#64, v (n+182)]
  row_189 : v (n+189) = (Op.cselc 3#4).eval [v (n+185), v (n+186), v (n+187), v (n+188), v (n+120), 0#64]
  row_190 : v (n+190) = (Op.sbc3).eval [v (n+169), v (n+189), 1#64]
  row_193 : v (n+193) = (Op.sbc3C).eval [v (n+169), v (n+189), 1#64]
  row_195 : v (n+195) = (Op.sbc3).eval [v (n+174), 0#64, v (n+193)]
  row_198 : v (n+198) = (Op.sbc3C).eval [v (n+174), 0#64, v (n+193)]
  row_200 : v (n+200) = (Op.sbc3).eval [v (n+179), 0#64, v (n+198)]
  row_203 : v (n+203) = (Op.sbc3C).eval [v (n+179), 0#64, v (n+198)]
  row_205 : v (n+205) = (Op.sbc3).eval [v (n+184), 0#64, v (n+203)]

structure RowPositions (defs : List Def) (n : Nat) : Prop where
  row_2 : defs[2]? = some (⟨.mul, [.id n, .id (n+1)]⟩ : Def)
  row_3 : defs[3]? = some (⟨.umulh, [.id n, .id (n+1)]⟩ : Def)
  row_6 : defs[6]? = some (⟨.mul, [.id n, .id (n+5)]⟩ : Def)
  row_7 : defs[7]? = some (⟨.umulh, [.id n, .id (n+5)]⟩ : Def)
  row_8 : defs[8]? = some (⟨.mul, [.id n, .id (n+4)]⟩ : Def)
  row_9 : defs[9]? = some (⟨.umulh, [.id n, .id (n+4)]⟩ : Def)
  row_10 : defs[10]? = some (⟨.add3, [.id (n+3), .id (n+8), .imm 0#64]⟩ : Def)
  row_13 : defs[13]? = some (⟨.carry3, [.id (n+3), .id (n+8), .imm 0#64]⟩ : Def)
  row_15 : defs[15]? = some (⟨.add3, [.id (n+6), .id (n+9), .id (n+13)]⟩ : Def)
  row_18 : defs[18]? = some (⟨.carry3, [.id (n+6), .id (n+9), .id (n+13)]⟩ : Def)
  row_20 : defs[20]? = some (⟨.mul, [.id (n+1), .id (n+4)]⟩ : Def)
  row_21 : defs[21]? = some (⟨.umulh, [.id (n+1), .id (n+4)]⟩ : Def)
  row_22 : defs[22]? = some (⟨.add3, [.id (n+21), .imm 0#64, .id (n+18)]⟩ : Def)
  row_23 : defs[23]? = some (⟨.add3, [.id (n+15), .id (n+20), .imm 0#64]⟩ : Def)
  row_26 : defs[26]? = some (⟨.carry3, [.id (n+15), .id (n+20), .imm 0#64]⟩ : Def)
  row_28 : defs[28]? = some (⟨.mul, [.id (n+4), .id (n+5)]⟩ : Def)
  row_29 : defs[29]? = some (⟨.umulh, [.id (n+4), .id (n+5)]⟩ : Def)
  row_30 : defs[30]? = some (⟨.add3, [.id (n+7), .id (n+22), .id (n+26)]⟩ : Def)
  row_33 : defs[33]? = some (⟨.carry3, [.id (n+7), .id (n+22), .id (n+26)]⟩ : Def)
  row_35 : defs[35]? = some (⟨.mul, [.id (n+1), .id (n+5)]⟩ : Def)
  row_36 : defs[36]? = some (⟨.umulh, [.id (n+1), .id (n+5)]⟩ : Def)
  row_37 : defs[37]? = some (⟨.add3, [.id (n+36), .imm 0#64, .id (n+33)]⟩ : Def)
  row_38 : defs[38]? = some (⟨.add3, [.id (n+30), .id (n+35), .imm 0#64]⟩ : Def)
  row_41 : defs[41]? = some (⟨.carry3, [.id (n+30), .id (n+35), .imm 0#64]⟩ : Def)
  row_43 : defs[43]? = some (⟨.add3, [.id (n+28), .id (n+37), .id (n+41)]⟩ : Def)
  row_46 : defs[46]? = some (⟨.carry3, [.id (n+28), .id (n+37), .id (n+41)]⟩ : Def)
  row_48 : defs[48]? = some (⟨.add3, [.id (n+29), .imm 0#64, .id (n+46)]⟩ : Def)
  row_49 : defs[49]? = some (⟨.add3, [.id (n+2), .id (n+2), .imm 0#64]⟩ : Def)
  row_52 : defs[52]? = some (⟨.carry3, [.id (n+2), .id (n+2), .imm 0#64]⟩ : Def)
  row_54 : defs[54]? = some (⟨.add3, [.id (n+10), .id (n+10), .id (n+52)]⟩ : Def)
  row_57 : defs[57]? = some (⟨.carry3, [.id (n+10), .id (n+10), .id (n+52)]⟩ : Def)
  row_59 : defs[59]? = some (⟨.add3, [.id (n+23), .id (n+23), .id (n+57)]⟩ : Def)
  row_62 : defs[62]? = some (⟨.carry3, [.id (n+23), .id (n+23), .id (n+57)]⟩ : Def)
  row_64 : defs[64]? = some (⟨.add3, [.id (n+38), .id (n+38), .id (n+62)]⟩ : Def)
  row_67 : defs[67]? = some (⟨.carry3, [.id (n+38), .id (n+38), .id (n+62)]⟩ : Def)
  row_69 : defs[69]? = some (⟨.add3, [.id (n+43), .id (n+43), .id (n+67)]⟩ : Def)
  row_72 : defs[72]? = some (⟨.carry3, [.id (n+43), .id (n+43), .id (n+67)]⟩ : Def)
  row_74 : defs[74]? = some (⟨.add3, [.id (n+48), .id (n+48), .id (n+72)]⟩ : Def)
  row_77 : defs[77]? = some (⟨.carry3, [.id (n+48), .id (n+48), .id (n+72)]⟩ : Def)
  row_79 : defs[79]? = some (⟨.cond 2#4, [.id (n+75), .id (n+76), .id (n+77), .id (n+78)]⟩ : Def)
  row_80 : defs[80]? = some (⟨.umulh, [.id n, .id n]⟩ : Def)
  row_81 : defs[81]? = some (⟨.mul, [.id n, .id n]⟩ : Def)
  row_82 : defs[82]? = some (⟨.add3, [.id (n+49), .id (n+80), .imm 0#64]⟩ : Def)
  row_85 : defs[85]? = some (⟨.carry3, [.id (n+49), .id (n+80), .imm 0#64]⟩ : Def)
  row_87 : defs[87]? = some (⟨.mul, [.id (n+1), .id (n+1)]⟩ : Def)
  row_88 : defs[88]? = some (⟨.add3, [.id (n+54), .id (n+87), .id (n+85)]⟩ : Def)
  row_91 : defs[91]? = some (⟨.carry3, [.id (n+54), .id (n+87), .id (n+85)]⟩ : Def)
  row_93 : defs[93]? = some (⟨.umulh, [.id (n+1), .id (n+1)]⟩ : Def)
  row_94 : defs[94]? = some (⟨.add3, [.id (n+59), .id (n+93), .id (n+91)]⟩ : Def)
  row_97 : defs[97]? = some (⟨.carry3, [.id (n+59), .id (n+93), .id (n+91)]⟩ : Def)
  row_99 : defs[99]? = some (⟨.mul, [.id (n+4), .id (n+4)]⟩ : Def)
  row_100 : defs[100]? = some (⟨.add3, [.id (n+64), .id (n+99), .id (n+97)]⟩ : Def)
  row_103 : defs[103]? = some (⟨.carry3, [.id (n+64), .id (n+99), .id (n+97)]⟩ : Def)
  row_105 : defs[105]? = some (⟨.umulh, [.id (n+4), .id (n+4)]⟩ : Def)
  row_106 : defs[106]? = some (⟨.add3, [.id (n+69), .id (n+105), .id (n+103)]⟩ : Def)
  row_109 : defs[109]? = some (⟨.carry3, [.id (n+69), .id (n+105), .id (n+103)]⟩ : Def)
  row_111 : defs[111]? = some (⟨.mul, [.id (n+5), .id (n+5)]⟩ : Def)
  row_112 : defs[112]? = some (⟨.add3, [.id (n+74), .id (n+111), .id (n+109)]⟩ : Def)
  row_115 : defs[115]? = some (⟨.carry3, [.id (n+74), .id (n+111), .id (n+109)]⟩ : Def)
  row_117 : defs[117]? = some (⟨.umulh, [.id (n+5), .id (n+5)]⟩ : Def)
  row_118 : defs[118]? = some (⟨.add3, [.id (n+79), .id (n+117), .id (n+115)]⟩ : Def)
  row_119 : defs[119]? = some (⟨.const 977#64, []⟩ : Def)
  row_120 : defs[120]? = some (⟨.orr, [.id (n+119), .imm 4294967296#64]⟩ : Def)
  row_121 : defs[121]? = some (⟨.mul, [.id (n+120), .id (n+100)]⟩ : Def)
  row_122 : defs[122]? = some (⟨.umulh, [.id (n+120), .id (n+100)]⟩ : Def)
  row_123 : defs[123]? = some (⟨.add3, [.id (n+81), .id (n+121), .imm 0#64]⟩ : Def)
  row_126 : defs[126]? = some (⟨.carry3, [.id (n+81), .id (n+121), .imm 0#64]⟩ : Def)
  row_128 : defs[128]? = some (⟨.mul, [.id (n+120), .id (n+106)]⟩ : Def)
  row_129 : defs[129]? = some (⟨.umulh, [.id (n+120), .id (n+106)]⟩ : Def)
  row_130 : defs[130]? = some (⟨.add3, [.id (n+82), .id (n+128), .id (n+126)]⟩ : Def)
  row_133 : defs[133]? = some (⟨.carry3, [.id (n+82), .id (n+128), .id (n+126)]⟩ : Def)
  row_135 : defs[135]? = some (⟨.mul, [.id (n+120), .id (n+112)]⟩ : Def)
  row_136 : defs[136]? = some (⟨.umulh, [.id (n+120), .id (n+112)]⟩ : Def)
  row_137 : defs[137]? = some (⟨.add3, [.id (n+88), .id (n+135), .id (n+133)]⟩ : Def)
  row_140 : defs[140]? = some (⟨.carry3, [.id (n+88), .id (n+135), .id (n+133)]⟩ : Def)
  row_142 : defs[142]? = some (⟨.mul, [.id (n+120), .id (n+118)]⟩ : Def)
  row_143 : defs[143]? = some (⟨.umulh, [.id (n+120), .id (n+118)]⟩ : Def)
  row_144 : defs[144]? = some (⟨.add3, [.id (n+94), .id (n+142), .id (n+140)]⟩ : Def)
  row_147 : defs[147]? = some (⟨.carry3, [.id (n+94), .id (n+142), .id (n+140)]⟩ : Def)
  row_149 : defs[149]? = some (⟨.cond 2#4, [.id (n+145), .id (n+146), .id (n+147), .id (n+148)]⟩ : Def)
  row_150 : defs[150]? = some (⟨.add3, [.id (n+130), .id (n+122), .imm 0#64]⟩ : Def)
  row_153 : defs[153]? = some (⟨.carry3, [.id (n+130), .id (n+122), .imm 0#64]⟩ : Def)
  row_155 : defs[155]? = some (⟨.add3, [.id (n+137), .id (n+129), .id (n+153)]⟩ : Def)
  row_158 : defs[158]? = some (⟨.carry3, [.id (n+137), .id (n+129), .id (n+153)]⟩ : Def)
  row_160 : defs[160]? = some (⟨.add3, [.id (n+144), .id (n+136), .id (n+158)]⟩ : Def)
  row_163 : defs[163]? = some (⟨.carry3, [.id (n+144), .id (n+136), .id (n+158)]⟩ : Def)
  row_165 : defs[165]? = some (⟨.add3, [.id (n+149), .id (n+143), .id (n+163)]⟩ : Def)
  row_166 : defs[166]? = some (⟨.add, [.id (n+165), .imm 1#64]⟩ : Def)
  row_167 : defs[167]? = some (⟨.mul, [.id (n+120), .id (n+166)]⟩ : Def)
  row_168 : defs[168]? = some (⟨.umulh, [.id (n+120), .id (n+166)]⟩ : Def)
  row_169 : defs[169]? = some (⟨.add3, [.id (n+123), .id (n+167), .imm 0#64]⟩ : Def)
  row_172 : defs[172]? = some (⟨.carry3, [.id (n+123), .id (n+167), .imm 0#64]⟩ : Def)
  row_174 : defs[174]? = some (⟨.add3, [.id (n+150), .id (n+168), .id (n+172)]⟩ : Def)
  row_177 : defs[177]? = some (⟨.carry3, [.id (n+150), .id (n+168), .id (n+172)]⟩ : Def)
  row_179 : defs[179]? = some (⟨.add3, [.id (n+155), .imm 0#64, .id (n+177)]⟩ : Def)
  row_182 : defs[182]? = some (⟨.carry3, [.id (n+155), .imm 0#64, .id (n+177)]⟩ : Def)
  row_184 : defs[184]? = some (⟨.add3, [.id (n+160), .imm 0#64, .id (n+182)]⟩ : Def)
  row_187 : defs[187]? = some (⟨.carry3, [.id (n+160), .imm 0#64, .id (n+182)]⟩ : Def)
  row_189 : defs[189]? = some (⟨.cselc 3#4, [.id (n+185), .id (n+186), .id (n+187), .id (n+188), .id (n+120), .imm 0#64]⟩ : Def)
  row_190 : defs[190]? = some (⟨.sbc3, [.id (n+169), .id (n+189), .imm 1#64]⟩ : Def)
  row_193 : defs[193]? = some (⟨.sbc3C, [.id (n+169), .id (n+189), .imm 1#64]⟩ : Def)
  row_195 : defs[195]? = some (⟨.sbc3, [.id (n+174), .imm 0#64, .id (n+193)]⟩ : Def)
  row_198 : defs[198]? = some (⟨.sbc3C, [.id (n+174), .imm 0#64, .id (n+193)]⟩ : Def)
  row_200 : defs[200]? = some (⟨.sbc3, [.id (n+179), .imm 0#64, .id (n+198)]⟩ : Def)
  row_203 : defs[203]? = some (⟨.sbc3C, [.id (n+179), .imm 0#64, .id (n+198)]⟩ : Def)
  row_205 : defs[205]? = some (⟨.sbc3, [.id (n+184), .imm 0#64, .id (n+203)]⟩ : Def)

def compilerRows (n xs : Nat) : List Def := [
  inputWordDef (xs),
  inputWordDef (xs+8),
  (⟨.mul, [.id n, .id (n+1)]⟩ : Def),
  (⟨.umulh, [.id n, .id (n+1)]⟩ : Def),
  inputWordDef (xs+16),
  inputWordDef (xs+24),
  (⟨.mul, [.id n, .id (n+5)]⟩ : Def),
  (⟨.umulh, [.id n, .id (n+5)]⟩ : Def),
  (⟨.mul, [.id n, .id (n+4)]⟩ : Def),
  (⟨.umulh, [.id n, .id (n+4)]⟩ : Def),
  (⟨.add3, [.id (n+3), .id (n+8), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+3), .id (n+8), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+3), .id (n+8), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+3), .id (n+8), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+3), .id (n+8), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+6), .id (n+9), .id (n+13)]⟩ : Def),
  (⟨.add3N, [.id (n+6), .id (n+9), .id (n+13)]⟩ : Def),
  (⟨.add3Z, [.id (n+6), .id (n+9), .id (n+13)]⟩ : Def),
  (⟨.carry3, [.id (n+6), .id (n+9), .id (n+13)]⟩ : Def),
  (⟨.ovf3, [.id (n+6), .id (n+9), .id (n+13)]⟩ : Def),
  (⟨.mul, [.id (n+1), .id (n+4)]⟩ : Def),
  (⟨.umulh, [.id (n+1), .id (n+4)]⟩ : Def),
  (⟨.add3, [.id (n+21), .imm 0#64, .id (n+18)]⟩ : Def),
  (⟨.add3, [.id (n+15), .id (n+20), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+15), .id (n+20), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+15), .id (n+20), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+15), .id (n+20), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+15), .id (n+20), .imm 0#64]⟩ : Def),
  (⟨.mul, [.id (n+4), .id (n+5)]⟩ : Def),
  (⟨.umulh, [.id (n+4), .id (n+5)]⟩ : Def),
  (⟨.add3, [.id (n+7), .id (n+22), .id (n+26)]⟩ : Def),
  (⟨.add3N, [.id (n+7), .id (n+22), .id (n+26)]⟩ : Def),
  (⟨.add3Z, [.id (n+7), .id (n+22), .id (n+26)]⟩ : Def),
  (⟨.carry3, [.id (n+7), .id (n+22), .id (n+26)]⟩ : Def),
  (⟨.ovf3, [.id (n+7), .id (n+22), .id (n+26)]⟩ : Def),
  (⟨.mul, [.id (n+1), .id (n+5)]⟩ : Def),
  (⟨.umulh, [.id (n+1), .id (n+5)]⟩ : Def),
  (⟨.add3, [.id (n+36), .imm 0#64, .id (n+33)]⟩ : Def),
  (⟨.add3, [.id (n+30), .id (n+35), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+30), .id (n+35), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+30), .id (n+35), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+30), .id (n+35), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+30), .id (n+35), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+28), .id (n+37), .id (n+41)]⟩ : Def),
  (⟨.add3N, [.id (n+28), .id (n+37), .id (n+41)]⟩ : Def),
  (⟨.add3Z, [.id (n+28), .id (n+37), .id (n+41)]⟩ : Def),
  (⟨.carry3, [.id (n+28), .id (n+37), .id (n+41)]⟩ : Def),
  (⟨.ovf3, [.id (n+28), .id (n+37), .id (n+41)]⟩ : Def),
  (⟨.add3, [.id (n+29), .imm 0#64, .id (n+46)]⟩ : Def),
  (⟨.add3, [.id (n+2), .id (n+2), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+2), .id (n+2), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+2), .id (n+2), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+2), .id (n+2), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+2), .id (n+2), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+10), .id (n+10), .id (n+52)]⟩ : Def),
  (⟨.add3N, [.id (n+10), .id (n+10), .id (n+52)]⟩ : Def),
  (⟨.add3Z, [.id (n+10), .id (n+10), .id (n+52)]⟩ : Def),
  (⟨.carry3, [.id (n+10), .id (n+10), .id (n+52)]⟩ : Def),
  (⟨.ovf3, [.id (n+10), .id (n+10), .id (n+52)]⟩ : Def),
  (⟨.add3, [.id (n+23), .id (n+23), .id (n+57)]⟩ : Def),
  (⟨.add3N, [.id (n+23), .id (n+23), .id (n+57)]⟩ : Def),
  (⟨.add3Z, [.id (n+23), .id (n+23), .id (n+57)]⟩ : Def),
  (⟨.carry3, [.id (n+23), .id (n+23), .id (n+57)]⟩ : Def),
  (⟨.ovf3, [.id (n+23), .id (n+23), .id (n+57)]⟩ : Def),
  (⟨.add3, [.id (n+38), .id (n+38), .id (n+62)]⟩ : Def),
  (⟨.add3N, [.id (n+38), .id (n+38), .id (n+62)]⟩ : Def),
  (⟨.add3Z, [.id (n+38), .id (n+38), .id (n+62)]⟩ : Def),
  (⟨.carry3, [.id (n+38), .id (n+38), .id (n+62)]⟩ : Def),
  (⟨.ovf3, [.id (n+38), .id (n+38), .id (n+62)]⟩ : Def),
  (⟨.add3, [.id (n+43), .id (n+43), .id (n+67)]⟩ : Def),
  (⟨.add3N, [.id (n+43), .id (n+43), .id (n+67)]⟩ : Def),
  (⟨.add3Z, [.id (n+43), .id (n+43), .id (n+67)]⟩ : Def),
  (⟨.carry3, [.id (n+43), .id (n+43), .id (n+67)]⟩ : Def),
  (⟨.ovf3, [.id (n+43), .id (n+43), .id (n+67)]⟩ : Def),
  (⟨.add3, [.id (n+48), .id (n+48), .id (n+72)]⟩ : Def),
  (⟨.add3N, [.id (n+48), .id (n+48), .id (n+72)]⟩ : Def),
  (⟨.add3Z, [.id (n+48), .id (n+48), .id (n+72)]⟩ : Def),
  (⟨.carry3, [.id (n+48), .id (n+48), .id (n+72)]⟩ : Def),
  (⟨.ovf3, [.id (n+48), .id (n+48), .id (n+72)]⟩ : Def),
  (⟨.cond 2#4, [.id (n+75), .id (n+76), .id (n+77), .id (n+78)]⟩ : Def),
  (⟨.umulh, [.id n, .id n]⟩ : Def),
  (⟨.mul, [.id n, .id n]⟩ : Def),
  (⟨.add3, [.id (n+49), .id (n+80), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+49), .id (n+80), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+49), .id (n+80), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+49), .id (n+80), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+49), .id (n+80), .imm 0#64]⟩ : Def),
  (⟨.mul, [.id (n+1), .id (n+1)]⟩ : Def),
  (⟨.add3, [.id (n+54), .id (n+87), .id (n+85)]⟩ : Def),
  (⟨.add3N, [.id (n+54), .id (n+87), .id (n+85)]⟩ : Def),
  (⟨.add3Z, [.id (n+54), .id (n+87), .id (n+85)]⟩ : Def),
  (⟨.carry3, [.id (n+54), .id (n+87), .id (n+85)]⟩ : Def),
  (⟨.ovf3, [.id (n+54), .id (n+87), .id (n+85)]⟩ : Def),
  (⟨.umulh, [.id (n+1), .id (n+1)]⟩ : Def),
  (⟨.add3, [.id (n+59), .id (n+93), .id (n+91)]⟩ : Def),
  (⟨.add3N, [.id (n+59), .id (n+93), .id (n+91)]⟩ : Def),
  (⟨.add3Z, [.id (n+59), .id (n+93), .id (n+91)]⟩ : Def),
  (⟨.carry3, [.id (n+59), .id (n+93), .id (n+91)]⟩ : Def),
  (⟨.ovf3, [.id (n+59), .id (n+93), .id (n+91)]⟩ : Def),
  (⟨.mul, [.id (n+4), .id (n+4)]⟩ : Def),
  (⟨.add3, [.id (n+64), .id (n+99), .id (n+97)]⟩ : Def),
  (⟨.add3N, [.id (n+64), .id (n+99), .id (n+97)]⟩ : Def),
  (⟨.add3Z, [.id (n+64), .id (n+99), .id (n+97)]⟩ : Def),
  (⟨.carry3, [.id (n+64), .id (n+99), .id (n+97)]⟩ : Def),
  (⟨.ovf3, [.id (n+64), .id (n+99), .id (n+97)]⟩ : Def),
  (⟨.umulh, [.id (n+4), .id (n+4)]⟩ : Def),
  (⟨.add3, [.id (n+69), .id (n+105), .id (n+103)]⟩ : Def),
  (⟨.add3N, [.id (n+69), .id (n+105), .id (n+103)]⟩ : Def),
  (⟨.add3Z, [.id (n+69), .id (n+105), .id (n+103)]⟩ : Def),
  (⟨.carry3, [.id (n+69), .id (n+105), .id (n+103)]⟩ : Def),
  (⟨.ovf3, [.id (n+69), .id (n+105), .id (n+103)]⟩ : Def),
  (⟨.mul, [.id (n+5), .id (n+5)]⟩ : Def),
  (⟨.add3, [.id (n+74), .id (n+111), .id (n+109)]⟩ : Def),
  (⟨.add3N, [.id (n+74), .id (n+111), .id (n+109)]⟩ : Def),
  (⟨.add3Z, [.id (n+74), .id (n+111), .id (n+109)]⟩ : Def),
  (⟨.carry3, [.id (n+74), .id (n+111), .id (n+109)]⟩ : Def),
  (⟨.ovf3, [.id (n+74), .id (n+111), .id (n+109)]⟩ : Def),
  (⟨.umulh, [.id (n+5), .id (n+5)]⟩ : Def),
  (⟨.add3, [.id (n+79), .id (n+117), .id (n+115)]⟩ : Def),
  (⟨.const 977#64, []⟩ : Def),
  (⟨.orr, [.id (n+119), .imm 4294967296#64]⟩ : Def),
  (⟨.mul, [.id (n+120), .id (n+100)]⟩ : Def),
  (⟨.umulh, [.id (n+120), .id (n+100)]⟩ : Def),
  (⟨.add3, [.id (n+81), .id (n+121), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+81), .id (n+121), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+81), .id (n+121), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+81), .id (n+121), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+81), .id (n+121), .imm 0#64]⟩ : Def),
  (⟨.mul, [.id (n+120), .id (n+106)]⟩ : Def),
  (⟨.umulh, [.id (n+120), .id (n+106)]⟩ : Def),
  (⟨.add3, [.id (n+82), .id (n+128), .id (n+126)]⟩ : Def),
  (⟨.add3N, [.id (n+82), .id (n+128), .id (n+126)]⟩ : Def),
  (⟨.add3Z, [.id (n+82), .id (n+128), .id (n+126)]⟩ : Def),
  (⟨.carry3, [.id (n+82), .id (n+128), .id (n+126)]⟩ : Def),
  (⟨.ovf3, [.id (n+82), .id (n+128), .id (n+126)]⟩ : Def),
  (⟨.mul, [.id (n+120), .id (n+112)]⟩ : Def),
  (⟨.umulh, [.id (n+120), .id (n+112)]⟩ : Def),
  (⟨.add3, [.id (n+88), .id (n+135), .id (n+133)]⟩ : Def),
  (⟨.add3N, [.id (n+88), .id (n+135), .id (n+133)]⟩ : Def),
  (⟨.add3Z, [.id (n+88), .id (n+135), .id (n+133)]⟩ : Def),
  (⟨.carry3, [.id (n+88), .id (n+135), .id (n+133)]⟩ : Def),
  (⟨.ovf3, [.id (n+88), .id (n+135), .id (n+133)]⟩ : Def),
  (⟨.mul, [.id (n+120), .id (n+118)]⟩ : Def),
  (⟨.umulh, [.id (n+120), .id (n+118)]⟩ : Def),
  (⟨.add3, [.id (n+94), .id (n+142), .id (n+140)]⟩ : Def),
  (⟨.add3N, [.id (n+94), .id (n+142), .id (n+140)]⟩ : Def),
  (⟨.add3Z, [.id (n+94), .id (n+142), .id (n+140)]⟩ : Def),
  (⟨.carry3, [.id (n+94), .id (n+142), .id (n+140)]⟩ : Def),
  (⟨.ovf3, [.id (n+94), .id (n+142), .id (n+140)]⟩ : Def),
  (⟨.cond 2#4, [.id (n+145), .id (n+146), .id (n+147), .id (n+148)]⟩ : Def),
  (⟨.add3, [.id (n+130), .id (n+122), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+130), .id (n+122), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+130), .id (n+122), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+130), .id (n+122), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+130), .id (n+122), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+137), .id (n+129), .id (n+153)]⟩ : Def),
  (⟨.add3N, [.id (n+137), .id (n+129), .id (n+153)]⟩ : Def),
  (⟨.add3Z, [.id (n+137), .id (n+129), .id (n+153)]⟩ : Def),
  (⟨.carry3, [.id (n+137), .id (n+129), .id (n+153)]⟩ : Def),
  (⟨.ovf3, [.id (n+137), .id (n+129), .id (n+153)]⟩ : Def),
  (⟨.add3, [.id (n+144), .id (n+136), .id (n+158)]⟩ : Def),
  (⟨.add3N, [.id (n+144), .id (n+136), .id (n+158)]⟩ : Def),
  (⟨.add3Z, [.id (n+144), .id (n+136), .id (n+158)]⟩ : Def),
  (⟨.carry3, [.id (n+144), .id (n+136), .id (n+158)]⟩ : Def),
  (⟨.ovf3, [.id (n+144), .id (n+136), .id (n+158)]⟩ : Def),
  (⟨.add3, [.id (n+149), .id (n+143), .id (n+163)]⟩ : Def),
  (⟨.add, [.id (n+165), .imm 1#64]⟩ : Def),
  (⟨.mul, [.id (n+120), .id (n+166)]⟩ : Def),
  (⟨.umulh, [.id (n+120), .id (n+166)]⟩ : Def),
  (⟨.add3, [.id (n+123), .id (n+167), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+123), .id (n+167), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+123), .id (n+167), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+123), .id (n+167), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+123), .id (n+167), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+150), .id (n+168), .id (n+172)]⟩ : Def),
  (⟨.add3N, [.id (n+150), .id (n+168), .id (n+172)]⟩ : Def),
  (⟨.add3Z, [.id (n+150), .id (n+168), .id (n+172)]⟩ : Def),
  (⟨.carry3, [.id (n+150), .id (n+168), .id (n+172)]⟩ : Def),
  (⟨.ovf3, [.id (n+150), .id (n+168), .id (n+172)]⟩ : Def),
  (⟨.add3, [.id (n+155), .imm 0#64, .id (n+177)]⟩ : Def),
  (⟨.add3N, [.id (n+155), .imm 0#64, .id (n+177)]⟩ : Def),
  (⟨.add3Z, [.id (n+155), .imm 0#64, .id (n+177)]⟩ : Def),
  (⟨.carry3, [.id (n+155), .imm 0#64, .id (n+177)]⟩ : Def),
  (⟨.ovf3, [.id (n+155), .imm 0#64, .id (n+177)]⟩ : Def),
  (⟨.add3, [.id (n+160), .imm 0#64, .id (n+182)]⟩ : Def),
  (⟨.add3N, [.id (n+160), .imm 0#64, .id (n+182)]⟩ : Def),
  (⟨.add3Z, [.id (n+160), .imm 0#64, .id (n+182)]⟩ : Def),
  (⟨.carry3, [.id (n+160), .imm 0#64, .id (n+182)]⟩ : Def),
  (⟨.ovf3, [.id (n+160), .imm 0#64, .id (n+182)]⟩ : Def),
  (⟨.cselc 3#4, [.id (n+185), .id (n+186), .id (n+187), .id (n+188), .id (n+120), .imm 0#64]⟩ : Def),
  (⟨.sbc3, [.id (n+169), .id (n+189), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+169), .id (n+189), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+169), .id (n+189), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+169), .id (n+189), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+169), .id (n+189), .imm 1#64]⟩ : Def),
  (⟨.sbc3, [.id (n+174), .imm 0#64, .id (n+193)]⟩ : Def),
  (⟨.sbc3N, [.id (n+174), .imm 0#64, .id (n+193)]⟩ : Def),
  (⟨.sbc3Z, [.id (n+174), .imm 0#64, .id (n+193)]⟩ : Def),
  (⟨.sbc3C, [.id (n+174), .imm 0#64, .id (n+193)]⟩ : Def),
  (⟨.sbc3V, [.id (n+174), .imm 0#64, .id (n+193)]⟩ : Def),
  (⟨.sbc3, [.id (n+179), .imm 0#64, .id (n+198)]⟩ : Def),
  (⟨.sbc3N, [.id (n+179), .imm 0#64, .id (n+198)]⟩ : Def),
  (⟨.sbc3Z, [.id (n+179), .imm 0#64, .id (n+198)]⟩ : Def),
  (⟨.sbc3C, [.id (n+179), .imm 0#64, .id (n+198)]⟩ : Def),
  (⟨.sbc3V, [.id (n+179), .imm 0#64, .id (n+198)]⟩ : Def),
  (⟨.sbc3, [.id (n+184), .imm 0#64, .id (n+203)]⟩ : Def)]

theorem row_positions (n xs : Nat) : RowPositions (compilerRows n xs) n := by
  constructor <;> rfl

theorem load_positions (n xs : Nat) : LoadPositions (compilerRows n xs) xs := by
  constructor <;> rfl

theorem equations_of_positions (inputs : List (BitVec 64)) (defs : List Def) (n : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n) :
    Equations (fun i => (evalDefs inputs defs).getD i 0) n := by
  constructor
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 2 (⟨.mul, [.id n, .id (n+1)]⟩ : Def) pos.row_2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 3 (⟨.umulh, [.id n, .id (n+1)]⟩ : Def) pos.row_3
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 6 (⟨.mul, [.id n, .id (n+5)]⟩ : Def) pos.row_6
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 7 (⟨.umulh, [.id n, .id (n+5)]⟩ : Def) pos.row_7
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 8 (⟨.mul, [.id n, .id (n+4)]⟩ : Def) pos.row_8
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 9 (⟨.umulh, [.id n, .id (n+4)]⟩ : Def) pos.row_9
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 10 (⟨.add3, [.id (n+3), .id (n+8), .imm 0#64]⟩ : Def) pos.row_10
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 13 (⟨.carry3, [.id (n+3), .id (n+8), .imm 0#64]⟩ : Def) pos.row_13
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 15 (⟨.add3, [.id (n+6), .id (n+9), .id (n+13)]⟩ : Def) pos.row_15
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 18 (⟨.carry3, [.id (n+6), .id (n+9), .id (n+13)]⟩ : Def) pos.row_18
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 20 (⟨.mul, [.id (n+1), .id (n+4)]⟩ : Def) pos.row_20
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 21 (⟨.umulh, [.id (n+1), .id (n+4)]⟩ : Def) pos.row_21
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 22 (⟨.add3, [.id (n+21), .imm 0#64, .id (n+18)]⟩ : Def) pos.row_22
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 23 (⟨.add3, [.id (n+15), .id (n+20), .imm 0#64]⟩ : Def) pos.row_23
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 26 (⟨.carry3, [.id (n+15), .id (n+20), .imm 0#64]⟩ : Def) pos.row_26
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 28 (⟨.mul, [.id (n+4), .id (n+5)]⟩ : Def) pos.row_28
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 29 (⟨.umulh, [.id (n+4), .id (n+5)]⟩ : Def) pos.row_29
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 30 (⟨.add3, [.id (n+7), .id (n+22), .id (n+26)]⟩ : Def) pos.row_30
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 33 (⟨.carry3, [.id (n+7), .id (n+22), .id (n+26)]⟩ : Def) pos.row_33
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 35 (⟨.mul, [.id (n+1), .id (n+5)]⟩ : Def) pos.row_35
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 36 (⟨.umulh, [.id (n+1), .id (n+5)]⟩ : Def) pos.row_36
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 37 (⟨.add3, [.id (n+36), .imm 0#64, .id (n+33)]⟩ : Def) pos.row_37
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 38 (⟨.add3, [.id (n+30), .id (n+35), .imm 0#64]⟩ : Def) pos.row_38
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 41 (⟨.carry3, [.id (n+30), .id (n+35), .imm 0#64]⟩ : Def) pos.row_41
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 43 (⟨.add3, [.id (n+28), .id (n+37), .id (n+41)]⟩ : Def) pos.row_43
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 46 (⟨.carry3, [.id (n+28), .id (n+37), .id (n+41)]⟩ : Def) pos.row_46
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 48 (⟨.add3, [.id (n+29), .imm 0#64, .id (n+46)]⟩ : Def) pos.row_48
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 49 (⟨.add3, [.id (n+2), .id (n+2), .imm 0#64]⟩ : Def) pos.row_49
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 52 (⟨.carry3, [.id (n+2), .id (n+2), .imm 0#64]⟩ : Def) pos.row_52
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 54 (⟨.add3, [.id (n+10), .id (n+10), .id (n+52)]⟩ : Def) pos.row_54
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 57 (⟨.carry3, [.id (n+10), .id (n+10), .id (n+52)]⟩ : Def) pos.row_57
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 59 (⟨.add3, [.id (n+23), .id (n+23), .id (n+57)]⟩ : Def) pos.row_59
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 62 (⟨.carry3, [.id (n+23), .id (n+23), .id (n+57)]⟩ : Def) pos.row_62
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 64 (⟨.add3, [.id (n+38), .id (n+38), .id (n+62)]⟩ : Def) pos.row_64
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 67 (⟨.carry3, [.id (n+38), .id (n+38), .id (n+62)]⟩ : Def) pos.row_67
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 69 (⟨.add3, [.id (n+43), .id (n+43), .id (n+67)]⟩ : Def) pos.row_69
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 72 (⟨.carry3, [.id (n+43), .id (n+43), .id (n+67)]⟩ : Def) pos.row_72
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 74 (⟨.add3, [.id (n+48), .id (n+48), .id (n+72)]⟩ : Def) pos.row_74
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 77 (⟨.carry3, [.id (n+48), .id (n+48), .id (n+72)]⟩ : Def) pos.row_77
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 79 (⟨.cond 2#4, [.id (n+75), .id (n+76), .id (n+77), .id (n+78)]⟩ : Def) pos.row_79
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 80 (⟨.umulh, [.id n, .id n]⟩ : Def) pos.row_80
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 81 (⟨.mul, [.id n, .id n]⟩ : Def) pos.row_81
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 82 (⟨.add3, [.id (n+49), .id (n+80), .imm 0#64]⟩ : Def) pos.row_82
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 85 (⟨.carry3, [.id (n+49), .id (n+80), .imm 0#64]⟩ : Def) pos.row_85
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 87 (⟨.mul, [.id (n+1), .id (n+1)]⟩ : Def) pos.row_87
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 88 (⟨.add3, [.id (n+54), .id (n+87), .id (n+85)]⟩ : Def) pos.row_88
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 91 (⟨.carry3, [.id (n+54), .id (n+87), .id (n+85)]⟩ : Def) pos.row_91
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 93 (⟨.umulh, [.id (n+1), .id (n+1)]⟩ : Def) pos.row_93
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 94 (⟨.add3, [.id (n+59), .id (n+93), .id (n+91)]⟩ : Def) pos.row_94
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 97 (⟨.carry3, [.id (n+59), .id (n+93), .id (n+91)]⟩ : Def) pos.row_97
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 99 (⟨.mul, [.id (n+4), .id (n+4)]⟩ : Def) pos.row_99
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 100 (⟨.add3, [.id (n+64), .id (n+99), .id (n+97)]⟩ : Def) pos.row_100
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 103 (⟨.carry3, [.id (n+64), .id (n+99), .id (n+97)]⟩ : Def) pos.row_103
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 105 (⟨.umulh, [.id (n+4), .id (n+4)]⟩ : Def) pos.row_105
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 106 (⟨.add3, [.id (n+69), .id (n+105), .id (n+103)]⟩ : Def) pos.row_106
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 109 (⟨.carry3, [.id (n+69), .id (n+105), .id (n+103)]⟩ : Def) pos.row_109
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 111 (⟨.mul, [.id (n+5), .id (n+5)]⟩ : Def) pos.row_111
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 112 (⟨.add3, [.id (n+74), .id (n+111), .id (n+109)]⟩ : Def) pos.row_112
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 115 (⟨.carry3, [.id (n+74), .id (n+111), .id (n+109)]⟩ : Def) pos.row_115
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 117 (⟨.umulh, [.id (n+5), .id (n+5)]⟩ : Def) pos.row_117
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 118 (⟨.add3, [.id (n+79), .id (n+117), .id (n+115)]⟩ : Def) pos.row_118
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · have h := TableEval.evalDefs_row inputs defs 119 (⟨.const 977#64, []⟩ : Def) pos.row_119
      (by rw [lengthEq]; simp [Def.Below, Arg.Below])
    rw [lengthEq, const_eval] at h
    exact h
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 120 (⟨.orr, [.id (n+119), .imm 4294967296#64]⟩ : Def) pos.row_120
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 121 (⟨.mul, [.id (n+120), .id (n+100)]⟩ : Def) pos.row_121
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 122 (⟨.umulh, [.id (n+120), .id (n+100)]⟩ : Def) pos.row_122
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 123 (⟨.add3, [.id (n+81), .id (n+121), .imm 0#64]⟩ : Def) pos.row_123
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 126 (⟨.carry3, [.id (n+81), .id (n+121), .imm 0#64]⟩ : Def) pos.row_126
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 128 (⟨.mul, [.id (n+120), .id (n+106)]⟩ : Def) pos.row_128
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 129 (⟨.umulh, [.id (n+120), .id (n+106)]⟩ : Def) pos.row_129
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 130 (⟨.add3, [.id (n+82), .id (n+128), .id (n+126)]⟩ : Def) pos.row_130
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 133 (⟨.carry3, [.id (n+82), .id (n+128), .id (n+126)]⟩ : Def) pos.row_133
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 135 (⟨.mul, [.id (n+120), .id (n+112)]⟩ : Def) pos.row_135
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 136 (⟨.umulh, [.id (n+120), .id (n+112)]⟩ : Def) pos.row_136
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 137 (⟨.add3, [.id (n+88), .id (n+135), .id (n+133)]⟩ : Def) pos.row_137
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 140 (⟨.carry3, [.id (n+88), .id (n+135), .id (n+133)]⟩ : Def) pos.row_140
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 142 (⟨.mul, [.id (n+120), .id (n+118)]⟩ : Def) pos.row_142
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 143 (⟨.umulh, [.id (n+120), .id (n+118)]⟩ : Def) pos.row_143
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 144 (⟨.add3, [.id (n+94), .id (n+142), .id (n+140)]⟩ : Def) pos.row_144
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 147 (⟨.carry3, [.id (n+94), .id (n+142), .id (n+140)]⟩ : Def) pos.row_147
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 149 (⟨.cond 2#4, [.id (n+145), .id (n+146), .id (n+147), .id (n+148)]⟩ : Def) pos.row_149
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 150 (⟨.add3, [.id (n+130), .id (n+122), .imm 0#64]⟩ : Def) pos.row_150
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 153 (⟨.carry3, [.id (n+130), .id (n+122), .imm 0#64]⟩ : Def) pos.row_153
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 155 (⟨.add3, [.id (n+137), .id (n+129), .id (n+153)]⟩ : Def) pos.row_155
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 158 (⟨.carry3, [.id (n+137), .id (n+129), .id (n+153)]⟩ : Def) pos.row_158
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 160 (⟨.add3, [.id (n+144), .id (n+136), .id (n+158)]⟩ : Def) pos.row_160
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 163 (⟨.carry3, [.id (n+144), .id (n+136), .id (n+158)]⟩ : Def) pos.row_163
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 165 (⟨.add3, [.id (n+149), .id (n+143), .id (n+163)]⟩ : Def) pos.row_165
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 166 (⟨.add, [.id (n+165), .imm 1#64]⟩ : Def) pos.row_166
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 167 (⟨.mul, [.id (n+120), .id (n+166)]⟩ : Def) pos.row_167
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 168 (⟨.umulh, [.id (n+120), .id (n+166)]⟩ : Def) pos.row_168
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 169 (⟨.add3, [.id (n+123), .id (n+167), .imm 0#64]⟩ : Def) pos.row_169
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 172 (⟨.carry3, [.id (n+123), .id (n+167), .imm 0#64]⟩ : Def) pos.row_172
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 174 (⟨.add3, [.id (n+150), .id (n+168), .id (n+172)]⟩ : Def) pos.row_174
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 177 (⟨.carry3, [.id (n+150), .id (n+168), .id (n+172)]⟩ : Def) pos.row_177
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 179 (⟨.add3, [.id (n+155), .imm 0#64, .id (n+177)]⟩ : Def) pos.row_179
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 182 (⟨.carry3, [.id (n+155), .imm 0#64, .id (n+177)]⟩ : Def) pos.row_182
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 184 (⟨.add3, [.id (n+160), .imm 0#64, .id (n+182)]⟩ : Def) pos.row_184
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 187 (⟨.carry3, [.id (n+160), .imm 0#64, .id (n+182)]⟩ : Def) pos.row_187
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 189 (⟨.cselc 3#4, [.id (n+185), .id (n+186), .id (n+187), .id (n+188), .id (n+120), .imm 0#64]⟩ : Def) pos.row_189
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 190 (⟨.sbc3, [.id (n+169), .id (n+189), .imm 1#64]⟩ : Def) pos.row_190
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 193 (⟨.sbc3C, [.id (n+169), .id (n+189), .imm 1#64]⟩ : Def) pos.row_193
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 195 (⟨.sbc3, [.id (n+174), .imm 0#64, .id (n+193)]⟩ : Def) pos.row_195
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 198 (⟨.sbc3C, [.id (n+174), .imm 0#64, .id (n+193)]⟩ : Def) pos.row_198
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 200 (⟨.sbc3, [.id (n+179), .imm 0#64, .id (n+198)]⟩ : Def) pos.row_200
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 203 (⟨.sbc3C, [.id (n+179), .imm 0#64, .id (n+198)]⟩ : Def) pos.row_203
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 205 (⟨.sbc3, [.id (n+184), .imm 0#64, .id (n+203)]⟩ : Def) pos.row_205
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))

theorem materialized_constant (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    v (n+120) = BitVec.ofNat 64 correction := by
  rw [rows.row_120, rows.row_119]
  decide

theorem first_fold (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    WordMulAdd.mulAdd4 (productLow v n) (BitVec.ofNat 64 correction) (productHigh v n) =
      ⟨⟨v (n+123),v (n+150),v (n+155),v (n+160)⟩,v (n+165)⟩ := by
  have flagBound : (v (n+147)).toNat ≤ 1 := by
    rw [rows.row_147]; exact Addition.carry3_le_one ..
  have selected : v (n+149) = v (n+147) := by
    rw [rows.row_149]; exact WordMulAdd.condition_carry _ _ _ _ flagBound
  have top : Op.add3.eval [v (n+143),v (n+147),v (n+163)] = v (n+165) := by
    rw [rows.row_165, selected]
    exact WordMulAdd.add_swap _ _ _
  simp only [WordMulAdd.mulAdd4, WordMulAdd.lowProducts, WordMulAdd.highProducts,
    Addition.coreChain4, productLow, productHigh, ← materialized_constant v n rows,
    ← rows.row_121, ← rows.row_122, ← rows.row_123, ← rows.row_126,
    ← rows.row_128, ← rows.row_129, ← rows.row_130, ← rows.row_133,
    ← rows.row_135, ← rows.row_136, ← rows.row_137, ← rows.row_140,
    ← rows.row_142, ← rows.row_143, ← rows.row_144, ← rows.row_147,
    ← rows.row_149, ← rows.row_150, ← rows.row_153, ← rows.row_155,
    ← rows.row_158, ← rows.row_160, ← rows.row_163, ← rows.row_165, WordMulAdd.add_zero, WordMulAdd.carry_zero, top]

theorem quotient_fold (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    WideWordReduce.foldedChain ⟨⟨v (n+123),v (n+150),v (n+155),v (n+160)⟩,v (n+165)⟩ =
      (⟨v (n+169),v (n+174),v (n+179),v (n+184)⟩,v (n+187)) := by
  have p0 : Op.mul.eval [v (n+166),v (n+120)] = v (n+167) :=
    (WordMulAdd.mul_swap _ _).trans rows.row_167.symm
  have p1 : Op.umulh.eval [v (n+166),v (n+120)] = v (n+168) :=
    (WordMulAdd.umulh_swap _ _).trans rows.row_168.symm
  simp only [WideWordReduce.foldedChain, CoreConstantMultiply.quotientWord,
    CoreConstantMultiply.correctionProduct, Addition.coreChain4,
    ← materialized_constant v n rows, ← rows.row_166, ← rows.row_167, ← rows.row_168, ← rows.row_169,
    ← rows.row_172, ← rows.row_174, ← rows.row_177, ← rows.row_179,
    ← rows.row_182, ← rows.row_184, ← rows.row_187, p0,p1]

theorem selected_value (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    v (n+189) = if v (n+187) == 0#64 then BitVec.ofNat 64 correction else 0#64 := by
  rw [rows.row_189, materialized_constant v n rows]
  exact SubSSA.select_correction _ _ _ _

theorem rows_reduceProduct (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    resultWords v n = WideWordReduce.reduceProduct (productLow v n) (productHigh v n) := by
  unfold WideWordReduce.reduceProduct
  rw [first_fold v n rows]
  unfold WideWordReduce.reduce4
  rw [quotient_fold v n rows]
  simp only [SecpMath.coreChain4, correctionWords, ← selected_value v n rows,
    ← rows.row_190, ← rows.row_193, ← rows.row_195, ← rows.row_198,
    ← rows.row_200, ← rows.row_203, ← rows.row_205, resultWords]

private def crossValue (v : Nat → BitVec 64) (n : Nat) : Nat :=
  (v (n+2)).toNat + limbRadix*(v (n+10)).toNat + limbRadix^2*(v (n+23)).toNat +
    limbRadix^3*(v (n+38)).toNat + limbRadix^4*(v (n+43)).toNat + limbRadix^5*(v (n+48)).toNat

private def doubledValue (v : Nat → BitVec 64) (n : Nat) : Nat :=
  (v (n+49)).toNat + limbRadix*(v (n+54)).toNat + limbRadix^2*(v (n+59)).toNat +
    limbRadix^3*(v (n+64)).toNat + limbRadix^4*(v (n+69)).toNat +
    limbRadix^5*(v (n+74)).toNat + limbRadix^6*(v (n+79)).toNat

private theorem cross_balance (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    crossValue v n = (v n).toNat*(v (n+1)).toNat + limbRadix*((v n).toNat*(v (n+4)).toNat) +
      limbRadix^2*((v n).toNat*(v (n+5)).toNat+(v (n+1)).toNat*(v (n+4)).toNat) +
      limbRadix^3*((v (n+1)).toNat*(v (n+5)).toNat) +
      limbRadix^4*((v (n+4)).toNat*(v (n+5)).toNat) := by
  have product_2 := Product.mul_balance (v n) (v (n+1))
  rw [← rows.row_2, ← rows.row_3] at product_2
  have product_6 := Product.mul_balance (v n) (v (n+5))
  rw [← rows.row_6, ← rows.row_7] at product_6
  have product_8 := Product.mul_balance (v n) (v (n+4))
  rw [← rows.row_8, ← rows.row_9] at product_8
  have balance_10 := Product.add_balance (v (n+3)) (v (n+8)) (0#64) (by decide)
  rw [← rows.row_10, ← rows.row_13] at balance_10
  have balance_15 := Product.add_balance (v (n+6)) (v (n+9)) (v (n+13)) (by rw [rows.row_13]; exact Addition.carry3_le_one ..)
  rw [← rows.row_15, ← rows.row_18] at balance_15
  have product_20 := Product.mul_balance (v (n+1)) (v (n+4))
  rw [← rows.row_20, ← rows.row_21] at product_20
  have balance_22 := SquareWord.high_add (v (n+1)) (v (n+4)) (v (n+18)) (by rw [rows.row_18]; exact Addition.carry3_le_one ..)
  rw [← rows.row_21, ← rows.row_22] at balance_22
  have balance_23 := Product.add_balance (v (n+15)) (v (n+20)) (0#64) (by decide)
  rw [← rows.row_23, ← rows.row_26] at balance_23
  have product_28 := Product.mul_balance (v (n+4)) (v (n+5))
  rw [← rows.row_28, ← rows.row_29] at product_28
  have balance_30 := Product.add_balance (v (n+7)) (v (n+22)) (v (n+26)) (by rw [rows.row_26]; exact Addition.carry3_le_one ..)
  rw [← rows.row_30, ← rows.row_33] at balance_30
  have product_35 := Product.mul_balance (v (n+1)) (v (n+5))
  rw [← rows.row_35, ← rows.row_36] at product_35
  have balance_37 := SquareWord.high_add (v (n+1)) (v (n+5)) (v (n+33)) (by rw [rows.row_33]; exact Addition.carry3_le_one ..)
  rw [← rows.row_36, ← rows.row_37] at balance_37
  have balance_38 := Product.add_balance (v (n+30)) (v (n+35)) (0#64) (by decide)
  rw [← rows.row_38, ← rows.row_41] at balance_38
  have balance_43 := Product.add_balance (v (n+28)) (v (n+37)) (v (n+41)) (by rw [rows.row_41]; exact Addition.carry3_le_one ..)
  rw [← rows.row_43, ← rows.row_46] at balance_43
  have balance_48 := SquareWord.high_add (v (n+4)) (v (n+5)) (v (n+46)) (by rw [rows.row_46]; exact Addition.carry3_le_one ..)
  rw [← rows.row_29, ← rows.row_48] at balance_48
  clear rows
  simp only [crossValue, limbRadix, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, Nat.zero_add] at *
  grind only

#print axioms cross_balance
private theorem double_balance (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    doubledValue v n = 2*crossValue v n := by
  have balance_49 := Product.add_balance (v (n+2)) (v (n+2)) (0#64) (by decide)
  rw [← rows.row_49, ← rows.row_52] at balance_49
  have balance_54 := Product.add_balance (v (n+10)) (v (n+10)) (v (n+52)) (by rw [rows.row_52]; exact Addition.carry3_le_one ..)
  rw [← rows.row_54, ← rows.row_57] at balance_54
  have balance_59 := Product.add_balance (v (n+23)) (v (n+23)) (v (n+57)) (by rw [rows.row_57]; exact Addition.carry3_le_one ..)
  rw [← rows.row_59, ← rows.row_62] at balance_59
  have balance_64 := Product.add_balance (v (n+38)) (v (n+38)) (v (n+62)) (by rw [rows.row_62]; exact Addition.carry3_le_one ..)
  rw [← rows.row_64, ← rows.row_67] at balance_64
  have balance_69 := Product.add_balance (v (n+43)) (v (n+43)) (v (n+67)) (by rw [rows.row_67]; exact Addition.carry3_le_one ..)
  rw [← rows.row_69, ← rows.row_72] at balance_69
  have balance_74 := Product.add_balance (v (n+48)) (v (n+48)) (v (n+72)) (by rw [rows.row_72]; exact Addition.carry3_le_one ..)
  rw [← rows.row_74, ← rows.row_77] at balance_74
  have selected_79 : v (n+79) = v (n+77) := by
    rw [rows.row_79]
    exact WordMulAdd.condition_carry _ _ _ _ (by rw [rows.row_77]; exact Addition.carry3_le_one ..)
  have selectedNat_79 := congrArg (fun w : BitVec 64 => w.toNat) selected_79
  clear rows
  simp only [crossValue, doubledValue, limbRadix,
    BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, Nat.zero_add] at *
  grind only

#print axioms double_balance
theorem product_balance (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    (productLow v n).value + radix*(productHigh v n).value =
      (loadedX v n).value * (loadedX v n).value := by
  have crossed := cross_balance v n rows
  have doubled := double_balance v n rows
  have product_81 := Product.mul_balance (v n) (v n)
  rw [← rows.row_81, ← rows.row_80] at product_81
  have balance_82 := Product.add_balance (v (n+49)) (v (n+80)) (0#64) (by decide)
  rw [← rows.row_82, ← rows.row_85] at balance_82
  have product_87 := Product.mul_balance (v (n+1)) (v (n+1))
  rw [← rows.row_87, ← rows.row_93] at product_87
  have balance_88 := Product.add_balance (v (n+54)) (v (n+87)) (v (n+85)) (by rw [rows.row_85]; exact Addition.carry3_le_one ..)
  rw [← rows.row_88, ← rows.row_91] at balance_88
  have balance_94 := Product.add_balance (v (n+59)) (v (n+93)) (v (n+91)) (by rw [rows.row_91]; exact Addition.carry3_le_one ..)
  rw [← rows.row_94, ← rows.row_97] at balance_94
  have product_99 := Product.mul_balance (v (n+4)) (v (n+4))
  rw [← rows.row_99, ← rows.row_105] at product_99
  have balance_100 := Product.add_balance (v (n+64)) (v (n+99)) (v (n+97)) (by rw [rows.row_97]; exact Addition.carry3_le_one ..)
  rw [← rows.row_100, ← rows.row_103] at balance_100
  have balance_106 := Product.add_balance (v (n+69)) (v (n+105)) (v (n+103)) (by rw [rows.row_103]; exact Addition.carry3_le_one ..)
  rw [← rows.row_106, ← rows.row_109] at balance_106
  have product_111 := Product.mul_balance (v (n+5)) (v (n+5))
  rw [← rows.row_111, ← rows.row_117] at product_111
  have balance_112 := Product.add_balance (v (n+74)) (v (n+111)) (v (n+109)) (by rw [rows.row_109]; exact Addition.carry3_le_one ..)
  rw [← rows.row_112, ← rows.row_115] at balance_112
  have balance_118 := Product.add_balance (v (n+79)) (v (n+117)) (v (n+115)) (by rw [rows.row_115]; exact Addition.carry3_le_one ..)
  rw [← rows.row_118] at balance_118
  generalize overflow_eq_118 : (Op.carry3.eval [v (n+79),v (n+117),v (n+115)]).toNat = overflow_118 at balance_118
  clear overflow_eq_118
  have expansion := SquareWord.square_expansion (v n).toNat (v (n+1)).toNat
    (v (n+4)).toNat (v (n+5)).toNat
  have bound := WideReduction.wide_product_bound (loadedX v n).value (loadedX v n).value
    (loadedX v n).value_lt (loadedX v n).value_lt
  clear rows
  simp only [productLow, productHigh, loadedX, crossValue, doubledValue, LimbWords.value, pack4, radix, limbRadix,
    BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, Nat.zero_add] at *
  grind only

theorem table_correct (inputs : List (BitVec 64)) (defs : List Def) (n xs : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n) (loads : LoadPositions defs xs)
    (inside : xs+32 ≤ n) :
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value < modulus ∧
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value =
      ((inputLimbs inputs xs).value*(inputLimbs inputs xs).value)%modulus := by
  have equations := equations_of_positions inputs defs n lengthEq pos
  have loaded := loaded_inputs inputs defs n xs lengthEq loads inside
  rw [rows_reduceProduct _ n equations]
  have result := WideWordReduce.reduceProduct_correct
    (productLow (fun i => (evalDefs inputs defs).getD i 0) n)
    (productHigh (fun i => (evalDefs inputs defs).getD i 0) n)
  rw [product_balance _ n equations, loaded] at result
  exact result

#print axioms equations_of_positions
#print axioms product_balance
#print axioms rows_reduceProduct
#print axioms table_correct
end SecpMath.SqrAltSSA
