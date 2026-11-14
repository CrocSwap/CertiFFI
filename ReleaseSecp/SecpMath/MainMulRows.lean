import SecpMath.HalfWord
import SecpMath.SubSSA
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
namespace SecpMath.MainMulSSA
open ArmCertValue SecpMath.Addition SecpMath.Product
open SecpMath.SubSSA (inputWordDef inputLimbs loaded_input_word)
structure LoadPositions (defs : List Def) (xs ys : Nat) : Prop where
  load_0 : defs[0]? = some (inputWordDef xs)
  load_1 : defs[1]? = some (inputWordDef (xs+8))
  load_2 : defs[2]? = some (inputWordDef ys)
  load_3 : defs[3]? = some (inputWordDef (ys+8))
  load_67 : defs[67]? = some (inputWordDef (xs+16))
  load_68 : defs[68]? = some (inputWordDef (xs+24))
  load_69 : defs[69]? = some (inputWordDef (ys+16))
  load_70 : defs[70]? = some (inputWordDef (ys+24))
  load_134 : defs[134]? = some (inputWordDef (xs+16))
  load_135 : defs[135]? = some (inputWordDef (xs+24))
  load_136 : defs[136]? = some (inputWordDef xs)
  load_137 : defs[137]? = some (inputWordDef (xs+8))
  load_149 : defs[149]? = some (inputWordDef ys)
  load_150 : defs[150]? = some (inputWordDef (ys+8))
private theorem const_eval (values : List (BitVec 64)) (c : BitVec 64) :
    Def.eval values ⟨.const c, []⟩ = c := rfl
structure Equations (v : Nat → BitVec 64) (n : Nat) : Prop where
  row_4 : v (n+4) = (Op.mul).eval [v n, v (n+2)]
  row_5 : v (n+5) = (Op.umulh).eval [v n, v (n+2)]
  row_6 : v (n+6) = (Op.mul).eval [v (n+1), v (n+3)]
  row_7 : v (n+7) = (Op.umulh).eval [v (n+1), v (n+3)]
  row_8 : v (n+8) = (Op.sbc3).eval [v (n+1), v n, 1#64]
  row_11 : v (n+11) = (Op.sbc3C).eval [v (n+1), v n, 1#64]
  row_13 : v (n+13) = (Op.cond 2#4).eval [v (n+9), v (n+10), v (n+11), v (n+12)]
  row_14 : v (n+14) = (Op.sub).eval [0#64, v (n+8)]
  row_15 : v (n+15) = (Op.csel).eval [v (n+13), v (n+8), v (n+14)]
  row_16 : v (n+16) = (Op.add).eval [v (n+15), 0#64]
  row_17 : v (n+17) = (Op.cselc 2#4).eval [v (n+9), v (n+10), v (n+11), v (n+12), 0#64, 18446744073709551615#64]
  row_18 : v (n+18) = (Op.add3).eval [v (n+6), v (n+5), 0#64]
  row_21 : v (n+21) = (Op.carry3).eval [v (n+6), v (n+5), 0#64]
  row_23 : v (n+23) = (Op.add3).eval [v (n+7), 0#64, v (n+21)]
  row_24 : v (n+24) = (Op.sbc3).eval [v (n+2), v (n+3), 1#64]
  row_27 : v (n+27) = (Op.sbc3C).eval [v (n+2), v (n+3), 1#64]
  row_29 : v (n+29) = (Op.cond 2#4).eval [v (n+25), v (n+26), v (n+27), v (n+28)]
  row_30 : v (n+30) = (Op.sub).eval [0#64, v (n+24)]
  row_31 : v (n+31) = (Op.csel).eval [v (n+29), v (n+24), v (n+30)]
  row_32 : v (n+32) = (Op.add).eval [v (n+31), 0#64]
  row_33 : v (n+33) = (Op.cond 2#4).eval [v (n+25), v (n+26), v (n+27), v (n+28)]
  row_34 : v (n+34) = (Op.not).eval [v (n+17)]
  row_35 : v (n+35) = (Op.csel).eval [v (n+33), v (n+17), v (n+34)]
  row_36 : v (n+36) = (Op.add).eval [v (n+35), 0#64]
  row_37 : v (n+37) = (Op.mul).eval [v (n+16), v (n+32)]
  row_38 : v (n+38) = (Op.umulh).eval [v (n+16), v (n+32)]
  row_39 : v (n+39) = (Op.add3).eval [v (n+4), v (n+18), 0#64]
  row_42 : v (n+42) = (Op.carry3).eval [v (n+4), v (n+18), 0#64]
  row_44 : v (n+44) = (Op.add3).eval [v (n+18), v (n+23), v (n+42)]
  row_47 : v (n+47) = (Op.carry3).eval [v (n+18), v (n+23), v (n+42)]
  row_49 : v (n+49) = (Op.add3).eval [v (n+23), 0#64, v (n+47)]
  row_52 : v (n+52) = (Op.carry3).eval [v (n+36), 1#64, 0#64]
  row_54 : v (n+54) = (Op.eor).eval [v (n+37), v (n+36)]
  row_55 : v (n+55) = (Op.add3).eval [v (n+54), v (n+39), v (n+52)]
  row_58 : v (n+58) = (Op.carry3).eval [v (n+54), v (n+39), v (n+52)]
  row_60 : v (n+60) = (Op.eor).eval [v (n+38), v (n+36)]
  row_61 : v (n+61) = (Op.add3).eval [v (n+60), v (n+44), v (n+58)]
  row_64 : v (n+64) = (Op.carry3).eval [v (n+60), v (n+44), v (n+58)]
  row_66 : v (n+66) = (Op.add3).eval [v (n+49), v (n+36), v (n+64)]
  row_71 : v (n+71) = (Op.mul).eval [v (n+67), v (n+69)]
  row_72 : v (n+72) = (Op.umulh).eval [v (n+67), v (n+69)]
  row_73 : v (n+73) = (Op.mul).eval [v (n+68), v (n+70)]
  row_74 : v (n+74) = (Op.umulh).eval [v (n+68), v (n+70)]
  row_75 : v (n+75) = (Op.sbc3).eval [v (n+68), v (n+67), 1#64]
  row_78 : v (n+78) = (Op.sbc3C).eval [v (n+68), v (n+67), 1#64]
  row_80 : v (n+80) = (Op.cond 2#4).eval [v (n+76), v (n+77), v (n+78), v (n+79)]
  row_81 : v (n+81) = (Op.sub).eval [0#64, v (n+75)]
  row_82 : v (n+82) = (Op.csel).eval [v (n+80), v (n+75), v (n+81)]
  row_83 : v (n+83) = (Op.add).eval [v (n+82), 0#64]
  row_84 : v (n+84) = (Op.cselc 2#4).eval [v (n+76), v (n+77), v (n+78), v (n+79), 0#64, 18446744073709551615#64]
  row_85 : v (n+85) = (Op.add3).eval [v (n+73), v (n+72), 0#64]
  row_88 : v (n+88) = (Op.carry3).eval [v (n+73), v (n+72), 0#64]
  row_90 : v (n+90) = (Op.add3).eval [v (n+74), 0#64, v (n+88)]
  row_91 : v (n+91) = (Op.sbc3).eval [v (n+69), v (n+70), 1#64]
  row_94 : v (n+94) = (Op.sbc3C).eval [v (n+69), v (n+70), 1#64]
  row_96 : v (n+96) = (Op.cond 2#4).eval [v (n+92), v (n+93), v (n+94), v (n+95)]
  row_97 : v (n+97) = (Op.sub).eval [0#64, v (n+91)]
  row_98 : v (n+98) = (Op.csel).eval [v (n+96), v (n+91), v (n+97)]
  row_99 : v (n+99) = (Op.add).eval [v (n+98), 0#64]
  row_100 : v (n+100) = (Op.cond 2#4).eval [v (n+92), v (n+93), v (n+94), v (n+95)]
  row_101 : v (n+101) = (Op.not).eval [v (n+84)]
  row_102 : v (n+102) = (Op.csel).eval [v (n+100), v (n+84), v (n+101)]
  row_103 : v (n+103) = (Op.add).eval [v (n+102), 0#64]
  row_104 : v (n+104) = (Op.mul).eval [v (n+83), v (n+99)]
  row_105 : v (n+105) = (Op.umulh).eval [v (n+83), v (n+99)]
  row_106 : v (n+106) = (Op.add3).eval [v (n+71), v (n+85), 0#64]
  row_109 : v (n+109) = (Op.carry3).eval [v (n+71), v (n+85), 0#64]
  row_111 : v (n+111) = (Op.add3).eval [v (n+85), v (n+90), v (n+109)]
  row_114 : v (n+114) = (Op.carry3).eval [v (n+85), v (n+90), v (n+109)]
  row_116 : v (n+116) = (Op.add3).eval [v (n+90), 0#64, v (n+114)]
  row_119 : v (n+119) = (Op.carry3).eval [v (n+103), 1#64, 0#64]
  row_121 : v (n+121) = (Op.eor).eval [v (n+104), v (n+103)]
  row_122 : v (n+122) = (Op.add3).eval [v (n+121), v (n+106), v (n+119)]
  row_125 : v (n+125) = (Op.carry3).eval [v (n+121), v (n+106), v (n+119)]
  row_127 : v (n+127) = (Op.eor).eval [v (n+105), v (n+103)]
  row_128 : v (n+128) = (Op.add3).eval [v (n+127), v (n+111), v (n+125)]
  row_131 : v (n+131) = (Op.carry3).eval [v (n+127), v (n+111), v (n+125)]
  row_133 : v (n+133) = (Op.add3).eval [v (n+116), v (n+103), v (n+131)]
  row_138 : v (n+138) = (Op.sbc3).eval [v (n+134), v (n+136), 1#64]
  row_141 : v (n+141) = (Op.sbc3C).eval [v (n+134), v (n+136), 1#64]
  row_143 : v (n+143) = (Op.sbc3).eval [v (n+135), v (n+137), v (n+141)]
  row_146 : v (n+146) = (Op.sbc3C).eval [v (n+135), v (n+137), v (n+141)]
  row_148 : v (n+148) = (Op.cselc 2#4).eval [v (n+144), v (n+145), v (n+146), v (n+147), 0#64, 18446744073709551615#64]
  row_151 : v (n+151) = (Op.sbc3).eval [v (n+149), v (n+69), 1#64]
  row_154 : v (n+154) = (Op.sbc3C).eval [v (n+149), v (n+69), 1#64]
  row_156 : v (n+156) = (Op.sbc3).eval [v (n+150), v (n+70), v (n+154)]
  row_159 : v (n+159) = (Op.sbc3C).eval [v (n+150), v (n+70), v (n+154)]
  row_161 : v (n+161) = (Op.cselc 2#4).eval [v (n+157), v (n+158), v (n+159), v (n+160), 0#64, 18446744073709551615#64]
  row_162 : v (n+162) = (Op.eor).eval [v (n+138), v (n+148)]
  row_163 : v (n+163) = (Op.sbc3).eval [v (n+162), v (n+148), 1#64]
  row_166 : v (n+166) = (Op.sbc3C).eval [v (n+162), v (n+148), 1#64]
  row_168 : v (n+168) = (Op.eor).eval [v (n+143), v (n+148)]
  row_169 : v (n+169) = (Op.sbc3).eval [v (n+168), v (n+148), v (n+166)]
  row_170 : v (n+170) = (Op.eor).eval [v (n+151), v (n+161)]
  row_171 : v (n+171) = (Op.sbc3).eval [v (n+170), v (n+161), 1#64]
  row_174 : v (n+174) = (Op.sbc3C).eval [v (n+170), v (n+161), 1#64]
  row_176 : v (n+176) = (Op.eor).eval [v (n+156), v (n+161)]
  row_177 : v (n+177) = (Op.sbc3).eval [v (n+176), v (n+161), v (n+174)]
  row_178 : v (n+178) = (Op.eor).eval [v (n+161), v (n+148)]
  row_179 : v (n+179) = (Op.add3).eval [v (n+71), v (n+61), 0#64]
  row_182 : v (n+182) = (Op.carry3).eval [v (n+71), v (n+61), 0#64]
  row_184 : v (n+184) = (Op.add3).eval [v (n+122), v (n+66), v (n+182)]
  row_187 : v (n+187) = (Op.carry3).eval [v (n+122), v (n+66), v (n+182)]
  row_189 : v (n+189) = (Op.add3).eval [v (n+128), 0#64, v (n+187)]
  row_192 : v (n+192) = (Op.carry3).eval [v (n+128), 0#64, v (n+187)]
  row_194 : v (n+194) = (Op.add3).eval [v (n+133), 0#64, v (n+192)]
  row_195 : v (n+195) = (Op.mul).eval [v (n+163), v (n+171)]
  row_196 : v (n+196) = (Op.umulh).eval [v (n+163), v (n+171)]
  row_197 : v (n+197) = (Op.mul).eval [v (n+169), v (n+177)]
  row_198 : v (n+198) = (Op.umulh).eval [v (n+169), v (n+177)]
  row_199 : v (n+199) = (Op.sbc3).eval [v (n+169), v (n+163), 1#64]
  row_202 : v (n+202) = (Op.sbc3C).eval [v (n+169), v (n+163), 1#64]
  row_204 : v (n+204) = (Op.cond 2#4).eval [v (n+200), v (n+201), v (n+202), v (n+203)]
  row_205 : v (n+205) = (Op.sub).eval [0#64, v (n+199)]
  row_206 : v (n+206) = (Op.csel).eval [v (n+204), v (n+199), v (n+205)]
  row_207 : v (n+207) = (Op.add).eval [v (n+206), 0#64]
  row_208 : v (n+208) = (Op.cselc 2#4).eval [v (n+200), v (n+201), v (n+202), v (n+203), 0#64, 18446744073709551615#64]
  row_209 : v (n+209) = (Op.add3).eval [v (n+197), v (n+196), 0#64]
  row_212 : v (n+212) = (Op.carry3).eval [v (n+197), v (n+196), 0#64]
  row_214 : v (n+214) = (Op.add3).eval [v (n+198), 0#64, v (n+212)]
  row_215 : v (n+215) = (Op.sbc3).eval [v (n+171), v (n+177), 1#64]
  row_218 : v (n+218) = (Op.sbc3C).eval [v (n+171), v (n+177), 1#64]
  row_220 : v (n+220) = (Op.cond 2#4).eval [v (n+216), v (n+217), v (n+218), v (n+219)]
  row_221 : v (n+221) = (Op.sub).eval [0#64, v (n+215)]
  row_222 : v (n+222) = (Op.csel).eval [v (n+220), v (n+215), v (n+221)]
  row_223 : v (n+223) = (Op.add).eval [v (n+222), 0#64]
  row_224 : v (n+224) = (Op.cond 2#4).eval [v (n+216), v (n+217), v (n+218), v (n+219)]
  row_225 : v (n+225) = (Op.not).eval [v (n+208)]
  row_226 : v (n+226) = (Op.csel).eval [v (n+224), v (n+208), v (n+225)]
  row_227 : v (n+227) = (Op.add).eval [v (n+226), 0#64]
  row_228 : v (n+228) = (Op.mul).eval [v (n+207), v (n+223)]
  row_229 : v (n+229) = (Op.umulh).eval [v (n+207), v (n+223)]
  row_230 : v (n+230) = (Op.add3).eval [v (n+195), v (n+209), 0#64]
  row_233 : v (n+233) = (Op.carry3).eval [v (n+195), v (n+209), 0#64]
  row_235 : v (n+235) = (Op.add3).eval [v (n+209), v (n+214), v (n+233)]
  row_238 : v (n+238) = (Op.carry3).eval [v (n+209), v (n+214), v (n+233)]
  row_240 : v (n+240) = (Op.add3).eval [v (n+214), 0#64, v (n+238)]
  row_243 : v (n+243) = (Op.carry3).eval [v (n+227), 1#64, 0#64]
  row_245 : v (n+245) = (Op.eor).eval [v (n+228), v (n+227)]
  row_246 : v (n+246) = (Op.add3).eval [v (n+245), v (n+230), v (n+243)]
  row_249 : v (n+249) = (Op.carry3).eval [v (n+245), v (n+230), v (n+243)]
  row_251 : v (n+251) = (Op.eor).eval [v (n+229), v (n+227)]
  row_252 : v (n+252) = (Op.add3).eval [v (n+251), v (n+235), v (n+249)]
  row_255 : v (n+255) = (Op.carry3).eval [v (n+251), v (n+235), v (n+249)]
  row_257 : v (n+257) = (Op.add3).eval [v (n+240), v (n+227), v (n+255)]
  row_258 : v (n+258) = (Op.add3).eval [v (n+179), v (n+4), 0#64]
  row_261 : v (n+261) = (Op.carry3).eval [v (n+179), v (n+4), 0#64]
  row_263 : v (n+263) = (Op.add3).eval [v (n+184), v (n+55), v (n+261)]
  row_266 : v (n+266) = (Op.carry3).eval [v (n+184), v (n+55), v (n+261)]
  row_268 : v (n+268) = (Op.add3).eval [v (n+189), v (n+179), v (n+266)]
  row_271 : v (n+271) = (Op.carry3).eval [v (n+189), v (n+179), v (n+266)]
  row_273 : v (n+273) = (Op.add3).eval [v (n+194), v (n+184), v (n+271)]
  row_276 : v (n+276) = (Op.carry3).eval [v (n+194), v (n+184), v (n+271)]
  row_278 : v (n+278) = (Op.add3).eval [v (n+189), 0#64, v (n+276)]
  row_281 : v (n+281) = (Op.carry3).eval [v (n+189), 0#64, v (n+276)]
  row_283 : v (n+283) = (Op.add3).eval [v (n+194), 0#64, v (n+281)]
  row_286 : v (n+286) = (Op.carry3).eval [v (n+178), 1#64, 0#64]
  row_288 : v (n+288) = (Op.eor).eval [v (n+195), v (n+178)]
  row_289 : v (n+289) = (Op.add3).eval [v (n+288), v (n+258), v (n+286)]
  row_292 : v (n+292) = (Op.carry3).eval [v (n+288), v (n+258), v (n+286)]
  row_294 : v (n+294) = (Op.eor).eval [v (n+246), v (n+178)]
  row_295 : v (n+295) = (Op.add3).eval [v (n+294), v (n+263), v (n+292)]
  row_298 : v (n+298) = (Op.carry3).eval [v (n+294), v (n+263), v (n+292)]
  row_300 : v (n+300) = (Op.eor).eval [v (n+252), v (n+178)]
  row_301 : v (n+301) = (Op.add3).eval [v (n+300), v (n+268), v (n+298)]
  row_304 : v (n+304) = (Op.carry3).eval [v (n+300), v (n+268), v (n+298)]
  row_306 : v (n+306) = (Op.eor).eval [v (n+257), v (n+178)]
  row_307 : v (n+307) = (Op.add3).eval [v (n+306), v (n+273), v (n+304)]
  row_310 : v (n+310) = (Op.carry3).eval [v (n+306), v (n+273), v (n+304)]
  row_312 : v (n+312) = (Op.add3).eval [v (n+278), v (n+178), v (n+310)]
  row_315 : v (n+315) = (Op.carry3).eval [v (n+278), v (n+178), v (n+310)]
  row_317 : v (n+317) = (Op.add3).eval [v (n+283), v (n+178), v (n+315)]
  row_318 : v (n+318) = 977#64
  row_319 : v (n+319) = (Op.orr).eval [v (n+318), 4294967296#64]
  row_320 : v (n+320) = (Op.mul).eval [v (n+319), v (n+301)]
  row_321 : v (n+321) = (Op.umulh).eval [v (n+319), v (n+301)]
  row_322 : v (n+322) = (Op.and).eval [v (n+307), 4294967295#64]
  row_323 : v (n+323) = (Op.lsr 32).eval [v (n+307)]
  row_324 : v (n+324) = (Op.mul).eval [v (n+318), v (n+322)]
  row_325 : v (n+325) = (Op.mul).eval [v (n+318), v (n+323)]
  row_326 : v (n+326) = (Op.add).eval [v (n+325), v (n+322)]
  row_327 : v (n+327) = (Op.add).eval [v (n+326), 0#64]
  row_328 : v (n+328) = (Op.lsl 32).eval [v (n+327)]
  row_329 : v (n+329) = (Op.add3).eval [v (n+324), v (n+328), 0#64]
  row_330 : v (n+330) = (Op.add).eval [v (n+329), 0#64]
  row_331 : v (n+331) = (Op.lsl 32).eval [v (n+327)]
  row_333 : v (n+333) = (Op.add).eval [v (n+332), 0#64]
  row_334 : v (n+334) = (Op.lsl 32).eval [v (n+327)]
  row_336 : v (n+336) = (Op.add).eval [v (n+335), 0#64]
  row_337 : v (n+337) = (Op.lsl 32).eval [v (n+327)]
  row_338 : v (n+338) = (Op.carry3).eval [v (n+324), v (n+337), 0#64]
  row_339 : v (n+339) = (Op.add).eval [v (n+338), 0#64]
  row_340 : v (n+340) = (Op.lsl 32).eval [v (n+327)]
  row_342 : v (n+342) = (Op.add).eval [v (n+341), 0#64]
  row_343 : v (n+343) = (Op.lsr 32).eval [v (n+327)]
  row_344 : v (n+344) = (Op.add3).eval [v (n+323), v (n+343), v (n+339)]
  row_345 : v (n+345) = (Op.mul).eval [v (n+319), v (n+312)]
  row_346 : v (n+346) = (Op.umulh).eval [v (n+319), v (n+312)]
  row_347 : v (n+347) = (Op.and).eval [v (n+317), 4294967295#64]
  row_348 : v (n+348) = (Op.lsr 32).eval [v (n+317)]
  row_349 : v (n+349) = (Op.mul).eval [v (n+318), v (n+347)]
  row_350 : v (n+350) = (Op.mul).eval [v (n+318), v (n+348)]
  row_351 : v (n+351) = (Op.add).eval [v (n+350), v (n+347)]
  row_352 : v (n+352) = (Op.add).eval [v (n+351), 0#64]
  row_353 : v (n+353) = (Op.lsl 32).eval [v (n+352)]
  row_354 : v (n+354) = (Op.add3).eval [v (n+349), v (n+353), 0#64]
  row_355 : v (n+355) = (Op.add).eval [v (n+354), 0#64]
  row_356 : v (n+356) = (Op.lsl 32).eval [v (n+352)]
  row_358 : v (n+358) = (Op.add).eval [v (n+357), 0#64]
  row_359 : v (n+359) = (Op.lsl 32).eval [v (n+352)]
  row_361 : v (n+361) = (Op.add).eval [v (n+360), 0#64]
  row_362 : v (n+362) = (Op.lsl 32).eval [v (n+352)]
  row_363 : v (n+363) = (Op.carry3).eval [v (n+349), v (n+362), 0#64]
  row_364 : v (n+364) = (Op.add).eval [v (n+363), 0#64]
  row_365 : v (n+365) = (Op.lsl 32).eval [v (n+352)]
  row_367 : v (n+367) = (Op.add).eval [v (n+366), 0#64]
  row_368 : v (n+368) = (Op.lsr 32).eval [v (n+352)]
  row_369 : v (n+369) = (Op.add3).eval [v (n+348), v (n+368), v (n+364)]
  row_370 : v (n+370) = (Op.add3).eval [v (n+4), v (n+320), 0#64]
  row_373 : v (n+373) = (Op.carry3).eval [v (n+4), v (n+320), 0#64]
  row_375 : v (n+375) = (Op.add3).eval [v (n+55), v (n+330), v (n+373)]
  row_378 : v (n+378) = (Op.carry3).eval [v (n+55), v (n+330), v (n+373)]
  row_380 : v (n+380) = (Op.add3).eval [v (n+289), v (n+345), v (n+378)]
  row_383 : v (n+383) = (Op.carry3).eval [v (n+289), v (n+345), v (n+378)]
  row_385 : v (n+385) = (Op.add3).eval [v (n+295), v (n+355), v (n+383)]
  row_388 : v (n+388) = (Op.carry3).eval [v (n+295), v (n+355), v (n+383)]
  row_390 : v (n+390) = (Op.cond 2#4).eval [v (n+386), v (n+387), v (n+388), v (n+389)]
  row_391 : v (n+391) = (Op.add3).eval [v (n+375), v (n+321), 0#64]
  row_394 : v (n+394) = (Op.carry3).eval [v (n+375), v (n+321), 0#64]
  row_396 : v (n+396) = (Op.add3).eval [v (n+380), v (n+344), v (n+394)]
  row_399 : v (n+399) = (Op.carry3).eval [v (n+380), v (n+344), v (n+394)]
  row_401 : v (n+401) = (Op.add3).eval [v (n+385), v (n+346), v (n+399)]
  row_404 : v (n+404) = (Op.carry3).eval [v (n+385), v (n+346), v (n+399)]
  row_406 : v (n+406) = (Op.add3).eval [v (n+390), v (n+369), v (n+404)]
  row_407 : v (n+407) = (Op.add).eval [v (n+406), 1#64]
  row_408 : v (n+408) = (Op.mul).eval [v (n+318), v (n+407)]
  row_409 : v (n+409) = (Op.lsr 32).eval [v (n+407)]
  row_410 : v (n+410) = (Op.lsl 32).eval [v (n+407)]
  row_411 : v (n+411) = (Op.add3).eval [v (n+408), v (n+410), 0#64]
  row_412 : v (n+412) = (Op.add).eval [v (n+411), 0#64]
  row_413 : v (n+413) = (Op.lsl 32).eval [v (n+407)]
  row_415 : v (n+415) = (Op.add).eval [v (n+414), 0#64]
  row_416 : v (n+416) = (Op.lsl 32).eval [v (n+407)]
  row_418 : v (n+418) = (Op.add).eval [v (n+417), 0#64]
  row_419 : v (n+419) = (Op.lsl 32).eval [v (n+407)]
  row_420 : v (n+420) = (Op.carry3).eval [v (n+408), v (n+419), 0#64]
  row_421 : v (n+421) = (Op.add).eval [v (n+420), 0#64]
  row_422 : v (n+422) = (Op.lsl 32).eval [v (n+407)]
  row_424 : v (n+424) = (Op.add).eval [v (n+423), 0#64]
  row_425 : v (n+425) = (Op.add3).eval [0#64, v (n+409), v (n+421)]
  row_426 : v (n+426) = (Op.add3).eval [v (n+370), v (n+412), 0#64]
  row_429 : v (n+429) = (Op.carry3).eval [v (n+370), v (n+412), 0#64]
  row_431 : v (n+431) = (Op.add3).eval [v (n+391), v (n+425), v (n+429)]
  row_434 : v (n+434) = (Op.carry3).eval [v (n+391), v (n+425), v (n+429)]
  row_436 : v (n+436) = (Op.add3).eval [v (n+396), 0#64, v (n+434)]
  row_439 : v (n+439) = (Op.carry3).eval [v (n+396), 0#64, v (n+434)]
  row_441 : v (n+441) = (Op.add3).eval [v (n+401), 0#64, v (n+439)]
  row_444 : v (n+444) = (Op.carry3).eval [v (n+401), 0#64, v (n+439)]
  row_446 : v (n+446) = (Op.cselc 3#4).eval [v (n+442), v (n+443), v (n+444), v (n+445), v (n+319), 0#64]
  row_447 : v (n+447) = (Op.sbc3).eval [v (n+426), v (n+446), 1#64]
  row_450 : v (n+450) = (Op.sbc3C).eval [v (n+426), v (n+446), 1#64]
  row_452 : v (n+452) = (Op.sbc3).eval [v (n+431), 0#64, v (n+450)]
  row_455 : v (n+455) = (Op.sbc3C).eval [v (n+431), 0#64, v (n+450)]
  row_457 : v (n+457) = (Op.sbc3).eval [v (n+436), 0#64, v (n+455)]
  row_460 : v (n+460) = (Op.sbc3C).eval [v (n+436), 0#64, v (n+455)]
  row_462 : v (n+462) = (Op.sbc3).eval [v (n+441), 0#64, v (n+460)]

structure RowPositions (defs : List Def) (n : Nat) : Prop where
  row_4 : defs[4]? = some (⟨.mul, [.id n, .id (n+2)]⟩ : Def)
  row_5 : defs[5]? = some (⟨.umulh, [.id n, .id (n+2)]⟩ : Def)
  row_6 : defs[6]? = some (⟨.mul, [.id (n+1), .id (n+3)]⟩ : Def)
  row_7 : defs[7]? = some (⟨.umulh, [.id (n+1), .id (n+3)]⟩ : Def)
  row_8 : defs[8]? = some (⟨.sbc3, [.id (n+1), .id n, .imm 1#64]⟩ : Def)
  row_11 : defs[11]? = some (⟨.sbc3C, [.id (n+1), .id n, .imm 1#64]⟩ : Def)
  row_13 : defs[13]? = some (⟨.cond 2#4, [.id (n+9), .id (n+10), .id (n+11), .id (n+12)]⟩ : Def)
  row_14 : defs[14]? = some (⟨.sub, [.imm 0#64, .id (n+8)]⟩ : Def)
  row_15 : defs[15]? = some (⟨.csel, [.id (n+13), .id (n+8), .id (n+14)]⟩ : Def)
  row_16 : defs[16]? = some (⟨.add, [.id (n+15), .imm 0#64]⟩ : Def)
  row_17 : defs[17]? = some (⟨.cselc 2#4, [.id (n+9), .id (n+10), .id (n+11), .id (n+12), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def)
  row_18 : defs[18]? = some (⟨.add3, [.id (n+6), .id (n+5), .imm 0#64]⟩ : Def)
  row_21 : defs[21]? = some (⟨.carry3, [.id (n+6), .id (n+5), .imm 0#64]⟩ : Def)
  row_23 : defs[23]? = some (⟨.add3, [.id (n+7), .imm 0#64, .id (n+21)]⟩ : Def)
  row_24 : defs[24]? = some (⟨.sbc3, [.id (n+2), .id (n+3), .imm 1#64]⟩ : Def)
  row_27 : defs[27]? = some (⟨.sbc3C, [.id (n+2), .id (n+3), .imm 1#64]⟩ : Def)
  row_29 : defs[29]? = some (⟨.cond 2#4, [.id (n+25), .id (n+26), .id (n+27), .id (n+28)]⟩ : Def)
  row_30 : defs[30]? = some (⟨.sub, [.imm 0#64, .id (n+24)]⟩ : Def)
  row_31 : defs[31]? = some (⟨.csel, [.id (n+29), .id (n+24), .id (n+30)]⟩ : Def)
  row_32 : defs[32]? = some (⟨.add, [.id (n+31), .imm 0#64]⟩ : Def)
  row_33 : defs[33]? = some (⟨.cond 2#4, [.id (n+25), .id (n+26), .id (n+27), .id (n+28)]⟩ : Def)
  row_34 : defs[34]? = some (⟨.not, [.id (n+17)]⟩ : Def)
  row_35 : defs[35]? = some (⟨.csel, [.id (n+33), .id (n+17), .id (n+34)]⟩ : Def)
  row_36 : defs[36]? = some (⟨.add, [.id (n+35), .imm 0#64]⟩ : Def)
  row_37 : defs[37]? = some (⟨.mul, [.id (n+16), .id (n+32)]⟩ : Def)
  row_38 : defs[38]? = some (⟨.umulh, [.id (n+16), .id (n+32)]⟩ : Def)
  row_39 : defs[39]? = some (⟨.add3, [.id (n+4), .id (n+18), .imm 0#64]⟩ : Def)
  row_42 : defs[42]? = some (⟨.carry3, [.id (n+4), .id (n+18), .imm 0#64]⟩ : Def)
  row_44 : defs[44]? = some (⟨.add3, [.id (n+18), .id (n+23), .id (n+42)]⟩ : Def)
  row_47 : defs[47]? = some (⟨.carry3, [.id (n+18), .id (n+23), .id (n+42)]⟩ : Def)
  row_49 : defs[49]? = some (⟨.add3, [.id (n+23), .imm 0#64, .id (n+47)]⟩ : Def)
  row_52 : defs[52]? = some (⟨.carry3, [.id (n+36), .imm 1#64, .imm 0#64]⟩ : Def)
  row_54 : defs[54]? = some (⟨.eor, [.id (n+37), .id (n+36)]⟩ : Def)
  row_55 : defs[55]? = some (⟨.add3, [.id (n+54), .id (n+39), .id (n+52)]⟩ : Def)
  row_58 : defs[58]? = some (⟨.carry3, [.id (n+54), .id (n+39), .id (n+52)]⟩ : Def)
  row_60 : defs[60]? = some (⟨.eor, [.id (n+38), .id (n+36)]⟩ : Def)
  row_61 : defs[61]? = some (⟨.add3, [.id (n+60), .id (n+44), .id (n+58)]⟩ : Def)
  row_64 : defs[64]? = some (⟨.carry3, [.id (n+60), .id (n+44), .id (n+58)]⟩ : Def)
  row_66 : defs[66]? = some (⟨.add3, [.id (n+49), .id (n+36), .id (n+64)]⟩ : Def)
  row_71 : defs[71]? = some (⟨.mul, [.id (n+67), .id (n+69)]⟩ : Def)
  row_72 : defs[72]? = some (⟨.umulh, [.id (n+67), .id (n+69)]⟩ : Def)
  row_73 : defs[73]? = some (⟨.mul, [.id (n+68), .id (n+70)]⟩ : Def)
  row_74 : defs[74]? = some (⟨.umulh, [.id (n+68), .id (n+70)]⟩ : Def)
  row_75 : defs[75]? = some (⟨.sbc3, [.id (n+68), .id (n+67), .imm 1#64]⟩ : Def)
  row_78 : defs[78]? = some (⟨.sbc3C, [.id (n+68), .id (n+67), .imm 1#64]⟩ : Def)
  row_80 : defs[80]? = some (⟨.cond 2#4, [.id (n+76), .id (n+77), .id (n+78), .id (n+79)]⟩ : Def)
  row_81 : defs[81]? = some (⟨.sub, [.imm 0#64, .id (n+75)]⟩ : Def)
  row_82 : defs[82]? = some (⟨.csel, [.id (n+80), .id (n+75), .id (n+81)]⟩ : Def)
  row_83 : defs[83]? = some (⟨.add, [.id (n+82), .imm 0#64]⟩ : Def)
  row_84 : defs[84]? = some (⟨.cselc 2#4, [.id (n+76), .id (n+77), .id (n+78), .id (n+79), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def)
  row_85 : defs[85]? = some (⟨.add3, [.id (n+73), .id (n+72), .imm 0#64]⟩ : Def)
  row_88 : defs[88]? = some (⟨.carry3, [.id (n+73), .id (n+72), .imm 0#64]⟩ : Def)
  row_90 : defs[90]? = some (⟨.add3, [.id (n+74), .imm 0#64, .id (n+88)]⟩ : Def)
  row_91 : defs[91]? = some (⟨.sbc3, [.id (n+69), .id (n+70), .imm 1#64]⟩ : Def)
  row_94 : defs[94]? = some (⟨.sbc3C, [.id (n+69), .id (n+70), .imm 1#64]⟩ : Def)
  row_96 : defs[96]? = some (⟨.cond 2#4, [.id (n+92), .id (n+93), .id (n+94), .id (n+95)]⟩ : Def)
  row_97 : defs[97]? = some (⟨.sub, [.imm 0#64, .id (n+91)]⟩ : Def)
  row_98 : defs[98]? = some (⟨.csel, [.id (n+96), .id (n+91), .id (n+97)]⟩ : Def)
  row_99 : defs[99]? = some (⟨.add, [.id (n+98), .imm 0#64]⟩ : Def)
  row_100 : defs[100]? = some (⟨.cond 2#4, [.id (n+92), .id (n+93), .id (n+94), .id (n+95)]⟩ : Def)
  row_101 : defs[101]? = some (⟨.not, [.id (n+84)]⟩ : Def)
  row_102 : defs[102]? = some (⟨.csel, [.id (n+100), .id (n+84), .id (n+101)]⟩ : Def)
  row_103 : defs[103]? = some (⟨.add, [.id (n+102), .imm 0#64]⟩ : Def)
  row_104 : defs[104]? = some (⟨.mul, [.id (n+83), .id (n+99)]⟩ : Def)
  row_105 : defs[105]? = some (⟨.umulh, [.id (n+83), .id (n+99)]⟩ : Def)
  row_106 : defs[106]? = some (⟨.add3, [.id (n+71), .id (n+85), .imm 0#64]⟩ : Def)
  row_109 : defs[109]? = some (⟨.carry3, [.id (n+71), .id (n+85), .imm 0#64]⟩ : Def)
  row_111 : defs[111]? = some (⟨.add3, [.id (n+85), .id (n+90), .id (n+109)]⟩ : Def)
  row_114 : defs[114]? = some (⟨.carry3, [.id (n+85), .id (n+90), .id (n+109)]⟩ : Def)
  row_116 : defs[116]? = some (⟨.add3, [.id (n+90), .imm 0#64, .id (n+114)]⟩ : Def)
  row_119 : defs[119]? = some (⟨.carry3, [.id (n+103), .imm 1#64, .imm 0#64]⟩ : Def)
  row_121 : defs[121]? = some (⟨.eor, [.id (n+104), .id (n+103)]⟩ : Def)
  row_122 : defs[122]? = some (⟨.add3, [.id (n+121), .id (n+106), .id (n+119)]⟩ : Def)
  row_125 : defs[125]? = some (⟨.carry3, [.id (n+121), .id (n+106), .id (n+119)]⟩ : Def)
  row_127 : defs[127]? = some (⟨.eor, [.id (n+105), .id (n+103)]⟩ : Def)
  row_128 : defs[128]? = some (⟨.add3, [.id (n+127), .id (n+111), .id (n+125)]⟩ : Def)
  row_131 : defs[131]? = some (⟨.carry3, [.id (n+127), .id (n+111), .id (n+125)]⟩ : Def)
  row_133 : defs[133]? = some (⟨.add3, [.id (n+116), .id (n+103), .id (n+131)]⟩ : Def)
  row_138 : defs[138]? = some (⟨.sbc3, [.id (n+134), .id (n+136), .imm 1#64]⟩ : Def)
  row_141 : defs[141]? = some (⟨.sbc3C, [.id (n+134), .id (n+136), .imm 1#64]⟩ : Def)
  row_143 : defs[143]? = some (⟨.sbc3, [.id (n+135), .id (n+137), .id (n+141)]⟩ : Def)
  row_146 : defs[146]? = some (⟨.sbc3C, [.id (n+135), .id (n+137), .id (n+141)]⟩ : Def)
  row_148 : defs[148]? = some (⟨.cselc 2#4, [.id (n+144), .id (n+145), .id (n+146), .id (n+147), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def)
  row_151 : defs[151]? = some (⟨.sbc3, [.id (n+149), .id (n+69), .imm 1#64]⟩ : Def)
  row_154 : defs[154]? = some (⟨.sbc3C, [.id (n+149), .id (n+69), .imm 1#64]⟩ : Def)
  row_156 : defs[156]? = some (⟨.sbc3, [.id (n+150), .id (n+70), .id (n+154)]⟩ : Def)
  row_159 : defs[159]? = some (⟨.sbc3C, [.id (n+150), .id (n+70), .id (n+154)]⟩ : Def)
  row_161 : defs[161]? = some (⟨.cselc 2#4, [.id (n+157), .id (n+158), .id (n+159), .id (n+160), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def)
  row_162 : defs[162]? = some (⟨.eor, [.id (n+138), .id (n+148)]⟩ : Def)
  row_163 : defs[163]? = some (⟨.sbc3, [.id (n+162), .id (n+148), .imm 1#64]⟩ : Def)
  row_166 : defs[166]? = some (⟨.sbc3C, [.id (n+162), .id (n+148), .imm 1#64]⟩ : Def)
  row_168 : defs[168]? = some (⟨.eor, [.id (n+143), .id (n+148)]⟩ : Def)
  row_169 : defs[169]? = some (⟨.sbc3, [.id (n+168), .id (n+148), .id (n+166)]⟩ : Def)
  row_170 : defs[170]? = some (⟨.eor, [.id (n+151), .id (n+161)]⟩ : Def)
  row_171 : defs[171]? = some (⟨.sbc3, [.id (n+170), .id (n+161), .imm 1#64]⟩ : Def)
  row_174 : defs[174]? = some (⟨.sbc3C, [.id (n+170), .id (n+161), .imm 1#64]⟩ : Def)
  row_176 : defs[176]? = some (⟨.eor, [.id (n+156), .id (n+161)]⟩ : Def)
  row_177 : defs[177]? = some (⟨.sbc3, [.id (n+176), .id (n+161), .id (n+174)]⟩ : Def)
  row_178 : defs[178]? = some (⟨.eor, [.id (n+161), .id (n+148)]⟩ : Def)
  row_179 : defs[179]? = some (⟨.add3, [.id (n+71), .id (n+61), .imm 0#64]⟩ : Def)
  row_182 : defs[182]? = some (⟨.carry3, [.id (n+71), .id (n+61), .imm 0#64]⟩ : Def)
  row_184 : defs[184]? = some (⟨.add3, [.id (n+122), .id (n+66), .id (n+182)]⟩ : Def)
  row_187 : defs[187]? = some (⟨.carry3, [.id (n+122), .id (n+66), .id (n+182)]⟩ : Def)
  row_189 : defs[189]? = some (⟨.add3, [.id (n+128), .imm 0#64, .id (n+187)]⟩ : Def)
  row_192 : defs[192]? = some (⟨.carry3, [.id (n+128), .imm 0#64, .id (n+187)]⟩ : Def)
  row_194 : defs[194]? = some (⟨.add3, [.id (n+133), .imm 0#64, .id (n+192)]⟩ : Def)
  row_195 : defs[195]? = some (⟨.mul, [.id (n+163), .id (n+171)]⟩ : Def)
  row_196 : defs[196]? = some (⟨.umulh, [.id (n+163), .id (n+171)]⟩ : Def)
  row_197 : defs[197]? = some (⟨.mul, [.id (n+169), .id (n+177)]⟩ : Def)
  row_198 : defs[198]? = some (⟨.umulh, [.id (n+169), .id (n+177)]⟩ : Def)
  row_199 : defs[199]? = some (⟨.sbc3, [.id (n+169), .id (n+163), .imm 1#64]⟩ : Def)
  row_202 : defs[202]? = some (⟨.sbc3C, [.id (n+169), .id (n+163), .imm 1#64]⟩ : Def)
  row_204 : defs[204]? = some (⟨.cond 2#4, [.id (n+200), .id (n+201), .id (n+202), .id (n+203)]⟩ : Def)
  row_205 : defs[205]? = some (⟨.sub, [.imm 0#64, .id (n+199)]⟩ : Def)
  row_206 : defs[206]? = some (⟨.csel, [.id (n+204), .id (n+199), .id (n+205)]⟩ : Def)
  row_207 : defs[207]? = some (⟨.add, [.id (n+206), .imm 0#64]⟩ : Def)
  row_208 : defs[208]? = some (⟨.cselc 2#4, [.id (n+200), .id (n+201), .id (n+202), .id (n+203), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def)
  row_209 : defs[209]? = some (⟨.add3, [.id (n+197), .id (n+196), .imm 0#64]⟩ : Def)
  row_212 : defs[212]? = some (⟨.carry3, [.id (n+197), .id (n+196), .imm 0#64]⟩ : Def)
  row_214 : defs[214]? = some (⟨.add3, [.id (n+198), .imm 0#64, .id (n+212)]⟩ : Def)
  row_215 : defs[215]? = some (⟨.sbc3, [.id (n+171), .id (n+177), .imm 1#64]⟩ : Def)
  row_218 : defs[218]? = some (⟨.sbc3C, [.id (n+171), .id (n+177), .imm 1#64]⟩ : Def)
  row_220 : defs[220]? = some (⟨.cond 2#4, [.id (n+216), .id (n+217), .id (n+218), .id (n+219)]⟩ : Def)
  row_221 : defs[221]? = some (⟨.sub, [.imm 0#64, .id (n+215)]⟩ : Def)
  row_222 : defs[222]? = some (⟨.csel, [.id (n+220), .id (n+215), .id (n+221)]⟩ : Def)
  row_223 : defs[223]? = some (⟨.add, [.id (n+222), .imm 0#64]⟩ : Def)
  row_224 : defs[224]? = some (⟨.cond 2#4, [.id (n+216), .id (n+217), .id (n+218), .id (n+219)]⟩ : Def)
  row_225 : defs[225]? = some (⟨.not, [.id (n+208)]⟩ : Def)
  row_226 : defs[226]? = some (⟨.csel, [.id (n+224), .id (n+208), .id (n+225)]⟩ : Def)
  row_227 : defs[227]? = some (⟨.add, [.id (n+226), .imm 0#64]⟩ : Def)
  row_228 : defs[228]? = some (⟨.mul, [.id (n+207), .id (n+223)]⟩ : Def)
  row_229 : defs[229]? = some (⟨.umulh, [.id (n+207), .id (n+223)]⟩ : Def)
  row_230 : defs[230]? = some (⟨.add3, [.id (n+195), .id (n+209), .imm 0#64]⟩ : Def)
  row_233 : defs[233]? = some (⟨.carry3, [.id (n+195), .id (n+209), .imm 0#64]⟩ : Def)
  row_235 : defs[235]? = some (⟨.add3, [.id (n+209), .id (n+214), .id (n+233)]⟩ : Def)
  row_238 : defs[238]? = some (⟨.carry3, [.id (n+209), .id (n+214), .id (n+233)]⟩ : Def)
  row_240 : defs[240]? = some (⟨.add3, [.id (n+214), .imm 0#64, .id (n+238)]⟩ : Def)
  row_243 : defs[243]? = some (⟨.carry3, [.id (n+227), .imm 1#64, .imm 0#64]⟩ : Def)
  row_245 : defs[245]? = some (⟨.eor, [.id (n+228), .id (n+227)]⟩ : Def)
  row_246 : defs[246]? = some (⟨.add3, [.id (n+245), .id (n+230), .id (n+243)]⟩ : Def)
  row_249 : defs[249]? = some (⟨.carry3, [.id (n+245), .id (n+230), .id (n+243)]⟩ : Def)
  row_251 : defs[251]? = some (⟨.eor, [.id (n+229), .id (n+227)]⟩ : Def)
  row_252 : defs[252]? = some (⟨.add3, [.id (n+251), .id (n+235), .id (n+249)]⟩ : Def)
  row_255 : defs[255]? = some (⟨.carry3, [.id (n+251), .id (n+235), .id (n+249)]⟩ : Def)
  row_257 : defs[257]? = some (⟨.add3, [.id (n+240), .id (n+227), .id (n+255)]⟩ : Def)
  row_258 : defs[258]? = some (⟨.add3, [.id (n+179), .id (n+4), .imm 0#64]⟩ : Def)
  row_261 : defs[261]? = some (⟨.carry3, [.id (n+179), .id (n+4), .imm 0#64]⟩ : Def)
  row_263 : defs[263]? = some (⟨.add3, [.id (n+184), .id (n+55), .id (n+261)]⟩ : Def)
  row_266 : defs[266]? = some (⟨.carry3, [.id (n+184), .id (n+55), .id (n+261)]⟩ : Def)
  row_268 : defs[268]? = some (⟨.add3, [.id (n+189), .id (n+179), .id (n+266)]⟩ : Def)
  row_271 : defs[271]? = some (⟨.carry3, [.id (n+189), .id (n+179), .id (n+266)]⟩ : Def)
  row_273 : defs[273]? = some (⟨.add3, [.id (n+194), .id (n+184), .id (n+271)]⟩ : Def)
  row_276 : defs[276]? = some (⟨.carry3, [.id (n+194), .id (n+184), .id (n+271)]⟩ : Def)
  row_278 : defs[278]? = some (⟨.add3, [.id (n+189), .imm 0#64, .id (n+276)]⟩ : Def)
  row_281 : defs[281]? = some (⟨.carry3, [.id (n+189), .imm 0#64, .id (n+276)]⟩ : Def)
  row_283 : defs[283]? = some (⟨.add3, [.id (n+194), .imm 0#64, .id (n+281)]⟩ : Def)
  row_286 : defs[286]? = some (⟨.carry3, [.id (n+178), .imm 1#64, .imm 0#64]⟩ : Def)
  row_288 : defs[288]? = some (⟨.eor, [.id (n+195), .id (n+178)]⟩ : Def)
  row_289 : defs[289]? = some (⟨.add3, [.id (n+288), .id (n+258), .id (n+286)]⟩ : Def)
  row_292 : defs[292]? = some (⟨.carry3, [.id (n+288), .id (n+258), .id (n+286)]⟩ : Def)
  row_294 : defs[294]? = some (⟨.eor, [.id (n+246), .id (n+178)]⟩ : Def)
  row_295 : defs[295]? = some (⟨.add3, [.id (n+294), .id (n+263), .id (n+292)]⟩ : Def)
  row_298 : defs[298]? = some (⟨.carry3, [.id (n+294), .id (n+263), .id (n+292)]⟩ : Def)
  row_300 : defs[300]? = some (⟨.eor, [.id (n+252), .id (n+178)]⟩ : Def)
  row_301 : defs[301]? = some (⟨.add3, [.id (n+300), .id (n+268), .id (n+298)]⟩ : Def)
  row_304 : defs[304]? = some (⟨.carry3, [.id (n+300), .id (n+268), .id (n+298)]⟩ : Def)
  row_306 : defs[306]? = some (⟨.eor, [.id (n+257), .id (n+178)]⟩ : Def)
  row_307 : defs[307]? = some (⟨.add3, [.id (n+306), .id (n+273), .id (n+304)]⟩ : Def)
  row_310 : defs[310]? = some (⟨.carry3, [.id (n+306), .id (n+273), .id (n+304)]⟩ : Def)
  row_312 : defs[312]? = some (⟨.add3, [.id (n+278), .id (n+178), .id (n+310)]⟩ : Def)
  row_315 : defs[315]? = some (⟨.carry3, [.id (n+278), .id (n+178), .id (n+310)]⟩ : Def)
  row_317 : defs[317]? = some (⟨.add3, [.id (n+283), .id (n+178), .id (n+315)]⟩ : Def)
  row_318 : defs[318]? = some (⟨.const 977#64, []⟩ : Def)
  row_319 : defs[319]? = some (⟨.orr, [.id (n+318), .imm 4294967296#64]⟩ : Def)
  row_320 : defs[320]? = some (⟨.mul, [.id (n+319), .id (n+301)]⟩ : Def)
  row_321 : defs[321]? = some (⟨.umulh, [.id (n+319), .id (n+301)]⟩ : Def)
  row_322 : defs[322]? = some (⟨.and, [.id (n+307), .imm 4294967295#64]⟩ : Def)
  row_323 : defs[323]? = some (⟨.lsr 32, [.id (n+307)]⟩ : Def)
  row_324 : defs[324]? = some (⟨.mul, [.id (n+318), .id (n+322)]⟩ : Def)
  row_325 : defs[325]? = some (⟨.mul, [.id (n+318), .id (n+323)]⟩ : Def)
  row_326 : defs[326]? = some (⟨.add, [.id (n+325), .id (n+322)]⟩ : Def)
  row_327 : defs[327]? = some (⟨.add, [.id (n+326), .imm 0#64]⟩ : Def)
  row_328 : defs[328]? = some (⟨.lsl 32, [.id (n+327)]⟩ : Def)
  row_329 : defs[329]? = some (⟨.add3, [.id (n+324), .id (n+328), .imm 0#64]⟩ : Def)
  row_330 : defs[330]? = some (⟨.add, [.id (n+329), .imm 0#64]⟩ : Def)
  row_331 : defs[331]? = some (⟨.lsl 32, [.id (n+327)]⟩ : Def)
  row_333 : defs[333]? = some (⟨.add, [.id (n+332), .imm 0#64]⟩ : Def)
  row_334 : defs[334]? = some (⟨.lsl 32, [.id (n+327)]⟩ : Def)
  row_336 : defs[336]? = some (⟨.add, [.id (n+335), .imm 0#64]⟩ : Def)
  row_337 : defs[337]? = some (⟨.lsl 32, [.id (n+327)]⟩ : Def)
  row_338 : defs[338]? = some (⟨.carry3, [.id (n+324), .id (n+337), .imm 0#64]⟩ : Def)
  row_339 : defs[339]? = some (⟨.add, [.id (n+338), .imm 0#64]⟩ : Def)
  row_340 : defs[340]? = some (⟨.lsl 32, [.id (n+327)]⟩ : Def)
  row_342 : defs[342]? = some (⟨.add, [.id (n+341), .imm 0#64]⟩ : Def)
  row_343 : defs[343]? = some (⟨.lsr 32, [.id (n+327)]⟩ : Def)
  row_344 : defs[344]? = some (⟨.add3, [.id (n+323), .id (n+343), .id (n+339)]⟩ : Def)
  row_345 : defs[345]? = some (⟨.mul, [.id (n+319), .id (n+312)]⟩ : Def)
  row_346 : defs[346]? = some (⟨.umulh, [.id (n+319), .id (n+312)]⟩ : Def)
  row_347 : defs[347]? = some (⟨.and, [.id (n+317), .imm 4294967295#64]⟩ : Def)
  row_348 : defs[348]? = some (⟨.lsr 32, [.id (n+317)]⟩ : Def)
  row_349 : defs[349]? = some (⟨.mul, [.id (n+318), .id (n+347)]⟩ : Def)
  row_350 : defs[350]? = some (⟨.mul, [.id (n+318), .id (n+348)]⟩ : Def)
  row_351 : defs[351]? = some (⟨.add, [.id (n+350), .id (n+347)]⟩ : Def)
  row_352 : defs[352]? = some (⟨.add, [.id (n+351), .imm 0#64]⟩ : Def)
  row_353 : defs[353]? = some (⟨.lsl 32, [.id (n+352)]⟩ : Def)
  row_354 : defs[354]? = some (⟨.add3, [.id (n+349), .id (n+353), .imm 0#64]⟩ : Def)
  row_355 : defs[355]? = some (⟨.add, [.id (n+354), .imm 0#64]⟩ : Def)
  row_356 : defs[356]? = some (⟨.lsl 32, [.id (n+352)]⟩ : Def)
  row_358 : defs[358]? = some (⟨.add, [.id (n+357), .imm 0#64]⟩ : Def)
  row_359 : defs[359]? = some (⟨.lsl 32, [.id (n+352)]⟩ : Def)
  row_361 : defs[361]? = some (⟨.add, [.id (n+360), .imm 0#64]⟩ : Def)
  row_362 : defs[362]? = some (⟨.lsl 32, [.id (n+352)]⟩ : Def)
  row_363 : defs[363]? = some (⟨.carry3, [.id (n+349), .id (n+362), .imm 0#64]⟩ : Def)
  row_364 : defs[364]? = some (⟨.add, [.id (n+363), .imm 0#64]⟩ : Def)
  row_365 : defs[365]? = some (⟨.lsl 32, [.id (n+352)]⟩ : Def)
  row_367 : defs[367]? = some (⟨.add, [.id (n+366), .imm 0#64]⟩ : Def)
  row_368 : defs[368]? = some (⟨.lsr 32, [.id (n+352)]⟩ : Def)
  row_369 : defs[369]? = some (⟨.add3, [.id (n+348), .id (n+368), .id (n+364)]⟩ : Def)
  row_370 : defs[370]? = some (⟨.add3, [.id (n+4), .id (n+320), .imm 0#64]⟩ : Def)
  row_373 : defs[373]? = some (⟨.carry3, [.id (n+4), .id (n+320), .imm 0#64]⟩ : Def)
  row_375 : defs[375]? = some (⟨.add3, [.id (n+55), .id (n+330), .id (n+373)]⟩ : Def)
  row_378 : defs[378]? = some (⟨.carry3, [.id (n+55), .id (n+330), .id (n+373)]⟩ : Def)
  row_380 : defs[380]? = some (⟨.add3, [.id (n+289), .id (n+345), .id (n+378)]⟩ : Def)
  row_383 : defs[383]? = some (⟨.carry3, [.id (n+289), .id (n+345), .id (n+378)]⟩ : Def)
  row_385 : defs[385]? = some (⟨.add3, [.id (n+295), .id (n+355), .id (n+383)]⟩ : Def)
  row_388 : defs[388]? = some (⟨.carry3, [.id (n+295), .id (n+355), .id (n+383)]⟩ : Def)
  row_390 : defs[390]? = some (⟨.cond 2#4, [.id (n+386), .id (n+387), .id (n+388), .id (n+389)]⟩ : Def)
  row_391 : defs[391]? = some (⟨.add3, [.id (n+375), .id (n+321), .imm 0#64]⟩ : Def)
  row_394 : defs[394]? = some (⟨.carry3, [.id (n+375), .id (n+321), .imm 0#64]⟩ : Def)
  row_396 : defs[396]? = some (⟨.add3, [.id (n+380), .id (n+344), .id (n+394)]⟩ : Def)
  row_399 : defs[399]? = some (⟨.carry3, [.id (n+380), .id (n+344), .id (n+394)]⟩ : Def)
  row_401 : defs[401]? = some (⟨.add3, [.id (n+385), .id (n+346), .id (n+399)]⟩ : Def)
  row_404 : defs[404]? = some (⟨.carry3, [.id (n+385), .id (n+346), .id (n+399)]⟩ : Def)
  row_406 : defs[406]? = some (⟨.add3, [.id (n+390), .id (n+369), .id (n+404)]⟩ : Def)
  row_407 : defs[407]? = some (⟨.add, [.id (n+406), .imm 1#64]⟩ : Def)
  row_408 : defs[408]? = some (⟨.mul, [.id (n+318), .id (n+407)]⟩ : Def)
  row_409 : defs[409]? = some (⟨.lsr 32, [.id (n+407)]⟩ : Def)
  row_410 : defs[410]? = some (⟨.lsl 32, [.id (n+407)]⟩ : Def)
  row_411 : defs[411]? = some (⟨.add3, [.id (n+408), .id (n+410), .imm 0#64]⟩ : Def)
  row_412 : defs[412]? = some (⟨.add, [.id (n+411), .imm 0#64]⟩ : Def)
  row_413 : defs[413]? = some (⟨.lsl 32, [.id (n+407)]⟩ : Def)
  row_415 : defs[415]? = some (⟨.add, [.id (n+414), .imm 0#64]⟩ : Def)
  row_416 : defs[416]? = some (⟨.lsl 32, [.id (n+407)]⟩ : Def)
  row_418 : defs[418]? = some (⟨.add, [.id (n+417), .imm 0#64]⟩ : Def)
  row_419 : defs[419]? = some (⟨.lsl 32, [.id (n+407)]⟩ : Def)
  row_420 : defs[420]? = some (⟨.carry3, [.id (n+408), .id (n+419), .imm 0#64]⟩ : Def)
  row_421 : defs[421]? = some (⟨.add, [.id (n+420), .imm 0#64]⟩ : Def)
  row_422 : defs[422]? = some (⟨.lsl 32, [.id (n+407)]⟩ : Def)
  row_424 : defs[424]? = some (⟨.add, [.id (n+423), .imm 0#64]⟩ : Def)
  row_425 : defs[425]? = some (⟨.add3, [.imm 0#64, .id (n+409), .id (n+421)]⟩ : Def)
  row_426 : defs[426]? = some (⟨.add3, [.id (n+370), .id (n+412), .imm 0#64]⟩ : Def)
  row_429 : defs[429]? = some (⟨.carry3, [.id (n+370), .id (n+412), .imm 0#64]⟩ : Def)
  row_431 : defs[431]? = some (⟨.add3, [.id (n+391), .id (n+425), .id (n+429)]⟩ : Def)
  row_434 : defs[434]? = some (⟨.carry3, [.id (n+391), .id (n+425), .id (n+429)]⟩ : Def)
  row_436 : defs[436]? = some (⟨.add3, [.id (n+396), .imm 0#64, .id (n+434)]⟩ : Def)
  row_439 : defs[439]? = some (⟨.carry3, [.id (n+396), .imm 0#64, .id (n+434)]⟩ : Def)
  row_441 : defs[441]? = some (⟨.add3, [.id (n+401), .imm 0#64, .id (n+439)]⟩ : Def)
  row_444 : defs[444]? = some (⟨.carry3, [.id (n+401), .imm 0#64, .id (n+439)]⟩ : Def)
  row_446 : defs[446]? = some (⟨.cselc 3#4, [.id (n+442), .id (n+443), .id (n+444), .id (n+445), .id (n+319), .imm 0#64]⟩ : Def)
  row_447 : defs[447]? = some (⟨.sbc3, [.id (n+426), .id (n+446), .imm 1#64]⟩ : Def)
  row_450 : defs[450]? = some (⟨.sbc3C, [.id (n+426), .id (n+446), .imm 1#64]⟩ : Def)
  row_452 : defs[452]? = some (⟨.sbc3, [.id (n+431), .imm 0#64, .id (n+450)]⟩ : Def)
  row_455 : defs[455]? = some (⟨.sbc3C, [.id (n+431), .imm 0#64, .id (n+450)]⟩ : Def)
  row_457 : defs[457]? = some (⟨.sbc3, [.id (n+436), .imm 0#64, .id (n+455)]⟩ : Def)
  row_460 : defs[460]? = some (⟨.sbc3C, [.id (n+436), .imm 0#64, .id (n+455)]⟩ : Def)
  row_462 : defs[462]? = some (⟨.sbc3, [.id (n+441), .imm 0#64, .id (n+460)]⟩ : Def)

def compilerRows (n xs ys : Nat) : List Def := [
  inputWordDef (xs),
  inputWordDef (xs+8),
  inputWordDef (ys),
  inputWordDef (ys+8),
  (⟨.mul, [.id n, .id (n+2)]⟩ : Def),
  (⟨.umulh, [.id n, .id (n+2)]⟩ : Def),
  (⟨.mul, [.id (n+1), .id (n+3)]⟩ : Def),
  (⟨.umulh, [.id (n+1), .id (n+3)]⟩ : Def),
  (⟨.sbc3, [.id (n+1), .id n, .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+1), .id n, .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+1), .id n, .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+1), .id n, .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+1), .id n, .imm 1#64]⟩ : Def),
  (⟨.cond 2#4, [.id (n+9), .id (n+10), .id (n+11), .id (n+12)]⟩ : Def),
  (⟨.sub, [.imm 0#64, .id (n+8)]⟩ : Def),
  (⟨.csel, [.id (n+13), .id (n+8), .id (n+14)]⟩ : Def),
  (⟨.add, [.id (n+15), .imm 0#64]⟩ : Def),
  (⟨.cselc 2#4, [.id (n+9), .id (n+10), .id (n+11), .id (n+12), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def),
  (⟨.add3, [.id (n+6), .id (n+5), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+6), .id (n+5), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+6), .id (n+5), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+6), .id (n+5), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+6), .id (n+5), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+7), .imm 0#64, .id (n+21)]⟩ : Def),
  (⟨.sbc3, [.id (n+2), .id (n+3), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+2), .id (n+3), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+2), .id (n+3), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+2), .id (n+3), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+2), .id (n+3), .imm 1#64]⟩ : Def),
  (⟨.cond 2#4, [.id (n+25), .id (n+26), .id (n+27), .id (n+28)]⟩ : Def),
  (⟨.sub, [.imm 0#64, .id (n+24)]⟩ : Def),
  (⟨.csel, [.id (n+29), .id (n+24), .id (n+30)]⟩ : Def),
  (⟨.add, [.id (n+31), .imm 0#64]⟩ : Def),
  (⟨.cond 2#4, [.id (n+25), .id (n+26), .id (n+27), .id (n+28)]⟩ : Def),
  (⟨.not, [.id (n+17)]⟩ : Def),
  (⟨.csel, [.id (n+33), .id (n+17), .id (n+34)]⟩ : Def),
  (⟨.add, [.id (n+35), .imm 0#64]⟩ : Def),
  (⟨.mul, [.id (n+16), .id (n+32)]⟩ : Def),
  (⟨.umulh, [.id (n+16), .id (n+32)]⟩ : Def),
  (⟨.add3, [.id (n+4), .id (n+18), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+4), .id (n+18), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+4), .id (n+18), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+4), .id (n+18), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+4), .id (n+18), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+18), .id (n+23), .id (n+42)]⟩ : Def),
  (⟨.add3N, [.id (n+18), .id (n+23), .id (n+42)]⟩ : Def),
  (⟨.add3Z, [.id (n+18), .id (n+23), .id (n+42)]⟩ : Def),
  (⟨.carry3, [.id (n+18), .id (n+23), .id (n+42)]⟩ : Def),
  (⟨.ovf3, [.id (n+18), .id (n+23), .id (n+42)]⟩ : Def),
  (⟨.add3, [.id (n+23), .imm 0#64, .id (n+47)]⟩ : Def),
  (⟨.add3N, [.id (n+36), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+36), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+36), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+36), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.eor, [.id (n+37), .id (n+36)]⟩ : Def),
  (⟨.add3, [.id (n+54), .id (n+39), .id (n+52)]⟩ : Def),
  (⟨.add3N, [.id (n+54), .id (n+39), .id (n+52)]⟩ : Def),
  (⟨.add3Z, [.id (n+54), .id (n+39), .id (n+52)]⟩ : Def),
  (⟨.carry3, [.id (n+54), .id (n+39), .id (n+52)]⟩ : Def),
  (⟨.ovf3, [.id (n+54), .id (n+39), .id (n+52)]⟩ : Def),
  (⟨.eor, [.id (n+38), .id (n+36)]⟩ : Def),
  (⟨.add3, [.id (n+60), .id (n+44), .id (n+58)]⟩ : Def),
  (⟨.add3N, [.id (n+60), .id (n+44), .id (n+58)]⟩ : Def),
  (⟨.add3Z, [.id (n+60), .id (n+44), .id (n+58)]⟩ : Def),
  (⟨.carry3, [.id (n+60), .id (n+44), .id (n+58)]⟩ : Def),
  (⟨.ovf3, [.id (n+60), .id (n+44), .id (n+58)]⟩ : Def),
  (⟨.add3, [.id (n+49), .id (n+36), .id (n+64)]⟩ : Def),
  inputWordDef (xs+16),
  inputWordDef (xs+24),
  inputWordDef (ys+16),
  inputWordDef (ys+24),
  (⟨.mul, [.id (n+67), .id (n+69)]⟩ : Def),
  (⟨.umulh, [.id (n+67), .id (n+69)]⟩ : Def),
  (⟨.mul, [.id (n+68), .id (n+70)]⟩ : Def),
  (⟨.umulh, [.id (n+68), .id (n+70)]⟩ : Def),
  (⟨.sbc3, [.id (n+68), .id (n+67), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+68), .id (n+67), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+68), .id (n+67), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+68), .id (n+67), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+68), .id (n+67), .imm 1#64]⟩ : Def),
  (⟨.cond 2#4, [.id (n+76), .id (n+77), .id (n+78), .id (n+79)]⟩ : Def),
  (⟨.sub, [.imm 0#64, .id (n+75)]⟩ : Def),
  (⟨.csel, [.id (n+80), .id (n+75), .id (n+81)]⟩ : Def),
  (⟨.add, [.id (n+82), .imm 0#64]⟩ : Def),
  (⟨.cselc 2#4, [.id (n+76), .id (n+77), .id (n+78), .id (n+79), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def),
  (⟨.add3, [.id (n+73), .id (n+72), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+73), .id (n+72), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+73), .id (n+72), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+73), .id (n+72), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+73), .id (n+72), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+74), .imm 0#64, .id (n+88)]⟩ : Def),
  (⟨.sbc3, [.id (n+69), .id (n+70), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+69), .id (n+70), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+69), .id (n+70), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+69), .id (n+70), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+69), .id (n+70), .imm 1#64]⟩ : Def),
  (⟨.cond 2#4, [.id (n+92), .id (n+93), .id (n+94), .id (n+95)]⟩ : Def),
  (⟨.sub, [.imm 0#64, .id (n+91)]⟩ : Def),
  (⟨.csel, [.id (n+96), .id (n+91), .id (n+97)]⟩ : Def),
  (⟨.add, [.id (n+98), .imm 0#64]⟩ : Def),
  (⟨.cond 2#4, [.id (n+92), .id (n+93), .id (n+94), .id (n+95)]⟩ : Def),
  (⟨.not, [.id (n+84)]⟩ : Def),
  (⟨.csel, [.id (n+100), .id (n+84), .id (n+101)]⟩ : Def),
  (⟨.add, [.id (n+102), .imm 0#64]⟩ : Def),
  (⟨.mul, [.id (n+83), .id (n+99)]⟩ : Def),
  (⟨.umulh, [.id (n+83), .id (n+99)]⟩ : Def),
  (⟨.add3, [.id (n+71), .id (n+85), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+71), .id (n+85), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+71), .id (n+85), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+71), .id (n+85), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+71), .id (n+85), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+85), .id (n+90), .id (n+109)]⟩ : Def),
  (⟨.add3N, [.id (n+85), .id (n+90), .id (n+109)]⟩ : Def),
  (⟨.add3Z, [.id (n+85), .id (n+90), .id (n+109)]⟩ : Def),
  (⟨.carry3, [.id (n+85), .id (n+90), .id (n+109)]⟩ : Def),
  (⟨.ovf3, [.id (n+85), .id (n+90), .id (n+109)]⟩ : Def),
  (⟨.add3, [.id (n+90), .imm 0#64, .id (n+114)]⟩ : Def),
  (⟨.add3N, [.id (n+103), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+103), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+103), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+103), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.eor, [.id (n+104), .id (n+103)]⟩ : Def),
  (⟨.add3, [.id (n+121), .id (n+106), .id (n+119)]⟩ : Def),
  (⟨.add3N, [.id (n+121), .id (n+106), .id (n+119)]⟩ : Def),
  (⟨.add3Z, [.id (n+121), .id (n+106), .id (n+119)]⟩ : Def),
  (⟨.carry3, [.id (n+121), .id (n+106), .id (n+119)]⟩ : Def),
  (⟨.ovf3, [.id (n+121), .id (n+106), .id (n+119)]⟩ : Def),
  (⟨.eor, [.id (n+105), .id (n+103)]⟩ : Def),
  (⟨.add3, [.id (n+127), .id (n+111), .id (n+125)]⟩ : Def),
  (⟨.add3N, [.id (n+127), .id (n+111), .id (n+125)]⟩ : Def),
  (⟨.add3Z, [.id (n+127), .id (n+111), .id (n+125)]⟩ : Def),
  (⟨.carry3, [.id (n+127), .id (n+111), .id (n+125)]⟩ : Def),
  (⟨.ovf3, [.id (n+127), .id (n+111), .id (n+125)]⟩ : Def),
  (⟨.add3, [.id (n+116), .id (n+103), .id (n+131)]⟩ : Def),
  inputWordDef (xs+16),
  inputWordDef (xs+24),
  inputWordDef (xs),
  inputWordDef (xs+8),
  (⟨.sbc3, [.id (n+134), .id (n+136), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+134), .id (n+136), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+134), .id (n+136), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+134), .id (n+136), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+134), .id (n+136), .imm 1#64]⟩ : Def),
  (⟨.sbc3, [.id (n+135), .id (n+137), .id (n+141)]⟩ : Def),
  (⟨.sbc3N, [.id (n+135), .id (n+137), .id (n+141)]⟩ : Def),
  (⟨.sbc3Z, [.id (n+135), .id (n+137), .id (n+141)]⟩ : Def),
  (⟨.sbc3C, [.id (n+135), .id (n+137), .id (n+141)]⟩ : Def),
  (⟨.sbc3V, [.id (n+135), .id (n+137), .id (n+141)]⟩ : Def),
  (⟨.cselc 2#4, [.id (n+144), .id (n+145), .id (n+146), .id (n+147), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def),
  inputWordDef (ys),
  inputWordDef (ys+8),
  (⟨.sbc3, [.id (n+149), .id (n+69), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+149), .id (n+69), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+149), .id (n+69), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+149), .id (n+69), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+149), .id (n+69), .imm 1#64]⟩ : Def),
  (⟨.sbc3, [.id (n+150), .id (n+70), .id (n+154)]⟩ : Def),
  (⟨.sbc3N, [.id (n+150), .id (n+70), .id (n+154)]⟩ : Def),
  (⟨.sbc3Z, [.id (n+150), .id (n+70), .id (n+154)]⟩ : Def),
  (⟨.sbc3C, [.id (n+150), .id (n+70), .id (n+154)]⟩ : Def),
  (⟨.sbc3V, [.id (n+150), .id (n+70), .id (n+154)]⟩ : Def),
  (⟨.cselc 2#4, [.id (n+157), .id (n+158), .id (n+159), .id (n+160), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def),
  (⟨.eor, [.id (n+138), .id (n+148)]⟩ : Def),
  (⟨.sbc3, [.id (n+162), .id (n+148), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+162), .id (n+148), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+162), .id (n+148), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+162), .id (n+148), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+162), .id (n+148), .imm 1#64]⟩ : Def),
  (⟨.eor, [.id (n+143), .id (n+148)]⟩ : Def),
  (⟨.sbc3, [.id (n+168), .id (n+148), .id (n+166)]⟩ : Def),
  (⟨.eor, [.id (n+151), .id (n+161)]⟩ : Def),
  (⟨.sbc3, [.id (n+170), .id (n+161), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+170), .id (n+161), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+170), .id (n+161), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+170), .id (n+161), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+170), .id (n+161), .imm 1#64]⟩ : Def),
  (⟨.eor, [.id (n+156), .id (n+161)]⟩ : Def),
  (⟨.sbc3, [.id (n+176), .id (n+161), .id (n+174)]⟩ : Def),
  (⟨.eor, [.id (n+161), .id (n+148)]⟩ : Def),
  (⟨.add3, [.id (n+71), .id (n+61), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+71), .id (n+61), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+71), .id (n+61), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+71), .id (n+61), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+71), .id (n+61), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+122), .id (n+66), .id (n+182)]⟩ : Def),
  (⟨.add3N, [.id (n+122), .id (n+66), .id (n+182)]⟩ : Def),
  (⟨.add3Z, [.id (n+122), .id (n+66), .id (n+182)]⟩ : Def),
  (⟨.carry3, [.id (n+122), .id (n+66), .id (n+182)]⟩ : Def),
  (⟨.ovf3, [.id (n+122), .id (n+66), .id (n+182)]⟩ : Def),
  (⟨.add3, [.id (n+128), .imm 0#64, .id (n+187)]⟩ : Def),
  (⟨.add3N, [.id (n+128), .imm 0#64, .id (n+187)]⟩ : Def),
  (⟨.add3Z, [.id (n+128), .imm 0#64, .id (n+187)]⟩ : Def),
  (⟨.carry3, [.id (n+128), .imm 0#64, .id (n+187)]⟩ : Def),
  (⟨.ovf3, [.id (n+128), .imm 0#64, .id (n+187)]⟩ : Def),
  (⟨.add3, [.id (n+133), .imm 0#64, .id (n+192)]⟩ : Def),
  (⟨.mul, [.id (n+163), .id (n+171)]⟩ : Def),
  (⟨.umulh, [.id (n+163), .id (n+171)]⟩ : Def),
  (⟨.mul, [.id (n+169), .id (n+177)]⟩ : Def),
  (⟨.umulh, [.id (n+169), .id (n+177)]⟩ : Def),
  (⟨.sbc3, [.id (n+169), .id (n+163), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+169), .id (n+163), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+169), .id (n+163), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+169), .id (n+163), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+169), .id (n+163), .imm 1#64]⟩ : Def),
  (⟨.cond 2#4, [.id (n+200), .id (n+201), .id (n+202), .id (n+203)]⟩ : Def),
  (⟨.sub, [.imm 0#64, .id (n+199)]⟩ : Def),
  (⟨.csel, [.id (n+204), .id (n+199), .id (n+205)]⟩ : Def),
  (⟨.add, [.id (n+206), .imm 0#64]⟩ : Def),
  (⟨.cselc 2#4, [.id (n+200), .id (n+201), .id (n+202), .id (n+203), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def),
  (⟨.add3, [.id (n+197), .id (n+196), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+197), .id (n+196), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+197), .id (n+196), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+197), .id (n+196), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+197), .id (n+196), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+198), .imm 0#64, .id (n+212)]⟩ : Def),
  (⟨.sbc3, [.id (n+171), .id (n+177), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+171), .id (n+177), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+171), .id (n+177), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+171), .id (n+177), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+171), .id (n+177), .imm 1#64]⟩ : Def),
  (⟨.cond 2#4, [.id (n+216), .id (n+217), .id (n+218), .id (n+219)]⟩ : Def),
  (⟨.sub, [.imm 0#64, .id (n+215)]⟩ : Def),
  (⟨.csel, [.id (n+220), .id (n+215), .id (n+221)]⟩ : Def),
  (⟨.add, [.id (n+222), .imm 0#64]⟩ : Def),
  (⟨.cond 2#4, [.id (n+216), .id (n+217), .id (n+218), .id (n+219)]⟩ : Def),
  (⟨.not, [.id (n+208)]⟩ : Def),
  (⟨.csel, [.id (n+224), .id (n+208), .id (n+225)]⟩ : Def),
  (⟨.add, [.id (n+226), .imm 0#64]⟩ : Def),
  (⟨.mul, [.id (n+207), .id (n+223)]⟩ : Def),
  (⟨.umulh, [.id (n+207), .id (n+223)]⟩ : Def),
  (⟨.add3, [.id (n+195), .id (n+209), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+195), .id (n+209), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+195), .id (n+209), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+195), .id (n+209), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+195), .id (n+209), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+209), .id (n+214), .id (n+233)]⟩ : Def),
  (⟨.add3N, [.id (n+209), .id (n+214), .id (n+233)]⟩ : Def),
  (⟨.add3Z, [.id (n+209), .id (n+214), .id (n+233)]⟩ : Def),
  (⟨.carry3, [.id (n+209), .id (n+214), .id (n+233)]⟩ : Def),
  (⟨.ovf3, [.id (n+209), .id (n+214), .id (n+233)]⟩ : Def),
  (⟨.add3, [.id (n+214), .imm 0#64, .id (n+238)]⟩ : Def),
  (⟨.add3N, [.id (n+227), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+227), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+227), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+227), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.eor, [.id (n+228), .id (n+227)]⟩ : Def),
  (⟨.add3, [.id (n+245), .id (n+230), .id (n+243)]⟩ : Def),
  (⟨.add3N, [.id (n+245), .id (n+230), .id (n+243)]⟩ : Def),
  (⟨.add3Z, [.id (n+245), .id (n+230), .id (n+243)]⟩ : Def),
  (⟨.carry3, [.id (n+245), .id (n+230), .id (n+243)]⟩ : Def),
  (⟨.ovf3, [.id (n+245), .id (n+230), .id (n+243)]⟩ : Def),
  (⟨.eor, [.id (n+229), .id (n+227)]⟩ : Def),
  (⟨.add3, [.id (n+251), .id (n+235), .id (n+249)]⟩ : Def),
  (⟨.add3N, [.id (n+251), .id (n+235), .id (n+249)]⟩ : Def),
  (⟨.add3Z, [.id (n+251), .id (n+235), .id (n+249)]⟩ : Def),
  (⟨.carry3, [.id (n+251), .id (n+235), .id (n+249)]⟩ : Def),
  (⟨.ovf3, [.id (n+251), .id (n+235), .id (n+249)]⟩ : Def),
  (⟨.add3, [.id (n+240), .id (n+227), .id (n+255)]⟩ : Def),
  (⟨.add3, [.id (n+179), .id (n+4), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+179), .id (n+4), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+179), .id (n+4), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+179), .id (n+4), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+179), .id (n+4), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+184), .id (n+55), .id (n+261)]⟩ : Def),
  (⟨.add3N, [.id (n+184), .id (n+55), .id (n+261)]⟩ : Def),
  (⟨.add3Z, [.id (n+184), .id (n+55), .id (n+261)]⟩ : Def),
  (⟨.carry3, [.id (n+184), .id (n+55), .id (n+261)]⟩ : Def),
  (⟨.ovf3, [.id (n+184), .id (n+55), .id (n+261)]⟩ : Def),
  (⟨.add3, [.id (n+189), .id (n+179), .id (n+266)]⟩ : Def),
  (⟨.add3N, [.id (n+189), .id (n+179), .id (n+266)]⟩ : Def),
  (⟨.add3Z, [.id (n+189), .id (n+179), .id (n+266)]⟩ : Def),
  (⟨.carry3, [.id (n+189), .id (n+179), .id (n+266)]⟩ : Def),
  (⟨.ovf3, [.id (n+189), .id (n+179), .id (n+266)]⟩ : Def),
  (⟨.add3, [.id (n+194), .id (n+184), .id (n+271)]⟩ : Def),
  (⟨.add3N, [.id (n+194), .id (n+184), .id (n+271)]⟩ : Def),
  (⟨.add3Z, [.id (n+194), .id (n+184), .id (n+271)]⟩ : Def),
  (⟨.carry3, [.id (n+194), .id (n+184), .id (n+271)]⟩ : Def),
  (⟨.ovf3, [.id (n+194), .id (n+184), .id (n+271)]⟩ : Def),
  (⟨.add3, [.id (n+189), .imm 0#64, .id (n+276)]⟩ : Def),
  (⟨.add3N, [.id (n+189), .imm 0#64, .id (n+276)]⟩ : Def),
  (⟨.add3Z, [.id (n+189), .imm 0#64, .id (n+276)]⟩ : Def),
  (⟨.carry3, [.id (n+189), .imm 0#64, .id (n+276)]⟩ : Def),
  (⟨.ovf3, [.id (n+189), .imm 0#64, .id (n+276)]⟩ : Def),
  (⟨.add3, [.id (n+194), .imm 0#64, .id (n+281)]⟩ : Def),
  (⟨.add3N, [.id (n+178), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+178), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+178), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+178), .imm 1#64, .imm 0#64]⟩ : Def),
  (⟨.eor, [.id (n+195), .id (n+178)]⟩ : Def),
  (⟨.add3, [.id (n+288), .id (n+258), .id (n+286)]⟩ : Def),
  (⟨.add3N, [.id (n+288), .id (n+258), .id (n+286)]⟩ : Def),
  (⟨.add3Z, [.id (n+288), .id (n+258), .id (n+286)]⟩ : Def),
  (⟨.carry3, [.id (n+288), .id (n+258), .id (n+286)]⟩ : Def),
  (⟨.ovf3, [.id (n+288), .id (n+258), .id (n+286)]⟩ : Def),
  (⟨.eor, [.id (n+246), .id (n+178)]⟩ : Def),
  (⟨.add3, [.id (n+294), .id (n+263), .id (n+292)]⟩ : Def),
  (⟨.add3N, [.id (n+294), .id (n+263), .id (n+292)]⟩ : Def),
  (⟨.add3Z, [.id (n+294), .id (n+263), .id (n+292)]⟩ : Def),
  (⟨.carry3, [.id (n+294), .id (n+263), .id (n+292)]⟩ : Def),
  (⟨.ovf3, [.id (n+294), .id (n+263), .id (n+292)]⟩ : Def),
  (⟨.eor, [.id (n+252), .id (n+178)]⟩ : Def),
  (⟨.add3, [.id (n+300), .id (n+268), .id (n+298)]⟩ : Def),
  (⟨.add3N, [.id (n+300), .id (n+268), .id (n+298)]⟩ : Def),
  (⟨.add3Z, [.id (n+300), .id (n+268), .id (n+298)]⟩ : Def),
  (⟨.carry3, [.id (n+300), .id (n+268), .id (n+298)]⟩ : Def),
  (⟨.ovf3, [.id (n+300), .id (n+268), .id (n+298)]⟩ : Def),
  (⟨.eor, [.id (n+257), .id (n+178)]⟩ : Def),
  (⟨.add3, [.id (n+306), .id (n+273), .id (n+304)]⟩ : Def),
  (⟨.add3N, [.id (n+306), .id (n+273), .id (n+304)]⟩ : Def),
  (⟨.add3Z, [.id (n+306), .id (n+273), .id (n+304)]⟩ : Def),
  (⟨.carry3, [.id (n+306), .id (n+273), .id (n+304)]⟩ : Def),
  (⟨.ovf3, [.id (n+306), .id (n+273), .id (n+304)]⟩ : Def),
  (⟨.add3, [.id (n+278), .id (n+178), .id (n+310)]⟩ : Def),
  (⟨.add3N, [.id (n+278), .id (n+178), .id (n+310)]⟩ : Def),
  (⟨.add3Z, [.id (n+278), .id (n+178), .id (n+310)]⟩ : Def),
  (⟨.carry3, [.id (n+278), .id (n+178), .id (n+310)]⟩ : Def),
  (⟨.ovf3, [.id (n+278), .id (n+178), .id (n+310)]⟩ : Def),
  (⟨.add3, [.id (n+283), .id (n+178), .id (n+315)]⟩ : Def),
  (⟨.const 977#64, []⟩ : Def),
  (⟨.orr, [.id (n+318), .imm 4294967296#64]⟩ : Def),
  (⟨.mul, [.id (n+319), .id (n+301)]⟩ : Def),
  (⟨.umulh, [.id (n+319), .id (n+301)]⟩ : Def),
  (⟨.and, [.id (n+307), .imm 4294967295#64]⟩ : Def),
  (⟨.lsr 32, [.id (n+307)]⟩ : Def),
  (⟨.mul, [.id (n+318), .id (n+322)]⟩ : Def),
  (⟨.mul, [.id (n+318), .id (n+323)]⟩ : Def),
  (⟨.add, [.id (n+325), .id (n+322)]⟩ : Def),
  (⟨.add, [.id (n+326), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+327)]⟩ : Def),
  (⟨.add3, [.id (n+324), .id (n+328), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+329), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+327)]⟩ : Def),
  (⟨.add3N, [.id (n+324), .id (n+331), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+332), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+327)]⟩ : Def),
  (⟨.add3Z, [.id (n+324), .id (n+334), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+335), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+327)]⟩ : Def),
  (⟨.carry3, [.id (n+324), .id (n+337), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+338), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+327)]⟩ : Def),
  (⟨.ovf3, [.id (n+324), .id (n+340), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+341), .imm 0#64]⟩ : Def),
  (⟨.lsr 32, [.id (n+327)]⟩ : Def),
  (⟨.add3, [.id (n+323), .id (n+343), .id (n+339)]⟩ : Def),
  (⟨.mul, [.id (n+319), .id (n+312)]⟩ : Def),
  (⟨.umulh, [.id (n+319), .id (n+312)]⟩ : Def),
  (⟨.and, [.id (n+317), .imm 4294967295#64]⟩ : Def),
  (⟨.lsr 32, [.id (n+317)]⟩ : Def),
  (⟨.mul, [.id (n+318), .id (n+347)]⟩ : Def),
  (⟨.mul, [.id (n+318), .id (n+348)]⟩ : Def),
  (⟨.add, [.id (n+350), .id (n+347)]⟩ : Def),
  (⟨.add, [.id (n+351), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+352)]⟩ : Def),
  (⟨.add3, [.id (n+349), .id (n+353), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+354), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+352)]⟩ : Def),
  (⟨.add3N, [.id (n+349), .id (n+356), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+357), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+352)]⟩ : Def),
  (⟨.add3Z, [.id (n+349), .id (n+359), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+360), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+352)]⟩ : Def),
  (⟨.carry3, [.id (n+349), .id (n+362), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+363), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+352)]⟩ : Def),
  (⟨.ovf3, [.id (n+349), .id (n+365), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+366), .imm 0#64]⟩ : Def),
  (⟨.lsr 32, [.id (n+352)]⟩ : Def),
  (⟨.add3, [.id (n+348), .id (n+368), .id (n+364)]⟩ : Def),
  (⟨.add3, [.id (n+4), .id (n+320), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+4), .id (n+320), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+4), .id (n+320), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+4), .id (n+320), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+4), .id (n+320), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+55), .id (n+330), .id (n+373)]⟩ : Def),
  (⟨.add3N, [.id (n+55), .id (n+330), .id (n+373)]⟩ : Def),
  (⟨.add3Z, [.id (n+55), .id (n+330), .id (n+373)]⟩ : Def),
  (⟨.carry3, [.id (n+55), .id (n+330), .id (n+373)]⟩ : Def),
  (⟨.ovf3, [.id (n+55), .id (n+330), .id (n+373)]⟩ : Def),
  (⟨.add3, [.id (n+289), .id (n+345), .id (n+378)]⟩ : Def),
  (⟨.add3N, [.id (n+289), .id (n+345), .id (n+378)]⟩ : Def),
  (⟨.add3Z, [.id (n+289), .id (n+345), .id (n+378)]⟩ : Def),
  (⟨.carry3, [.id (n+289), .id (n+345), .id (n+378)]⟩ : Def),
  (⟨.ovf3, [.id (n+289), .id (n+345), .id (n+378)]⟩ : Def),
  (⟨.add3, [.id (n+295), .id (n+355), .id (n+383)]⟩ : Def),
  (⟨.add3N, [.id (n+295), .id (n+355), .id (n+383)]⟩ : Def),
  (⟨.add3Z, [.id (n+295), .id (n+355), .id (n+383)]⟩ : Def),
  (⟨.carry3, [.id (n+295), .id (n+355), .id (n+383)]⟩ : Def),
  (⟨.ovf3, [.id (n+295), .id (n+355), .id (n+383)]⟩ : Def),
  (⟨.cond 2#4, [.id (n+386), .id (n+387), .id (n+388), .id (n+389)]⟩ : Def),
  (⟨.add3, [.id (n+375), .id (n+321), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+375), .id (n+321), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+375), .id (n+321), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+375), .id (n+321), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+375), .id (n+321), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+380), .id (n+344), .id (n+394)]⟩ : Def),
  (⟨.add3N, [.id (n+380), .id (n+344), .id (n+394)]⟩ : Def),
  (⟨.add3Z, [.id (n+380), .id (n+344), .id (n+394)]⟩ : Def),
  (⟨.carry3, [.id (n+380), .id (n+344), .id (n+394)]⟩ : Def),
  (⟨.ovf3, [.id (n+380), .id (n+344), .id (n+394)]⟩ : Def),
  (⟨.add3, [.id (n+385), .id (n+346), .id (n+399)]⟩ : Def),
  (⟨.add3N, [.id (n+385), .id (n+346), .id (n+399)]⟩ : Def),
  (⟨.add3Z, [.id (n+385), .id (n+346), .id (n+399)]⟩ : Def),
  (⟨.carry3, [.id (n+385), .id (n+346), .id (n+399)]⟩ : Def),
  (⟨.ovf3, [.id (n+385), .id (n+346), .id (n+399)]⟩ : Def),
  (⟨.add3, [.id (n+390), .id (n+369), .id (n+404)]⟩ : Def),
  (⟨.add, [.id (n+406), .imm 1#64]⟩ : Def),
  (⟨.mul, [.id (n+318), .id (n+407)]⟩ : Def),
  (⟨.lsr 32, [.id (n+407)]⟩ : Def),
  (⟨.lsl 32, [.id (n+407)]⟩ : Def),
  (⟨.add3, [.id (n+408), .id (n+410), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+411), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+407)]⟩ : Def),
  (⟨.add3N, [.id (n+408), .id (n+413), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+414), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+407)]⟩ : Def),
  (⟨.add3Z, [.id (n+408), .id (n+416), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+417), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+407)]⟩ : Def),
  (⟨.carry3, [.id (n+408), .id (n+419), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+420), .imm 0#64]⟩ : Def),
  (⟨.lsl 32, [.id (n+407)]⟩ : Def),
  (⟨.ovf3, [.id (n+408), .id (n+422), .imm 0#64]⟩ : Def),
  (⟨.add, [.id (n+423), .imm 0#64]⟩ : Def),
  (⟨.add3, [.imm 0#64, .id (n+409), .id (n+421)]⟩ : Def),
  (⟨.add3, [.id (n+370), .id (n+412), .imm 0#64]⟩ : Def),
  (⟨.add3N, [.id (n+370), .id (n+412), .imm 0#64]⟩ : Def),
  (⟨.add3Z, [.id (n+370), .id (n+412), .imm 0#64]⟩ : Def),
  (⟨.carry3, [.id (n+370), .id (n+412), .imm 0#64]⟩ : Def),
  (⟨.ovf3, [.id (n+370), .id (n+412), .imm 0#64]⟩ : Def),
  (⟨.add3, [.id (n+391), .id (n+425), .id (n+429)]⟩ : Def),
  (⟨.add3N, [.id (n+391), .id (n+425), .id (n+429)]⟩ : Def),
  (⟨.add3Z, [.id (n+391), .id (n+425), .id (n+429)]⟩ : Def),
  (⟨.carry3, [.id (n+391), .id (n+425), .id (n+429)]⟩ : Def),
  (⟨.ovf3, [.id (n+391), .id (n+425), .id (n+429)]⟩ : Def),
  (⟨.add3, [.id (n+396), .imm 0#64, .id (n+434)]⟩ : Def),
  (⟨.add3N, [.id (n+396), .imm 0#64, .id (n+434)]⟩ : Def),
  (⟨.add3Z, [.id (n+396), .imm 0#64, .id (n+434)]⟩ : Def),
  (⟨.carry3, [.id (n+396), .imm 0#64, .id (n+434)]⟩ : Def),
  (⟨.ovf3, [.id (n+396), .imm 0#64, .id (n+434)]⟩ : Def),
  (⟨.add3, [.id (n+401), .imm 0#64, .id (n+439)]⟩ : Def),
  (⟨.add3N, [.id (n+401), .imm 0#64, .id (n+439)]⟩ : Def),
  (⟨.add3Z, [.id (n+401), .imm 0#64, .id (n+439)]⟩ : Def),
  (⟨.carry3, [.id (n+401), .imm 0#64, .id (n+439)]⟩ : Def),
  (⟨.ovf3, [.id (n+401), .imm 0#64, .id (n+439)]⟩ : Def),
  (⟨.cselc 3#4, [.id (n+442), .id (n+443), .id (n+444), .id (n+445), .id (n+319), .imm 0#64]⟩ : Def),
  (⟨.sbc3, [.id (n+426), .id (n+446), .imm 1#64]⟩ : Def),
  (⟨.sbc3N, [.id (n+426), .id (n+446), .imm 1#64]⟩ : Def),
  (⟨.sbc3Z, [.id (n+426), .id (n+446), .imm 1#64]⟩ : Def),
  (⟨.sbc3C, [.id (n+426), .id (n+446), .imm 1#64]⟩ : Def),
  (⟨.sbc3V, [.id (n+426), .id (n+446), .imm 1#64]⟩ : Def),
  (⟨.sbc3, [.id (n+431), .imm 0#64, .id (n+450)]⟩ : Def),
  (⟨.sbc3N, [.id (n+431), .imm 0#64, .id (n+450)]⟩ : Def),
  (⟨.sbc3Z, [.id (n+431), .imm 0#64, .id (n+450)]⟩ : Def),
  (⟨.sbc3C, [.id (n+431), .imm 0#64, .id (n+450)]⟩ : Def),
  (⟨.sbc3V, [.id (n+431), .imm 0#64, .id (n+450)]⟩ : Def),
  (⟨.sbc3, [.id (n+436), .imm 0#64, .id (n+455)]⟩ : Def),
  (⟨.sbc3N, [.id (n+436), .imm 0#64, .id (n+455)]⟩ : Def),
  (⟨.sbc3Z, [.id (n+436), .imm 0#64, .id (n+455)]⟩ : Def),
  (⟨.sbc3C, [.id (n+436), .imm 0#64, .id (n+455)]⟩ : Def),
  (⟨.sbc3V, [.id (n+436), .imm 0#64, .id (n+455)]⟩ : Def),
  (⟨.sbc3, [.id (n+441), .imm 0#64, .id (n+460)]⟩ : Def)]

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
      (TableEval.evalDefs_row inputs defs 6 (⟨.mul, [.id (n+1), .id (n+3)]⟩ : Def) pos.row_6
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 7 (⟨.umulh, [.id (n+1), .id (n+3)]⟩ : Def) pos.row_7
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 8 (⟨.sbc3, [.id (n+1), .id n, .imm 1#64]⟩ : Def) pos.row_8
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 11 (⟨.sbc3C, [.id (n+1), .id n, .imm 1#64]⟩ : Def) pos.row_11
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 13 (⟨.cond 2#4, [.id (n+9), .id (n+10), .id (n+11), .id (n+12)]⟩ : Def) pos.row_13
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 14 (⟨.sub, [.imm 0#64, .id (n+8)]⟩ : Def) pos.row_14
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 15 (⟨.csel, [.id (n+13), .id (n+8), .id (n+14)]⟩ : Def) pos.row_15
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 16 (⟨.add, [.id (n+15), .imm 0#64]⟩ : Def) pos.row_16
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 17 (⟨.cselc 2#4, [.id (n+9), .id (n+10), .id (n+11), .id (n+12), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def) pos.row_17
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 18 (⟨.add3, [.id (n+6), .id (n+5), .imm 0#64]⟩ : Def) pos.row_18
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 21 (⟨.carry3, [.id (n+6), .id (n+5), .imm 0#64]⟩ : Def) pos.row_21
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 23 (⟨.add3, [.id (n+7), .imm 0#64, .id (n+21)]⟩ : Def) pos.row_23
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 24 (⟨.sbc3, [.id (n+2), .id (n+3), .imm 1#64]⟩ : Def) pos.row_24
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 27 (⟨.sbc3C, [.id (n+2), .id (n+3), .imm 1#64]⟩ : Def) pos.row_27
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 29 (⟨.cond 2#4, [.id (n+25), .id (n+26), .id (n+27), .id (n+28)]⟩ : Def) pos.row_29
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 30 (⟨.sub, [.imm 0#64, .id (n+24)]⟩ : Def) pos.row_30
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 31 (⟨.csel, [.id (n+29), .id (n+24), .id (n+30)]⟩ : Def) pos.row_31
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 32 (⟨.add, [.id (n+31), .imm 0#64]⟩ : Def) pos.row_32
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 33 (⟨.cond 2#4, [.id (n+25), .id (n+26), .id (n+27), .id (n+28)]⟩ : Def) pos.row_33
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 34 (⟨.not, [.id (n+17)]⟩ : Def) pos.row_34
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 35 (⟨.csel, [.id (n+33), .id (n+17), .id (n+34)]⟩ : Def) pos.row_35
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 36 (⟨.add, [.id (n+35), .imm 0#64]⟩ : Def) pos.row_36
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 37 (⟨.mul, [.id (n+16), .id (n+32)]⟩ : Def) pos.row_37
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 38 (⟨.umulh, [.id (n+16), .id (n+32)]⟩ : Def) pos.row_38
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 39 (⟨.add3, [.id (n+4), .id (n+18), .imm 0#64]⟩ : Def) pos.row_39
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 42 (⟨.carry3, [.id (n+4), .id (n+18), .imm 0#64]⟩ : Def) pos.row_42
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 44 (⟨.add3, [.id (n+18), .id (n+23), .id (n+42)]⟩ : Def) pos.row_44
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 47 (⟨.carry3, [.id (n+18), .id (n+23), .id (n+42)]⟩ : Def) pos.row_47
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 49 (⟨.add3, [.id (n+23), .imm 0#64, .id (n+47)]⟩ : Def) pos.row_49
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 52 (⟨.carry3, [.id (n+36), .imm 1#64, .imm 0#64]⟩ : Def) pos.row_52
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 54 (⟨.eor, [.id (n+37), .id (n+36)]⟩ : Def) pos.row_54
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 55 (⟨.add3, [.id (n+54), .id (n+39), .id (n+52)]⟩ : Def) pos.row_55
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 58 (⟨.carry3, [.id (n+54), .id (n+39), .id (n+52)]⟩ : Def) pos.row_58
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 60 (⟨.eor, [.id (n+38), .id (n+36)]⟩ : Def) pos.row_60
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 61 (⟨.add3, [.id (n+60), .id (n+44), .id (n+58)]⟩ : Def) pos.row_61
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 64 (⟨.carry3, [.id (n+60), .id (n+44), .id (n+58)]⟩ : Def) pos.row_64
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 66 (⟨.add3, [.id (n+49), .id (n+36), .id (n+64)]⟩ : Def) pos.row_66
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 71 (⟨.mul, [.id (n+67), .id (n+69)]⟩ : Def) pos.row_71
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 72 (⟨.umulh, [.id (n+67), .id (n+69)]⟩ : Def) pos.row_72
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 73 (⟨.mul, [.id (n+68), .id (n+70)]⟩ : Def) pos.row_73
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 74 (⟨.umulh, [.id (n+68), .id (n+70)]⟩ : Def) pos.row_74
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 75 (⟨.sbc3, [.id (n+68), .id (n+67), .imm 1#64]⟩ : Def) pos.row_75
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 78 (⟨.sbc3C, [.id (n+68), .id (n+67), .imm 1#64]⟩ : Def) pos.row_78
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 80 (⟨.cond 2#4, [.id (n+76), .id (n+77), .id (n+78), .id (n+79)]⟩ : Def) pos.row_80
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 81 (⟨.sub, [.imm 0#64, .id (n+75)]⟩ : Def) pos.row_81
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 82 (⟨.csel, [.id (n+80), .id (n+75), .id (n+81)]⟩ : Def) pos.row_82
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 83 (⟨.add, [.id (n+82), .imm 0#64]⟩ : Def) pos.row_83
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 84 (⟨.cselc 2#4, [.id (n+76), .id (n+77), .id (n+78), .id (n+79), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def) pos.row_84
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 85 (⟨.add3, [.id (n+73), .id (n+72), .imm 0#64]⟩ : Def) pos.row_85
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 88 (⟨.carry3, [.id (n+73), .id (n+72), .imm 0#64]⟩ : Def) pos.row_88
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 90 (⟨.add3, [.id (n+74), .imm 0#64, .id (n+88)]⟩ : Def) pos.row_90
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 91 (⟨.sbc3, [.id (n+69), .id (n+70), .imm 1#64]⟩ : Def) pos.row_91
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 94 (⟨.sbc3C, [.id (n+69), .id (n+70), .imm 1#64]⟩ : Def) pos.row_94
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 96 (⟨.cond 2#4, [.id (n+92), .id (n+93), .id (n+94), .id (n+95)]⟩ : Def) pos.row_96
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 97 (⟨.sub, [.imm 0#64, .id (n+91)]⟩ : Def) pos.row_97
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 98 (⟨.csel, [.id (n+96), .id (n+91), .id (n+97)]⟩ : Def) pos.row_98
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 99 (⟨.add, [.id (n+98), .imm 0#64]⟩ : Def) pos.row_99
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 100 (⟨.cond 2#4, [.id (n+92), .id (n+93), .id (n+94), .id (n+95)]⟩ : Def) pos.row_100
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 101 (⟨.not, [.id (n+84)]⟩ : Def) pos.row_101
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 102 (⟨.csel, [.id (n+100), .id (n+84), .id (n+101)]⟩ : Def) pos.row_102
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 103 (⟨.add, [.id (n+102), .imm 0#64]⟩ : Def) pos.row_103
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 104 (⟨.mul, [.id (n+83), .id (n+99)]⟩ : Def) pos.row_104
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 105 (⟨.umulh, [.id (n+83), .id (n+99)]⟩ : Def) pos.row_105
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 106 (⟨.add3, [.id (n+71), .id (n+85), .imm 0#64]⟩ : Def) pos.row_106
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 109 (⟨.carry3, [.id (n+71), .id (n+85), .imm 0#64]⟩ : Def) pos.row_109
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 111 (⟨.add3, [.id (n+85), .id (n+90), .id (n+109)]⟩ : Def) pos.row_111
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 114 (⟨.carry3, [.id (n+85), .id (n+90), .id (n+109)]⟩ : Def) pos.row_114
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 116 (⟨.add3, [.id (n+90), .imm 0#64, .id (n+114)]⟩ : Def) pos.row_116
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 119 (⟨.carry3, [.id (n+103), .imm 1#64, .imm 0#64]⟩ : Def) pos.row_119
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 121 (⟨.eor, [.id (n+104), .id (n+103)]⟩ : Def) pos.row_121
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 122 (⟨.add3, [.id (n+121), .id (n+106), .id (n+119)]⟩ : Def) pos.row_122
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 125 (⟨.carry3, [.id (n+121), .id (n+106), .id (n+119)]⟩ : Def) pos.row_125
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 127 (⟨.eor, [.id (n+105), .id (n+103)]⟩ : Def) pos.row_127
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 128 (⟨.add3, [.id (n+127), .id (n+111), .id (n+125)]⟩ : Def) pos.row_128
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 131 (⟨.carry3, [.id (n+127), .id (n+111), .id (n+125)]⟩ : Def) pos.row_131
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 133 (⟨.add3, [.id (n+116), .id (n+103), .id (n+131)]⟩ : Def) pos.row_133
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 138 (⟨.sbc3, [.id (n+134), .id (n+136), .imm 1#64]⟩ : Def) pos.row_138
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 141 (⟨.sbc3C, [.id (n+134), .id (n+136), .imm 1#64]⟩ : Def) pos.row_141
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 143 (⟨.sbc3, [.id (n+135), .id (n+137), .id (n+141)]⟩ : Def) pos.row_143
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 146 (⟨.sbc3C, [.id (n+135), .id (n+137), .id (n+141)]⟩ : Def) pos.row_146
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 148 (⟨.cselc 2#4, [.id (n+144), .id (n+145), .id (n+146), .id (n+147), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def) pos.row_148
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 151 (⟨.sbc3, [.id (n+149), .id (n+69), .imm 1#64]⟩ : Def) pos.row_151
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 154 (⟨.sbc3C, [.id (n+149), .id (n+69), .imm 1#64]⟩ : Def) pos.row_154
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 156 (⟨.sbc3, [.id (n+150), .id (n+70), .id (n+154)]⟩ : Def) pos.row_156
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 159 (⟨.sbc3C, [.id (n+150), .id (n+70), .id (n+154)]⟩ : Def) pos.row_159
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 161 (⟨.cselc 2#4, [.id (n+157), .id (n+158), .id (n+159), .id (n+160), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def) pos.row_161
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 162 (⟨.eor, [.id (n+138), .id (n+148)]⟩ : Def) pos.row_162
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 163 (⟨.sbc3, [.id (n+162), .id (n+148), .imm 1#64]⟩ : Def) pos.row_163
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 166 (⟨.sbc3C, [.id (n+162), .id (n+148), .imm 1#64]⟩ : Def) pos.row_166
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 168 (⟨.eor, [.id (n+143), .id (n+148)]⟩ : Def) pos.row_168
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 169 (⟨.sbc3, [.id (n+168), .id (n+148), .id (n+166)]⟩ : Def) pos.row_169
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 170 (⟨.eor, [.id (n+151), .id (n+161)]⟩ : Def) pos.row_170
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 171 (⟨.sbc3, [.id (n+170), .id (n+161), .imm 1#64]⟩ : Def) pos.row_171
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 174 (⟨.sbc3C, [.id (n+170), .id (n+161), .imm 1#64]⟩ : Def) pos.row_174
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 176 (⟨.eor, [.id (n+156), .id (n+161)]⟩ : Def) pos.row_176
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 177 (⟨.sbc3, [.id (n+176), .id (n+161), .id (n+174)]⟩ : Def) pos.row_177
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 178 (⟨.eor, [.id (n+161), .id (n+148)]⟩ : Def) pos.row_178
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 179 (⟨.add3, [.id (n+71), .id (n+61), .imm 0#64]⟩ : Def) pos.row_179
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 182 (⟨.carry3, [.id (n+71), .id (n+61), .imm 0#64]⟩ : Def) pos.row_182
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 184 (⟨.add3, [.id (n+122), .id (n+66), .id (n+182)]⟩ : Def) pos.row_184
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 187 (⟨.carry3, [.id (n+122), .id (n+66), .id (n+182)]⟩ : Def) pos.row_187
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 189 (⟨.add3, [.id (n+128), .imm 0#64, .id (n+187)]⟩ : Def) pos.row_189
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 192 (⟨.carry3, [.id (n+128), .imm 0#64, .id (n+187)]⟩ : Def) pos.row_192
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 194 (⟨.add3, [.id (n+133), .imm 0#64, .id (n+192)]⟩ : Def) pos.row_194
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 195 (⟨.mul, [.id (n+163), .id (n+171)]⟩ : Def) pos.row_195
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 196 (⟨.umulh, [.id (n+163), .id (n+171)]⟩ : Def) pos.row_196
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 197 (⟨.mul, [.id (n+169), .id (n+177)]⟩ : Def) pos.row_197
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 198 (⟨.umulh, [.id (n+169), .id (n+177)]⟩ : Def) pos.row_198
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 199 (⟨.sbc3, [.id (n+169), .id (n+163), .imm 1#64]⟩ : Def) pos.row_199
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 202 (⟨.sbc3C, [.id (n+169), .id (n+163), .imm 1#64]⟩ : Def) pos.row_202
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 204 (⟨.cond 2#4, [.id (n+200), .id (n+201), .id (n+202), .id (n+203)]⟩ : Def) pos.row_204
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 205 (⟨.sub, [.imm 0#64, .id (n+199)]⟩ : Def) pos.row_205
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 206 (⟨.csel, [.id (n+204), .id (n+199), .id (n+205)]⟩ : Def) pos.row_206
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 207 (⟨.add, [.id (n+206), .imm 0#64]⟩ : Def) pos.row_207
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 208 (⟨.cselc 2#4, [.id (n+200), .id (n+201), .id (n+202), .id (n+203), .imm 0#64, .imm 18446744073709551615#64]⟩ : Def) pos.row_208
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 209 (⟨.add3, [.id (n+197), .id (n+196), .imm 0#64]⟩ : Def) pos.row_209
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 212 (⟨.carry3, [.id (n+197), .id (n+196), .imm 0#64]⟩ : Def) pos.row_212
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 214 (⟨.add3, [.id (n+198), .imm 0#64, .id (n+212)]⟩ : Def) pos.row_214
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 215 (⟨.sbc3, [.id (n+171), .id (n+177), .imm 1#64]⟩ : Def) pos.row_215
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 218 (⟨.sbc3C, [.id (n+171), .id (n+177), .imm 1#64]⟩ : Def) pos.row_218
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 220 (⟨.cond 2#4, [.id (n+216), .id (n+217), .id (n+218), .id (n+219)]⟩ : Def) pos.row_220
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 221 (⟨.sub, [.imm 0#64, .id (n+215)]⟩ : Def) pos.row_221
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 222 (⟨.csel, [.id (n+220), .id (n+215), .id (n+221)]⟩ : Def) pos.row_222
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 223 (⟨.add, [.id (n+222), .imm 0#64]⟩ : Def) pos.row_223
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 224 (⟨.cond 2#4, [.id (n+216), .id (n+217), .id (n+218), .id (n+219)]⟩ : Def) pos.row_224
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 225 (⟨.not, [.id (n+208)]⟩ : Def) pos.row_225
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 226 (⟨.csel, [.id (n+224), .id (n+208), .id (n+225)]⟩ : Def) pos.row_226
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 227 (⟨.add, [.id (n+226), .imm 0#64]⟩ : Def) pos.row_227
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 228 (⟨.mul, [.id (n+207), .id (n+223)]⟩ : Def) pos.row_228
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 229 (⟨.umulh, [.id (n+207), .id (n+223)]⟩ : Def) pos.row_229
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 230 (⟨.add3, [.id (n+195), .id (n+209), .imm 0#64]⟩ : Def) pos.row_230
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 233 (⟨.carry3, [.id (n+195), .id (n+209), .imm 0#64]⟩ : Def) pos.row_233
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 235 (⟨.add3, [.id (n+209), .id (n+214), .id (n+233)]⟩ : Def) pos.row_235
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 238 (⟨.carry3, [.id (n+209), .id (n+214), .id (n+233)]⟩ : Def) pos.row_238
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 240 (⟨.add3, [.id (n+214), .imm 0#64, .id (n+238)]⟩ : Def) pos.row_240
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 243 (⟨.carry3, [.id (n+227), .imm 1#64, .imm 0#64]⟩ : Def) pos.row_243
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 245 (⟨.eor, [.id (n+228), .id (n+227)]⟩ : Def) pos.row_245
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 246 (⟨.add3, [.id (n+245), .id (n+230), .id (n+243)]⟩ : Def) pos.row_246
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 249 (⟨.carry3, [.id (n+245), .id (n+230), .id (n+243)]⟩ : Def) pos.row_249
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 251 (⟨.eor, [.id (n+229), .id (n+227)]⟩ : Def) pos.row_251
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 252 (⟨.add3, [.id (n+251), .id (n+235), .id (n+249)]⟩ : Def) pos.row_252
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 255 (⟨.carry3, [.id (n+251), .id (n+235), .id (n+249)]⟩ : Def) pos.row_255
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 257 (⟨.add3, [.id (n+240), .id (n+227), .id (n+255)]⟩ : Def) pos.row_257
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 258 (⟨.add3, [.id (n+179), .id (n+4), .imm 0#64]⟩ : Def) pos.row_258
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 261 (⟨.carry3, [.id (n+179), .id (n+4), .imm 0#64]⟩ : Def) pos.row_261
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 263 (⟨.add3, [.id (n+184), .id (n+55), .id (n+261)]⟩ : Def) pos.row_263
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 266 (⟨.carry3, [.id (n+184), .id (n+55), .id (n+261)]⟩ : Def) pos.row_266
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 268 (⟨.add3, [.id (n+189), .id (n+179), .id (n+266)]⟩ : Def) pos.row_268
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 271 (⟨.carry3, [.id (n+189), .id (n+179), .id (n+266)]⟩ : Def) pos.row_271
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 273 (⟨.add3, [.id (n+194), .id (n+184), .id (n+271)]⟩ : Def) pos.row_273
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 276 (⟨.carry3, [.id (n+194), .id (n+184), .id (n+271)]⟩ : Def) pos.row_276
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 278 (⟨.add3, [.id (n+189), .imm 0#64, .id (n+276)]⟩ : Def) pos.row_278
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 281 (⟨.carry3, [.id (n+189), .imm 0#64, .id (n+276)]⟩ : Def) pos.row_281
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 283 (⟨.add3, [.id (n+194), .imm 0#64, .id (n+281)]⟩ : Def) pos.row_283
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 286 (⟨.carry3, [.id (n+178), .imm 1#64, .imm 0#64]⟩ : Def) pos.row_286
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 288 (⟨.eor, [.id (n+195), .id (n+178)]⟩ : Def) pos.row_288
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 289 (⟨.add3, [.id (n+288), .id (n+258), .id (n+286)]⟩ : Def) pos.row_289
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 292 (⟨.carry3, [.id (n+288), .id (n+258), .id (n+286)]⟩ : Def) pos.row_292
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 294 (⟨.eor, [.id (n+246), .id (n+178)]⟩ : Def) pos.row_294
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 295 (⟨.add3, [.id (n+294), .id (n+263), .id (n+292)]⟩ : Def) pos.row_295
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 298 (⟨.carry3, [.id (n+294), .id (n+263), .id (n+292)]⟩ : Def) pos.row_298
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 300 (⟨.eor, [.id (n+252), .id (n+178)]⟩ : Def) pos.row_300
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 301 (⟨.add3, [.id (n+300), .id (n+268), .id (n+298)]⟩ : Def) pos.row_301
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 304 (⟨.carry3, [.id (n+300), .id (n+268), .id (n+298)]⟩ : Def) pos.row_304
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 306 (⟨.eor, [.id (n+257), .id (n+178)]⟩ : Def) pos.row_306
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 307 (⟨.add3, [.id (n+306), .id (n+273), .id (n+304)]⟩ : Def) pos.row_307
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 310 (⟨.carry3, [.id (n+306), .id (n+273), .id (n+304)]⟩ : Def) pos.row_310
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 312 (⟨.add3, [.id (n+278), .id (n+178), .id (n+310)]⟩ : Def) pos.row_312
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 315 (⟨.carry3, [.id (n+278), .id (n+178), .id (n+310)]⟩ : Def) pos.row_315
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 317 (⟨.add3, [.id (n+283), .id (n+178), .id (n+315)]⟩ : Def) pos.row_317
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · have h := TableEval.evalDefs_row inputs defs 318 (⟨.const 977#64, []⟩ : Def) pos.row_318
      (by rw [lengthEq]; simp [Def.Below, Arg.Below])
    rw [lengthEq, const_eval] at h
    exact h
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 319 (⟨.orr, [.id (n+318), .imm 4294967296#64]⟩ : Def) pos.row_319
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 320 (⟨.mul, [.id (n+319), .id (n+301)]⟩ : Def) pos.row_320
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 321 (⟨.umulh, [.id (n+319), .id (n+301)]⟩ : Def) pos.row_321
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 322 (⟨.and, [.id (n+307), .imm 4294967295#64]⟩ : Def) pos.row_322
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 323 (⟨.lsr 32, [.id (n+307)]⟩ : Def) pos.row_323
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 324 (⟨.mul, [.id (n+318), .id (n+322)]⟩ : Def) pos.row_324
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 325 (⟨.mul, [.id (n+318), .id (n+323)]⟩ : Def) pos.row_325
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 326 (⟨.add, [.id (n+325), .id (n+322)]⟩ : Def) pos.row_326
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 327 (⟨.add, [.id (n+326), .imm 0#64]⟩ : Def) pos.row_327
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 328 (⟨.lsl 32, [.id (n+327)]⟩ : Def) pos.row_328
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 329 (⟨.add3, [.id (n+324), .id (n+328), .imm 0#64]⟩ : Def) pos.row_329
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 330 (⟨.add, [.id (n+329), .imm 0#64]⟩ : Def) pos.row_330
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 331 (⟨.lsl 32, [.id (n+327)]⟩ : Def) pos.row_331
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 333 (⟨.add, [.id (n+332), .imm 0#64]⟩ : Def) pos.row_333
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 334 (⟨.lsl 32, [.id (n+327)]⟩ : Def) pos.row_334
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 336 (⟨.add, [.id (n+335), .imm 0#64]⟩ : Def) pos.row_336
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 337 (⟨.lsl 32, [.id (n+327)]⟩ : Def) pos.row_337
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 338 (⟨.carry3, [.id (n+324), .id (n+337), .imm 0#64]⟩ : Def) pos.row_338
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 339 (⟨.add, [.id (n+338), .imm 0#64]⟩ : Def) pos.row_339
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 340 (⟨.lsl 32, [.id (n+327)]⟩ : Def) pos.row_340
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 342 (⟨.add, [.id (n+341), .imm 0#64]⟩ : Def) pos.row_342
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 343 (⟨.lsr 32, [.id (n+327)]⟩ : Def) pos.row_343
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 344 (⟨.add3, [.id (n+323), .id (n+343), .id (n+339)]⟩ : Def) pos.row_344
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 345 (⟨.mul, [.id (n+319), .id (n+312)]⟩ : Def) pos.row_345
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 346 (⟨.umulh, [.id (n+319), .id (n+312)]⟩ : Def) pos.row_346
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 347 (⟨.and, [.id (n+317), .imm 4294967295#64]⟩ : Def) pos.row_347
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 348 (⟨.lsr 32, [.id (n+317)]⟩ : Def) pos.row_348
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 349 (⟨.mul, [.id (n+318), .id (n+347)]⟩ : Def) pos.row_349
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 350 (⟨.mul, [.id (n+318), .id (n+348)]⟩ : Def) pos.row_350
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 351 (⟨.add, [.id (n+350), .id (n+347)]⟩ : Def) pos.row_351
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 352 (⟨.add, [.id (n+351), .imm 0#64]⟩ : Def) pos.row_352
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 353 (⟨.lsl 32, [.id (n+352)]⟩ : Def) pos.row_353
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 354 (⟨.add3, [.id (n+349), .id (n+353), .imm 0#64]⟩ : Def) pos.row_354
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 355 (⟨.add, [.id (n+354), .imm 0#64]⟩ : Def) pos.row_355
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 356 (⟨.lsl 32, [.id (n+352)]⟩ : Def) pos.row_356
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 358 (⟨.add, [.id (n+357), .imm 0#64]⟩ : Def) pos.row_358
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 359 (⟨.lsl 32, [.id (n+352)]⟩ : Def) pos.row_359
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 361 (⟨.add, [.id (n+360), .imm 0#64]⟩ : Def) pos.row_361
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 362 (⟨.lsl 32, [.id (n+352)]⟩ : Def) pos.row_362
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 363 (⟨.carry3, [.id (n+349), .id (n+362), .imm 0#64]⟩ : Def) pos.row_363
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 364 (⟨.add, [.id (n+363), .imm 0#64]⟩ : Def) pos.row_364
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 365 (⟨.lsl 32, [.id (n+352)]⟩ : Def) pos.row_365
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 367 (⟨.add, [.id (n+366), .imm 0#64]⟩ : Def) pos.row_367
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 368 (⟨.lsr 32, [.id (n+352)]⟩ : Def) pos.row_368
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 369 (⟨.add3, [.id (n+348), .id (n+368), .id (n+364)]⟩ : Def) pos.row_369
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 370 (⟨.add3, [.id (n+4), .id (n+320), .imm 0#64]⟩ : Def) pos.row_370
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 373 (⟨.carry3, [.id (n+4), .id (n+320), .imm 0#64]⟩ : Def) pos.row_373
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 375 (⟨.add3, [.id (n+55), .id (n+330), .id (n+373)]⟩ : Def) pos.row_375
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 378 (⟨.carry3, [.id (n+55), .id (n+330), .id (n+373)]⟩ : Def) pos.row_378
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 380 (⟨.add3, [.id (n+289), .id (n+345), .id (n+378)]⟩ : Def) pos.row_380
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 383 (⟨.carry3, [.id (n+289), .id (n+345), .id (n+378)]⟩ : Def) pos.row_383
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 385 (⟨.add3, [.id (n+295), .id (n+355), .id (n+383)]⟩ : Def) pos.row_385
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 388 (⟨.carry3, [.id (n+295), .id (n+355), .id (n+383)]⟩ : Def) pos.row_388
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 390 (⟨.cond 2#4, [.id (n+386), .id (n+387), .id (n+388), .id (n+389)]⟩ : Def) pos.row_390
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 391 (⟨.add3, [.id (n+375), .id (n+321), .imm 0#64]⟩ : Def) pos.row_391
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 394 (⟨.carry3, [.id (n+375), .id (n+321), .imm 0#64]⟩ : Def) pos.row_394
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 396 (⟨.add3, [.id (n+380), .id (n+344), .id (n+394)]⟩ : Def) pos.row_396
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 399 (⟨.carry3, [.id (n+380), .id (n+344), .id (n+394)]⟩ : Def) pos.row_399
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 401 (⟨.add3, [.id (n+385), .id (n+346), .id (n+399)]⟩ : Def) pos.row_401
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 404 (⟨.carry3, [.id (n+385), .id (n+346), .id (n+399)]⟩ : Def) pos.row_404
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 406 (⟨.add3, [.id (n+390), .id (n+369), .id (n+404)]⟩ : Def) pos.row_406
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 407 (⟨.add, [.id (n+406), .imm 1#64]⟩ : Def) pos.row_407
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 408 (⟨.mul, [.id (n+318), .id (n+407)]⟩ : Def) pos.row_408
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 409 (⟨.lsr 32, [.id (n+407)]⟩ : Def) pos.row_409
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 410 (⟨.lsl 32, [.id (n+407)]⟩ : Def) pos.row_410
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 411 (⟨.add3, [.id (n+408), .id (n+410), .imm 0#64]⟩ : Def) pos.row_411
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 412 (⟨.add, [.id (n+411), .imm 0#64]⟩ : Def) pos.row_412
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 413 (⟨.lsl 32, [.id (n+407)]⟩ : Def) pos.row_413
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 415 (⟨.add, [.id (n+414), .imm 0#64]⟩ : Def) pos.row_415
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 416 (⟨.lsl 32, [.id (n+407)]⟩ : Def) pos.row_416
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 418 (⟨.add, [.id (n+417), .imm 0#64]⟩ : Def) pos.row_418
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 419 (⟨.lsl 32, [.id (n+407)]⟩ : Def) pos.row_419
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 420 (⟨.carry3, [.id (n+408), .id (n+419), .imm 0#64]⟩ : Def) pos.row_420
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 421 (⟨.add, [.id (n+420), .imm 0#64]⟩ : Def) pos.row_421
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 422 (⟨.lsl 32, [.id (n+407)]⟩ : Def) pos.row_422
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 424 (⟨.add, [.id (n+423), .imm 0#64]⟩ : Def) pos.row_424
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 425 (⟨.add3, [.imm 0#64, .id (n+409), .id (n+421)]⟩ : Def) pos.row_425
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 426 (⟨.add3, [.id (n+370), .id (n+412), .imm 0#64]⟩ : Def) pos.row_426
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 429 (⟨.carry3, [.id (n+370), .id (n+412), .imm 0#64]⟩ : Def) pos.row_429
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 431 (⟨.add3, [.id (n+391), .id (n+425), .id (n+429)]⟩ : Def) pos.row_431
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 434 (⟨.carry3, [.id (n+391), .id (n+425), .id (n+429)]⟩ : Def) pos.row_434
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 436 (⟨.add3, [.id (n+396), .imm 0#64, .id (n+434)]⟩ : Def) pos.row_436
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 439 (⟨.carry3, [.id (n+396), .imm 0#64, .id (n+434)]⟩ : Def) pos.row_439
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 441 (⟨.add3, [.id (n+401), .imm 0#64, .id (n+439)]⟩ : Def) pos.row_441
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 444 (⟨.carry3, [.id (n+401), .imm 0#64, .id (n+439)]⟩ : Def) pos.row_444
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 446 (⟨.cselc 3#4, [.id (n+442), .id (n+443), .id (n+444), .id (n+445), .id (n+319), .imm 0#64]⟩ : Def) pos.row_446
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 447 (⟨.sbc3, [.id (n+426), .id (n+446), .imm 1#64]⟩ : Def) pos.row_447
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 450 (⟨.sbc3C, [.id (n+426), .id (n+446), .imm 1#64]⟩ : Def) pos.row_450
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 452 (⟨.sbc3, [.id (n+431), .imm 0#64, .id (n+450)]⟩ : Def) pos.row_452
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 455 (⟨.sbc3C, [.id (n+431), .imm 0#64, .id (n+450)]⟩ : Def) pos.row_455
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 457 (⟨.sbc3, [.id (n+436), .imm 0#64, .id (n+455)]⟩ : Def) pos.row_457
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 460 (⟨.sbc3C, [.id (n+436), .imm 0#64, .id (n+455)]⟩ : Def) pos.row_460
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 462 (⟨.sbc3, [.id (n+441), .imm 0#64, .id (n+460)]⟩ : Def) pos.row_462
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))

def loadedX (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v n,v (n+1),v (n+67),v (n+68)⟩
def loadedY (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+2),v (n+3),v (n+69),v (n+70)⟩
theorem loaded_inputs (inputs : List (BitVec 64)) (defs : List Def) (n xs ys : Nat)
    (lengthEq : inputs.length = n) (pos : LoadPositions defs xs ys)
    (insideX : xs+32 ≤ n) (insideY : ys+32 ≤ n) :
    loadedX (fun i => (evalDefs inputs defs).getD i 0) n = inputLimbs inputs xs ∧
    loadedY (fun i => (evalDefs inputs defs).getD i 0) n = inputLimbs inputs ys := by
  subst n
  have load_0 := loaded_input_word inputs defs 0 xs pos.load_0 (by omega)
  have load_1 := loaded_input_word inputs defs 1 (xs+8) pos.load_1 (by omega)
  have load_2 := loaded_input_word inputs defs 2 ys pos.load_2 (by omega)
  have load_3 := loaded_input_word inputs defs 3 (ys+8) pos.load_3 (by omega)
  have load_67 := loaded_input_word inputs defs 67 (xs+16) pos.load_67 (by omega)
  have load_68 := loaded_input_word inputs defs 68 (xs+24) pos.load_68 (by omega)
  have load_69 := loaded_input_word inputs defs 69 (ys+16) pos.load_69 (by omega)
  have load_70 := loaded_input_word inputs defs 70 (ys+24) pos.load_70 (by omega)
  simp only [Nat.add_zero] at load_0
  simp only [loadedX,loadedY,inputLimbs,load_0, load_1, load_2, load_3, load_67, load_68, load_69, load_70]
  constructor <;> trivial
end SecpMath.MainMulSSA
