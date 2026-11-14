import SecpMath.CoreCmul
import SecpMath.SubSSA
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
namespace SecpMath.CmulSSA
open ArmCertValue SecpMath.Addition SecpMath.Product SecpMath.CoreConstantMultiply
open SecpMath.SubSSA (inputWordDef inputLimbs loaded_input_word)

def loadedX (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v n, v (n+1), v (n+2), v (n+3)⟩

def resultWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+58), v (n+63), v (n+68), v (n+73)⟩

structure LoadPositions (defs : List Def) (xs : Nat) : Prop where
  w0 : defs[0]? = some (inputWordDef xs)
  w1 : defs[1]? = some (inputWordDef (xs+8))
  w2 : defs[2]? = some (inputWordDef (xs+16))
  w3 : defs[3]? = some (inputWordDef (xs+24))

theorem loaded_inputs (inputs : List (BitVec 64)) (defs : List Def) (n xs : Nat)
    (lengthEq : inputs.length = n) (pos : LoadPositions defs xs) (inside : xs+32 ≤ n) :
    loadedX (fun i => (evalDefs inputs defs).getD i 0) n = inputLimbs inputs xs := by
  subst n
  have first := loaded_input_word inputs defs 0 xs pos.w0 (by omega)
  simp only [Nat.add_zero] at first
  simp only [loadedX, inputLimbs, first,
    loaded_input_word inputs defs 1 (xs+8) pos.w1 (by omega),
    loaded_input_word inputs defs 2 (xs+16) pos.w2 (by omega),
    loaded_input_word inputs defs 3 (xs+24) pos.w3 (by omega)]

private theorem const_eval (values : List (BitVec 64)) (c : BitVec 64) :
    Def.eval values ⟨.const c, []⟩ = c := rfl

structure Equations (v : Nat → BitVec 64) (n ci : Nat) : Prop where
  u0 : v (n+4) = (Op.mul).eval [v ci, v n]
  u1 : v (n+5) = (Op.mul).eval [v ci, v (n+1)]
  u2 : v (n+6) = (Op.mul).eval [v ci, v (n+2)]
  u3 : v (n+7) = (Op.mul).eval [v ci, v (n+3)]
  v0 : v (n+8) = (Op.umulh).eval [v ci, v n]
  v1 : v (n+9) = (Op.umulh).eval [v ci, v (n+1)]
  v2 : v (n+10) = (Op.umulh).eval [v ci, v (n+2)]
  v3 : v (n+11) = (Op.umulh).eval [v ci, v (n+3)]
  d1 : v (n+12) = (Op.add3).eval [v (n+5), v (n+8), 0#64]
  c1 : v (n+15) = (Op.carry3).eval [v (n+5), v (n+8), 0#64]
  d2 : v (n+17) = (Op.add3).eval [v (n+6), v (n+9), v (n+15)]
  c2 : v (n+20) = (Op.carry3).eval [v (n+6), v (n+9), v (n+15)]
  d3 : v (n+22) = (Op.add3).eval [v (n+7), v (n+10), v (n+20)]
  c3 : v (n+25) = (Op.carry3).eval [v (n+7), v (n+10), v (n+20)]
  high : v (n+27) = (Op.add3).eval [v (n+11), 0#64, v (n+25)]
  quotient : v (n+32) = (Op.add).eval [v (n+27), 1#64]
  constant : v (n+33) = 977#64
  combine : v (n+34) = (Op.orr).eval [v (n+33), 4294967296#64]
  p0 : v (n+35) = (Op.mul).eval [v (n+32), v (n+34)]
  p1 : v (n+36) = (Op.umulh).eval [v (n+32), v (n+34)]
  f0 : v (n+37) = (Op.add3).eval [v (n+4), v (n+35), 0#64]
  fc0 : v (n+40) = (Op.carry3).eval [v (n+4), v (n+35), 0#64]
  f1 : v (n+42) = (Op.add3).eval [v (n+12), v (n+36), v (n+40)]
  fc1 : v (n+45) = (Op.carry3).eval [v (n+12), v (n+36), v (n+40)]
  f2 : v (n+47) = (Op.add3).eval [v (n+17), 0#64, v (n+45)]
  fc2 : v (n+50) = (Op.carry3).eval [v (n+17), 0#64, v (n+45)]
  f3 : v (n+52) = (Op.add3).eval [v (n+22), 0#64, v (n+50)]
  fc3 : v (n+55) = (Op.carry3).eval [v (n+22), 0#64, v (n+50)]
  select : v (n+57) = (Op.cselc 3#4).eval [v (n+53), v (n+54), v (n+55), v (n+56), v (n+34), 0#64]
  r0 : v (n+58) = (Op.sbc3).eval [v (n+37), v (n+57), 1#64]
  rc0 : v (n+61) = (Op.sbc3C).eval [v (n+37), v (n+57), 1#64]
  r1 : v (n+63) = (Op.sbc3).eval [v (n+42), 0#64, v (n+61)]
  rc1 : v (n+66) = (Op.sbc3C).eval [v (n+42), 0#64, v (n+61)]
  r2 : v (n+68) = (Op.sbc3).eval [v (n+47), 0#64, v (n+66)]
  rc2 : v (n+71) = (Op.sbc3C).eval [v (n+47), 0#64, v (n+66)]
  r3 : v (n+73) = (Op.sbc3).eval [v (n+52), 0#64, v (n+71)]

structure RowPositions (defs : List Def) (n ci : Nat) : Prop where
  u0 : defs[4]? = some (⟨.mul, [.id ci, .id n]⟩ : Def)
  u1 : defs[5]? = some (⟨.mul, [.id ci, .id (n+1)]⟩ : Def)
  u2 : defs[6]? = some (⟨.mul, [.id ci, .id (n+2)]⟩ : Def)
  u3 : defs[7]? = some (⟨.mul, [.id ci, .id (n+3)]⟩ : Def)
  v0 : defs[8]? = some (⟨.umulh, [.id ci, .id n]⟩ : Def)
  v1 : defs[9]? = some (⟨.umulh, [.id ci, .id (n+1)]⟩ : Def)
  v2 : defs[10]? = some (⟨.umulh, [.id ci, .id (n+2)]⟩ : Def)
  v3 : defs[11]? = some (⟨.umulh, [.id ci, .id (n+3)]⟩ : Def)
  d1 : defs[12]? = some (⟨.add3, [.id (n+5), .id (n+8), .imm 0#64]⟩ : Def)
  c1 : defs[15]? = some (⟨.carry3, [.id (n+5), .id (n+8), .imm 0#64]⟩ : Def)
  d2 : defs[17]? = some (⟨.add3, [.id (n+6), .id (n+9), .id (n+15)]⟩ : Def)
  c2 : defs[20]? = some (⟨.carry3, [.id (n+6), .id (n+9), .id (n+15)]⟩ : Def)
  d3 : defs[22]? = some (⟨.add3, [.id (n+7), .id (n+10), .id (n+20)]⟩ : Def)
  c3 : defs[25]? = some (⟨.carry3, [.id (n+7), .id (n+10), .id (n+20)]⟩ : Def)
  high : defs[27]? = some (⟨.add3, [.id (n+11), .imm 0#64, .id (n+25)]⟩ : Def)
  quotient : defs[32]? = some (⟨.add, [.id (n+27), .imm 1#64]⟩ : Def)
  constant : defs[33]? = some (⟨.const 977#64, []⟩ : Def)
  combine : defs[34]? = some (⟨.orr, [.id (n+33), .imm 4294967296#64]⟩ : Def)
  p0 : defs[35]? = some (⟨.mul, [.id (n+32), .id (n+34)]⟩ : Def)
  p1 : defs[36]? = some (⟨.umulh, [.id (n+32), .id (n+34)]⟩ : Def)
  f0 : defs[37]? = some (⟨.add3, [.id (n+4), .id (n+35), .imm 0#64]⟩ : Def)
  fc0 : defs[40]? = some (⟨.carry3, [.id (n+4), .id (n+35), .imm 0#64]⟩ : Def)
  f1 : defs[42]? = some (⟨.add3, [.id (n+12), .id (n+36), .id (n+40)]⟩ : Def)
  fc1 : defs[45]? = some (⟨.carry3, [.id (n+12), .id (n+36), .id (n+40)]⟩ : Def)
  f2 : defs[47]? = some (⟨.add3, [.id (n+17), .imm 0#64, .id (n+45)]⟩ : Def)
  fc2 : defs[50]? = some (⟨.carry3, [.id (n+17), .imm 0#64, .id (n+45)]⟩ : Def)
  f3 : defs[52]? = some (⟨.add3, [.id (n+22), .imm 0#64, .id (n+50)]⟩ : Def)
  fc3 : defs[55]? = some (⟨.carry3, [.id (n+22), .imm 0#64, .id (n+50)]⟩ : Def)
  select : defs[57]? = some (⟨.cselc 3#4, [.id (n+53), .id (n+54), .id (n+55), .id (n+56), .id (n+34), .imm 0#64]⟩ : Def)
  r0 : defs[58]? = some (⟨.sbc3, [.id (n+37), .id (n+57), .imm 1#64]⟩ : Def)
  rc0 : defs[61]? = some (⟨.sbc3C, [.id (n+37), .id (n+57), .imm 1#64]⟩ : Def)
  r1 : defs[63]? = some (⟨.sbc3, [.id (n+42), .imm 0#64, .id (n+61)]⟩ : Def)
  rc1 : defs[66]? = some (⟨.sbc3C, [.id (n+42), .imm 0#64, .id (n+61)]⟩ : Def)
  r2 : defs[68]? = some (⟨.sbc3, [.id (n+47), .imm 0#64, .id (n+66)]⟩ : Def)
  rc2 : defs[71]? = some (⟨.sbc3C, [.id (n+47), .imm 0#64, .id (n+66)]⟩ : Def)
  r3 : defs[73]? = some (⟨.sbc3, [.id (n+52), .imm 0#64, .id (n+71)]⟩ : Def)

theorem equations_of_positions (inputs : List (BitVec 64)) (defs : List Def) (n ci : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n ci) (cInside : ci < n) :
    Equations (fun i => (evalDefs inputs defs).getD i 0) n ci := by
  constructor
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 4 (⟨.mul, [.id ci, .id n]⟩ : Def) pos.u0
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 5 (⟨.mul, [.id ci, .id (n+1)]⟩ : Def) pos.u1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 6 (⟨.mul, [.id ci, .id (n+2)]⟩ : Def) pos.u2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 7 (⟨.mul, [.id ci, .id (n+3)]⟩ : Def) pos.u3
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 8 (⟨.umulh, [.id ci, .id n]⟩ : Def) pos.v0
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 9 (⟨.umulh, [.id ci, .id (n+1)]⟩ : Def) pos.v1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 10 (⟨.umulh, [.id ci, .id (n+2)]⟩ : Def) pos.v2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 11 (⟨.umulh, [.id ci, .id (n+3)]⟩ : Def) pos.v3
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 12 (⟨.add3, [.id (n+5), .id (n+8), .imm 0#64]⟩ : Def) pos.d1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 15 (⟨.carry3, [.id (n+5), .id (n+8), .imm 0#64]⟩ : Def) pos.c1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 17 (⟨.add3, [.id (n+6), .id (n+9), .id (n+15)]⟩ : Def) pos.d2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 20 (⟨.carry3, [.id (n+6), .id (n+9), .id (n+15)]⟩ : Def) pos.c2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 22 (⟨.add3, [.id (n+7), .id (n+10), .id (n+20)]⟩ : Def) pos.d3
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 25 (⟨.carry3, [.id (n+7), .id (n+10), .id (n+20)]⟩ : Def) pos.c3
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 27 (⟨.add3, [.id (n+11), .imm 0#64, .id (n+25)]⟩ : Def) pos.high
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 32 (⟨.add, [.id (n+27), .imm 1#64]⟩ : Def) pos.quotient
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · have h := TableEval.evalDefs_row inputs defs 33 (⟨.const 977#64, []⟩ : Def) pos.constant
      (by rw [lengthEq]; simp [Def.Below, Arg.Below])
    rw [lengthEq, const_eval] at h
    exact h
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 34 (⟨.orr, [.id (n+33), .imm 4294967296#64]⟩ : Def) pos.combine
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 35 (⟨.mul, [.id (n+32), .id (n+34)]⟩ : Def) pos.p0
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 36 (⟨.umulh, [.id (n+32), .id (n+34)]⟩ : Def) pos.p1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 37 (⟨.add3, [.id (n+4), .id (n+35), .imm 0#64]⟩ : Def) pos.f0
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 40 (⟨.carry3, [.id (n+4), .id (n+35), .imm 0#64]⟩ : Def) pos.fc0
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 42 (⟨.add3, [.id (n+12), .id (n+36), .id (n+40)]⟩ : Def) pos.f1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 45 (⟨.carry3, [.id (n+12), .id (n+36), .id (n+40)]⟩ : Def) pos.fc1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 47 (⟨.add3, [.id (n+17), .imm 0#64, .id (n+45)]⟩ : Def) pos.f2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 50 (⟨.carry3, [.id (n+17), .imm 0#64, .id (n+45)]⟩ : Def) pos.fc2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 52 (⟨.add3, [.id (n+22), .imm 0#64, .id (n+50)]⟩ : Def) pos.f3
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 55 (⟨.carry3, [.id (n+22), .imm 0#64, .id (n+50)]⟩ : Def) pos.fc3
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 57 (⟨.cselc 3#4, [.id (n+53), .id (n+54), .id (n+55), .id (n+56), .id (n+34), .imm 0#64]⟩ : Def) pos.select
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 58 (⟨.sbc3, [.id (n+37), .id (n+57), .imm 1#64]⟩ : Def) pos.r0
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 61 (⟨.sbc3C, [.id (n+37), .id (n+57), .imm 1#64]⟩ : Def) pos.rc0
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 63 (⟨.sbc3, [.id (n+42), .imm 0#64, .id (n+61)]⟩ : Def) pos.r1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 66 (⟨.sbc3C, [.id (n+42), .imm 0#64, .id (n+61)]⟩ : Def) pos.rc1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 68 (⟨.sbc3, [.id (n+47), .imm 0#64, .id (n+66)]⟩ : Def) pos.r2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 71 (⟨.sbc3C, [.id (n+47), .imm 0#64, .id (n+66)]⟩ : Def) pos.rc2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 73 (⟨.sbc3, [.id (n+52), .imm 0#64, .id (n+71)]⟩ : Def) pos.r3
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))

theorem rows_product (v : Nat → BitVec 64) (n ci : Nat) (rows : Equations v n ci) :
    coreMultiplyWord (v ci) (loadedX v n) =
      ⟨⟨v (n+4), v (n+12), v (n+17), v (n+22)⟩, v (n+27)⟩ := by
  simp only [coreMultiplyWord, loadedX, ← rows.u0, ← rows.u1, ← rows.u2, ← rows.u3,
    ← rows.v0, ← rows.v1, ← rows.v2, ← rows.v3, ← rows.d1, ← rows.c1,
    ← rows.d2, ← rows.c2, ← rows.d3, ← rows.c3, ← rows.high]

theorem materialized_constant (v : Nat → BitVec 64) (n ci : Nat) (rows : Equations v n ci) :
    v (n+34) = BitVec.ofNat 64 correction := by
  rw [rows.combine, rows.constant]
  decide

theorem rows_fold (v : Nat → BitVec 64) (n ci : Nat) (rows : Equations v n ci) :
    foldedChain (v ci) (loadedX v n) =
      (⟨v (n+37), v (n+42), v (n+47), v (n+52)⟩, v (n+55)) := by
  unfold foldedChain
  rw [rows_product v n ci rows]
  simp only [quotientWord, correctionProduct, Addition.coreChain4,
    ← materialized_constant v n ci rows, ← rows.quotient, ← rows.p0, ← rows.p1,
    ← rows.f0, ← rows.fc0, ← rows.f1, ← rows.fc1, ← rows.f2, ← rows.fc2, ← rows.f3, ← rows.fc3]

theorem selected_value (v : Nat → BitVec 64) (n ci : Nat) (rows : Equations v n ci) :
    v (n+57) = if v (n+55) == 0#64 then BitVec.ofNat 64 correction else 0#64 := by
  rw [rows.select, materialized_constant v n ci rows]
  exact SubSSA.select_correction _ _ _ _

theorem rows_coreCmul4 (v : Nat → BitVec 64) (n ci : Nat) (rows : Equations v n ci) :
    resultWords v n = coreCmul4 (v ci) (loadedX v n) := by
  unfold coreCmul4
  rw [rows_fold v n ci rows]
  simp only [SecpMath.coreChain4, correctionWords, ← selected_value v n ci rows,
    ← rows.r0, ← rows.rc0, ← rows.r1, ← rows.rc1, ← rows.r2, ← rows.rc2, ← rows.r3, resultWords]

theorem table_correct (inputs : List (BitVec 64)) (defs : List Def) (n xs ci : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n ci)
    (loads : LoadPositions defs xs) (inside : xs+32 ≤ n) (cInside : ci < n)
    (hx : (inputLimbs inputs xs).value < modulus) :
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value < modulus ∧
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value =
      ((inputs.getD ci 0).toNat * (inputLimbs inputs xs).value) % modulus := by
  have equations := equations_of_positions inputs defs n ci lengthEq pos cInside
  have loaded := loaded_inputs inputs defs n xs lengthEq loads inside
  rw [rows_coreCmul4 _ n ci equations, loaded]
  have coefficient : (evalDefs inputs defs).getD ci 0 = inputs.getD ci 0 :=
    TableEval.extend_getD_old inputs defs ci (by omega)
  rw [coefficient]
  exact coreCmul4_correct _ _ hx

#print axioms equations_of_positions
#print axioms rows_product
#print axioms rows_fold
#print axioms rows_coreCmul4
#print axioms table_correct
end SecpMath.CmulSSA
