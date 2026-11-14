-- Actual F compiler row arithmetic for four-limb reduction. All bounds are derived.
import SecpMath.Mod4
import SecpMath.SubSSA
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
namespace SecpMath.Mod4SSA
open ArmCertValue SecpMath.Reduction SecpMath.Addition
open SecpMath.SubSSA (inputWordDef inputLimbs loaded_input_word)

def inputWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v n,v (n+1),v (n+2),v (n+3)⟩

def resultWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+18),v (n+19),v (n+20),v (n+21)⟩

structure LoadPositions (defs : List Def) (xs : Nat) : Prop where
  w0 : defs[0]? = some (inputWordDef xs)
  w1 : defs[1]? = some (inputWordDef (xs+8))
  w2 : defs[2]? = some (inputWordDef (xs+16))
  w3 : defs[3]? = some (inputWordDef (xs+24))

theorem loaded_inputs (inputs : List (BitVec 64)) (defs : List Def) (n xs : Nat)
    (lengthEq : inputs.length = n) (pos : LoadPositions defs xs) (inside : xs+32 ≤ n) :
    inputWords (fun i => (evalDefs inputs defs).getD i 0) n = inputLimbs inputs xs := by
  subst n
  have first := loaded_input_word inputs defs 0 xs pos.w0 (by omega)
  simp only [Nat.add_zero] at first
  simp only [inputWords,inputLimbs,first,
    loaded_input_word inputs defs 1 (xs+8) pos.w1 (by omega),
    loaded_input_word inputs defs 2 (xs+16) pos.w2 (by omega),
    loaded_input_word inputs defs 3 (xs+24) pos.w3 (by omega)]

structure Equations (v : Nat → BitVec 64) (n : Nat) : Prop where
  andLow : v (n+4) = (Op.and).eval [v (n+1), v (n+2)]
  andHigh : v (n+5) = (Op.and).eval [v (n+4), v (n+3)]
  constant : v (n+6) = 977#64
  combine : v (n+7) = (Op.orr).eval [v (n+6), 4294967296#64]
  lowSum : v (n+8) = (Op.add3).eval [v (n+7), v n, 0#64]
  lowCarry : v (n+11) = (Op.carry3).eval [v (n+7), v n, 0#64]
  highSum : v (n+13) = (Op.add3).eval [v (n+5), 0#64, v (n+11)]
  compare : v (n+16) = (Op.carry3).eval [v (n+5), 0#64, v (n+11)]
  select0 : v (n+18) = (Op.cselc 3#4).eval [v (n+14), v (n+15), v (n+16), v (n+17), v n, v (n+8)]
  select1 : v (n+19) = (Op.cselc 3#4).eval [v (n+14), v (n+15), v (n+16), v (n+17), v (n+1), v (n+13)]
  select2 : v (n+20) = (Op.cselc 3#4).eval [v (n+14), v (n+15), v (n+16), v (n+17), v (n+2), v (n+13)]
  select3 : v (n+21) = (Op.cselc 3#4).eval [v (n+14), v (n+15), v (n+16), v (n+17), v (n+3), v (n+13)]

structure RowPositions (defs : List Def) (n : Nat) : Prop where
  andLow : defs[4]? = some (⟨.and, [.id (n+1), .id (n+2)]⟩ : Def)
  andHigh : defs[5]? = some (⟨.and, [.id (n+4), .id (n+3)]⟩ : Def)
  constant : defs[6]? = some (⟨.const 977#64, []⟩ : Def)
  combine : defs[7]? = some (⟨.orr, [.id (n+6), .imm (4294967296#64)]⟩ : Def)
  lowSum : defs[8]? = some (⟨.add3, [.id (n+7), .id n, .imm (0#64)]⟩ : Def)
  lowCarry : defs[11]? = some (⟨.carry3, [.id (n+7), .id n, .imm (0#64)]⟩ : Def)
  highSum : defs[13]? = some (⟨.add3, [.id (n+5), .imm (0#64), .id (n+11)]⟩ : Def)
  compare : defs[16]? = some (⟨.carry3, [.id (n+5), .imm (0#64), .id (n+11)]⟩ : Def)
  select0 : defs[18]? = some (⟨.cselc 3#4, [.id (n+14), .id (n+15), .id (n+16), .id (n+17), .id n, .id (n+8)]⟩ : Def)
  select1 : defs[19]? = some (⟨.cselc 3#4, [.id (n+14), .id (n+15), .id (n+16), .id (n+17), .id (n+1), .id (n+13)]⟩ : Def)
  select2 : defs[20]? = some (⟨.cselc 3#4, [.id (n+14), .id (n+15), .id (n+16), .id (n+17), .id (n+2), .id (n+13)]⟩ : Def)
  select3 : defs[21]? = some (⟨.cselc 3#4, [.id (n+14), .id (n+15), .id (n+16), .id (n+17), .id (n+3), .id (n+13)]⟩ : Def)

private theorem const_eval (values : List (BitVec 64)) (c : BitVec 64) :
    Def.eval values ⟨.const c, []⟩ = c := rfl

theorem equations_of_positions (inputs : List (BitVec 64)) (defs : List Def) (n : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n) :
    Equations (fun i => (evalDefs inputs defs).getD i 0) n := by
  constructor
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 4 (⟨.and, [.id (n+1), .id (n+2)]⟩ : Def) pos.andLow
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 5 (⟨.and, [.id (n+4), .id (n+3)]⟩ : Def) pos.andHigh
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · have h := TableEval.evalDefs_row inputs defs 6 (⟨.const 977#64, []⟩ : Def) pos.constant
      (by rw [lengthEq]; simp [Def.Below,Arg.Below])
    rw [lengthEq,const_eval] at h
    exact h
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 7 (⟨.orr, [.id (n+6), .imm (4294967296#64)]⟩ : Def) pos.combine
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 8 (⟨.add3, [.id (n+7), .id n, .imm (0#64)]⟩ : Def) pos.lowSum
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 11 (⟨.carry3, [.id (n+7), .id n, .imm (0#64)]⟩ : Def) pos.lowCarry
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 13 (⟨.add3, [.id (n+5), .imm (0#64), .id (n+11)]⟩ : Def) pos.highSum
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 16 (⟨.carry3, [.id (n+5), .imm (0#64), .id (n+11)]⟩ : Def) pos.compare
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 18 (⟨.cselc 3#4, [.id (n+14), .id (n+15), .id (n+16), .id (n+17), .id n, .id (n+8)]⟩ : Def) pos.select0
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 19 (⟨.cselc 3#4, [.id (n+14), .id (n+15), .id (n+16), .id (n+17), .id (n+1), .id (n+13)]⟩ : Def) pos.select1
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 20 (⟨.cselc 3#4, [.id (n+14), .id (n+15), .id (n+16), .id (n+17), .id (n+2), .id (n+13)]⟩ : Def) pos.select2
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 21 (⟨.cselc 3#4, [.id (n+14), .id (n+15), .id (n+16), .id (n+17), .id (n+3), .id (n+13)]⟩ : Def) pos.select3
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))

private theorem add3_swap (a b c : BitVec 64) :
    Op.add3.eval [a,b,c] = Op.add3.eval [b,a,c] := by
  change a+b+c = b+a+c
  rw [BitVec.add_comm a b]

private theorem carry3_swap (a b c : BitVec 64) :
    Op.carry3.eval [a,b,c] = Op.carry3.eval [b,a,c] := by
  change b01 (2^64 ≤ a.toNat+b.toNat+c.toNat) = b01 (2^64 ≤ b.toNat+a.toNat+c.toNat)
  simp only [Nat.add_comm a.toNat b.toNat]

private theorem actual_selectCC (n z c v original adjusted : BitVec 64) :
    (Op.cselc 3#4).eval [n,z,c,v,original,adjusted] = selectCC c original adjusted := rfl

#check "CURRENT_DECL rows_coreReduce4"
theorem rows_coreReduce4 (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    resultWords v n = coreReduce4 (inputWords v n) := by
  have k : v (n+7) = BitVec.ofNat 64 correction := by
    rw [rows.combine,rows.constant]
    decide
  have dd : v (n+5) = Op.and.eval [Op.and.eval [v (n+1),v (n+2)],v (n+3)] := by
    rw [rows.andHigh,rows.andLow]
  have lowCarry : v (n+11) = Op.carry3.eval [v n,BitVec.ofNat 64 correction,0#64] := by
    rw [rows.lowCarry,k]
    exact carry3_swap _ _ _
  have lowSum : v (n+8) = Op.add3.eval [v n,BitVec.ofNat 64 correction,0#64] := by
    rw [rows.lowSum,k]
    exact add3_swap _ _ _
  have comparison : v (n+16) = coreComparison (inputWords v n) := by
    rw [rows.compare,dd,lowCarry]
    rfl
  have adjust : adjustedWords (inputWords v n) = ⟨v (n+8),v (n+13),v (n+13),v (n+13)⟩ := by
    dsimp only [adjustedWords,inputWords]
    rw [← dd, ← lowCarry, ← lowSum, ← rows.highSum]
  unfold coreReduce4
  rw [← comparison,adjust]
  simp only [resultWords,inputWords,rows.select0,rows.select1,rows.select2,rows.select3,actual_selectCC]

#check "CURRENT_DECL table_correct"
theorem table_correct (inputs : List (BitVec 64)) (defs : List Def) (n xs : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n)
    (loads : LoadPositions defs xs) (inside : xs+32 ≤ n) :
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value < modulus ∧
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value =
      (inputLimbs inputs xs).value % modulus := by
  have equations := equations_of_positions inputs defs n lengthEq pos
  have loaded := loaded_inputs inputs defs n xs lengthEq loads inside
  rw [rows_coreReduce4 _ n equations,loaded]
  exact coreReduce4_correct _

#print axioms equations_of_positions
#print axioms rows_coreReduce4
#print axioms table_correct
end SecpMath.Mod4SSA
