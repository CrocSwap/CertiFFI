-- Exact row-based negation consumer. No native execution or future state input.
import SecpMath.Neg
import SecpMath.SubSSA
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
namespace SecpMath.NegSSA
open ArmCertValue SecpMath.Negation
open SecpMath.SubSSA (inputWordDef inputLimbs loaded_input_word)

def inputWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v n,v (n+1),v (n+3),v (n+4)⟩
def baseWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+16),v (n+11),v (n+11),v (n+11)⟩
def resultWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+17),v (n+22),v (n+27),v (n+32)⟩

structure LoadPositions (defs : List Def) (xs : Nat) : Prop where
  w0 : defs[0]? = some (inputWordDef xs)
  w1 : defs[1]? = some (inputWordDef (xs+8))
  w2 : defs[3]? = some (inputWordDef (xs+16))
  w3 : defs[4]? = some (inputWordDef (xs+24))

theorem loaded_inputs (inputs : List (BitVec 64)) (defs : List Def) (n xs : Nat)
    (lengthEq : inputs.length = n) (pos : LoadPositions defs xs) (inside : xs+32 ≤ n) :
    inputWords (fun i => (evalDefs inputs defs).getD i 0) n = inputLimbs inputs xs := by
  subst n
  have first := loaded_input_word inputs defs 0 xs pos.w0 (by omega)
  simp only [Nat.add_zero] at first
  simp only [inputWords,inputLimbs,first,
    loaded_input_word inputs defs 1 (xs+8) pos.w1 (by omega),
    loaded_input_word inputs defs 3 (xs+16) pos.w2 (by omega),
    loaded_input_word inputs defs 4 (xs+24) pos.w3 (by omega)]

structure Equations (v : Nat → BitVec 64) (n : Nat) : Prop where
  or0 : v (n+2) = (Op.orrShl 0).eval [v n, v (n+1)]
  or1 : v (n+5) = (Op.orrShl 0).eval [v (n+2), v (n+3)]
  or2 : v (n+6) = (Op.orrShl 0).eval [v (n+5), v (n+4)]
  zf : v (n+8) = (Op.sbc3Z).eval [v (n+6), 0#64, 1#64]
  mask : v (n+11) = (Op.cselc 0#4).eval [v (n+7), v (n+8), v (n+9), v (n+10), 0#64, ~~~(0#64)]
  constant : v (n+12) = 976#64
  combine : v (n+13) = (Op.orr).eval [v (n+12), 4294967296#64]
  notConstant : v (n+14) = (Op.not).eval [v (n+13)]
  bic : v (n+15) = (Op.and).eval [v (n+11), v (n+14)]
  addZero : v (n+16) = (Op.add).eval [v (n+15), 0#64]
  d0 : v (n+17) = (Op.sbc3).eval [v (n+16), v n, 1#64]
  c0 : v (n+20) = (Op.sbc3C).eval [v (n+16), v n, 1#64]
  d1 : v (n+22) = (Op.sbc3).eval [v (n+11), v (n+1), v (n+20)]
  c1 : v (n+25) = (Op.sbc3C).eval [v (n+11), v (n+1), v (n+20)]
  d2 : v (n+27) = (Op.sbc3).eval [v (n+11), v (n+3), v (n+25)]
  c2 : v (n+30) = (Op.sbc3C).eval [v (n+11), v (n+3), v (n+25)]
  d3 : v (n+32) = (Op.sbc3).eval [v (n+11), v (n+4), v (n+30)]

structure RowPositions (defs : List Def) (n : Nat) : Prop where
  or0 : defs[2]? = some (⟨.orrShl 0, [.id n, .id (n+1)]⟩ : Def)
  or1 : defs[5]? = some (⟨.orrShl 0, [.id (n+2), .id (n+3)]⟩ : Def)
  or2 : defs[6]? = some (⟨.orrShl 0, [.id (n+5), .id (n+4)]⟩ : Def)
  zf : defs[8]? = some (⟨.sbc3Z, [.id (n+6), .imm (0#64), .imm (1#64)]⟩ : Def)
  mask : defs[11]? = some (⟨.cselc 0#4, [.id (n+7), .id (n+8), .id (n+9), .id (n+10), .imm (0#64), .imm (~~~(0#64))]⟩ : Def)
  constant : defs[12]? = some (⟨.const 976#64, []⟩ : Def)
  combine : defs[13]? = some (⟨.orr, [.id (n+12), .imm (4294967296#64)]⟩ : Def)
  notConstant : defs[14]? = some (⟨.not, [.id (n+13)]⟩ : Def)
  bic : defs[15]? = some (⟨.and, [.id (n+11), .id (n+14)]⟩ : Def)
  addZero : defs[16]? = some (⟨.add, [.id (n+15), .imm (0#64)]⟩ : Def)
  d0 : defs[17]? = some (⟨.sbc3, [.id (n+16), .id n, .imm (1#64)]⟩ : Def)
  c0 : defs[20]? = some (⟨.sbc3C, [.id (n+16), .id n, .imm (1#64)]⟩ : Def)
  d1 : defs[22]? = some (⟨.sbc3, [.id (n+11), .id (n+1), .id (n+20)]⟩ : Def)
  c1 : defs[25]? = some (⟨.sbc3C, [.id (n+11), .id (n+1), .id (n+20)]⟩ : Def)
  d2 : defs[27]? = some (⟨.sbc3, [.id (n+11), .id (n+3), .id (n+25)]⟩ : Def)
  c2 : defs[30]? = some (⟨.sbc3C, [.id (n+11), .id (n+3), .id (n+25)]⟩ : Def)
  d3 : defs[32]? = some (⟨.sbc3, [.id (n+11), .id (n+4), .id (n+30)]⟩ : Def)

private theorem const_eval (values : List (BitVec 64)) (c : BitVec 64) :
    (⟨.const c,[]⟩ : Def).eval values = c := rfl

theorem equations_of_positions (inputs : List (BitVec 64)) (defs : List Def) (n : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n) :
    Equations (fun i => (evalDefs inputs defs).getD i 0) n := by
  constructor
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 2 (⟨.orrShl 0, [.id n, .id (n+1)]⟩ : Def) pos.or0
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 5 (⟨.orrShl 0, [.id (n+2), .id (n+3)]⟩ : Def) pos.or1
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 6 (⟨.orrShl 0, [.id (n+5), .id (n+4)]⟩ : Def) pos.or2
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 8 (⟨.sbc3Z, [.id (n+6), .imm (0#64), .imm (1#64)]⟩ : Def) pos.zf
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 11 (⟨.cselc 0#4, [.id (n+7), .id (n+8), .id (n+9), .id (n+10), .imm (0#64), .imm (~~~(0#64))]⟩ : Def) pos.mask
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · have h := TableEval.evalDefs_row inputs defs 12 (⟨.const 976#64, []⟩ : Def) pos.constant
      (by rw [lengthEq]; simp [Def.Below,Arg.Below])
    rw [lengthEq,const_eval] at h
    exact h
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 13 (⟨.orr, [.id (n+12), .imm (4294967296#64)]⟩ : Def) pos.combine
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 14 (⟨.not, [.id (n+13)]⟩ : Def) pos.notConstant
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 15 (⟨.and, [.id (n+11), .id (n+14)]⟩ : Def) pos.bic
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 16 (⟨.add, [.id (n+15), .imm (0#64)]⟩ : Def) pos.addZero
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 17 (⟨.sbc3, [.id (n+16), .id n, .imm (1#64)]⟩ : Def) pos.d0
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 20 (⟨.sbc3C, [.id (n+16), .id n, .imm (1#64)]⟩ : Def) pos.c0
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 22 (⟨.sbc3, [.id (n+11), .id (n+1), .id (n+20)]⟩ : Def) pos.d1
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 25 (⟨.sbc3C, [.id (n+11), .id (n+1), .id (n+20)]⟩ : Def) pos.c1
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 27 (⟨.sbc3, [.id (n+11), .id (n+3), .id (n+25)]⟩ : Def) pos.d2
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 30 (⟨.sbc3C, [.id (n+11), .id (n+3), .id (n+25)]⟩ : Def) pos.c2
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 32 (⟨.sbc3, [.id (n+11), .id (n+4), .id (n+30)]⟩ : Def) pos.d3
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))

private theorem add_zero (word : BitVec 64) : Op.add.eval [word,0#64] = word := by
  change word+0#64 = word
  simp

theorem mask_value (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    v (n+11) = maskWord (inputWords v n) := by
  rw [rows.mask,csetm_ne,rows.zf,rows.or2,rows.or1,rows.or0,
    orrShl_zero,orrShl_zero,orrShl_zero]
  rfl

theorem base_low (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    v (n+16) = Op.and.eval [v (n+11),Op.not.eval [Op.orr.eval [976#64,4294967296#64]]] := by
  rw [rows.addZero,add_zero,rows.bic,rows.notConstant,rows.combine,rows.constant]

theorem base_words (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    baseWords v n = modulusWords (inputWords v n) := by
  simp only [baseWords,modulusWords,← mask_value v n rows,← base_low v n rows]

theorem rows_coreNeg4 (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    resultWords v n = coreNeg4 (inputWords v n) := by
  unfold coreNeg4
  rw [← base_words v n rows]
  simp only [SecpMath.coreChain4,baseWords,inputWords,resultWords,
    ← rows.d0,← rows.c0,← rows.d1,← rows.c1,← rows.d2,← rows.c2,← rows.d3]

#check "CURRENT_DECL table_correct"
theorem table_correct (inputs : List (BitVec 64)) (defs : List Def) (n xs : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n)
    (loads : LoadPositions defs xs) (inside : xs+32 ≤ n)
    (hx : (inputLimbs inputs xs).value < modulus) :
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value < modulus ∧
    ((resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value : Int) =
      (-((inputLimbs inputs xs).value : Int)) % (modulus : Int) := by
  have equations := equations_of_positions inputs defs n lengthEq pos
  have loaded := loaded_inputs inputs defs n xs lengthEq loads inside
  rw [rows_coreNeg4 _ n equations,loaded]
  exact coreNeg4_correct _ hx

#print axioms equations_of_positions
#print axioms rows_coreNeg4
#print axioms table_correct
end SecpMath.NegSSA
