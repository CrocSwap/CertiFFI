-- Generated small row metadata and proofs; actual compiler specialization is separate.
import SecpMath.CoreAdd
import SecpMath.SubSSA
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
namespace SecpMath.AddSSA
open ArmCertValue
open SecpMath.Addition
open SecpMath.SubSSA (inputLimbs loadedX loadedY LoadPositions loaded_inputs)

def firstWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+4),v (n+9),v (n+18),v (n+24)⟩
def resultWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+47),v (n+52),v (n+57),v (n+62)⟩

/-- These equations are derived from compiler rows, never public hypotheses. -/
structure Equations (v : Nat → BitVec 64) (n : Nat) : Prop where
  d0 : v (n+4) = (Op.add3).eval [v n, v (n+2), 0#64]
  c0 : v (n+7) = (Op.carry3).eval [v n, v (n+2), 0#64]
  d1 : v (n+9) = (Op.add3).eval [v (n+1), v (n+3), v (n+7)]
  c1 : v (n+12) = (Op.carry3).eval [v (n+1), v (n+3), v (n+7)]
  d2 : v (n+18) = (Op.add3).eval [v (n+14), v (n+16), v (n+12)]
  c2 : v (n+21) = (Op.carry3).eval [v (n+14), v (n+16), v (n+12)]
  and12 : v (n+23) = (Op.and).eval [v (n+9), v (n+18)]
  d3 : v (n+24) = (Op.add3).eval [v (n+15), v (n+17), v (n+21)]
  c3 : v (n+27) = (Op.carry3).eval [v (n+15), v (n+17), v (n+21)]
  and123 : v (n+29) = (Op.and).eval [v (n+23), v (n+24)]
  original : v (n+30) = (Op.add3).eval [0#64, 0#64, v (n+27)]
  constant : v (n+31) = 977#64
  combine : v (n+32) = (Op.orr).eval [v (n+31), 4294967296#64]
  low : v (n+35) = (Op.carry3).eval [v (n+4), v (n+32), 0#64]
  test : v (n+39) = (Op.carry3).eval [v (n+29), 0#64, v (n+35)]
  zf : v (n+43) = (Op.add3Z).eval [v (n+30), 0#64, v (n+39)]
  select : v (n+46) = (Op.cselc 1#4).eval [v (n+42), v (n+43), v (n+44), v (n+45), v (n+32), 0#64]
  r0 : v (n+47) = (Op.add3).eval [v (n+4), v (n+46), 0#64]
  rc0 : v (n+50) = (Op.carry3).eval [v (n+4), v (n+46), 0#64]
  r1 : v (n+52) = (Op.add3).eval [v (n+9), 0#64, v (n+50)]
  rc1 : v (n+55) = (Op.carry3).eval [v (n+9), 0#64, v (n+50)]
  r2 : v (n+57) = (Op.add3).eval [v (n+18), 0#64, v (n+55)]
  rc2 : v (n+60) = (Op.carry3).eval [v (n+18), 0#64, v (n+55)]
  r3 : v (n+62) = (Op.add3).eval [v (n+24), 0#64, v (n+60)]

structure RowPositions (defs : List Def) (n : Nat) : Prop where
  d0 : defs[4]? = some (⟨.add3, [.id n, .id (n+2), .imm 0#64]⟩ : Def)
  c0 : defs[7]? = some (⟨.carry3, [.id n, .id (n+2), .imm 0#64]⟩ : Def)
  d1 : defs[9]? = some (⟨.add3, [.id (n+1), .id (n+3), .id (n+7)]⟩ : Def)
  c1 : defs[12]? = some (⟨.carry3, [.id (n+1), .id (n+3), .id (n+7)]⟩ : Def)
  d2 : defs[18]? = some (⟨.add3, [.id (n+14), .id (n+16), .id (n+12)]⟩ : Def)
  c2 : defs[21]? = some (⟨.carry3, [.id (n+14), .id (n+16), .id (n+12)]⟩ : Def)
  and12 : defs[23]? = some (⟨.and, [.id (n+9), .id (n+18)]⟩ : Def)
  d3 : defs[24]? = some (⟨.add3, [.id (n+15), .id (n+17), .id (n+21)]⟩ : Def)
  c3 : defs[27]? = some (⟨.carry3, [.id (n+15), .id (n+17), .id (n+21)]⟩ : Def)
  and123 : defs[29]? = some (⟨.and, [.id (n+23), .id (n+24)]⟩ : Def)
  original : defs[30]? = some (⟨.add3, [.imm 0#64, .imm 0#64, .id (n+27)]⟩ : Def)
  constant : defs[31]? = some (⟨.const 977#64, []⟩ : Def)
  combine : defs[32]? = some (⟨.orr, [.id (n+31), .imm 4294967296#64]⟩ : Def)
  low : defs[35]? = some (⟨.carry3, [.id (n+4), .id (n+32), .imm 0#64]⟩ : Def)
  test : defs[39]? = some (⟨.carry3, [.id (n+29), .imm 0#64, .id (n+35)]⟩ : Def)
  zf : defs[43]? = some (⟨.add3Z, [.id (n+30), .imm 0#64, .id (n+39)]⟩ : Def)
  select : defs[46]? = some (⟨.cselc 1#4, [.id (n+42), .id (n+43), .id (n+44), .id (n+45), .id (n+32), .imm 0#64]⟩ : Def)
  r0 : defs[47]? = some (⟨.add3, [.id (n+4), .id (n+46), .imm 0#64]⟩ : Def)
  rc0 : defs[50]? = some (⟨.carry3, [.id (n+4), .id (n+46), .imm 0#64]⟩ : Def)
  r1 : defs[52]? = some (⟨.add3, [.id (n+9), .imm 0#64, .id (n+50)]⟩ : Def)
  rc1 : defs[55]? = some (⟨.carry3, [.id (n+9), .imm 0#64, .id (n+50)]⟩ : Def)
  r2 : defs[57]? = some (⟨.add3, [.id (n+18), .imm 0#64, .id (n+55)]⟩ : Def)
  rc2 : defs[60]? = some (⟨.carry3, [.id (n+18), .imm 0#64, .id (n+55)]⟩ : Def)
  r3 : defs[62]? = some (⟨.add3, [.id (n+24), .imm 0#64, .id (n+60)]⟩ : Def)

private theorem const_eval (values : List (BitVec 64)) (c : BitVec 64) :
    (⟨.const c,[]⟩ : Def).eval values = c := rfl

theorem equations_of_positions (inputs : List (BitVec 64)) (defs : List Def) (n : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n) :
    Equations (fun i => (evalDefs inputs defs).getD i 0) n := by
  constructor
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 4 (⟨.add3, [.id n, .id (n+2), .imm 0#64]⟩ : Def) pos.d0
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 7 (⟨.carry3, [.id n, .id (n+2), .imm 0#64]⟩ : Def) pos.c0
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 9 (⟨.add3, [.id (n+1), .id (n+3), .id (n+7)]⟩ : Def) pos.d1
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 12 (⟨.carry3, [.id (n+1), .id (n+3), .id (n+7)]⟩ : Def) pos.c1
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 18 (⟨.add3, [.id (n+14), .id (n+16), .id (n+12)]⟩ : Def) pos.d2
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 21 (⟨.carry3, [.id (n+14), .id (n+16), .id (n+12)]⟩ : Def) pos.c2
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 23 (⟨.and, [.id (n+9), .id (n+18)]⟩ : Def) pos.and12
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 24 (⟨.add3, [.id (n+15), .id (n+17), .id (n+21)]⟩ : Def) pos.d3
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 27 (⟨.carry3, [.id (n+15), .id (n+17), .id (n+21)]⟩ : Def) pos.c3
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 29 (⟨.and, [.id (n+23), .id (n+24)]⟩ : Def) pos.and123
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 30 (⟨.add3, [.imm 0#64, .imm 0#64, .id (n+27)]⟩ : Def) pos.original
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · have h := TableEval.evalDefs_row inputs defs 31 (⟨.const 977#64, []⟩ : Def) pos.constant
      (by rw [lengthEq]; simp [Def.Below, Arg.Below])
    rw [lengthEq,const_eval] at h
    exact h
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 32 (⟨.orr, [.id (n+31), .imm 4294967296#64]⟩ : Def) pos.combine
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 35 (⟨.carry3, [.id (n+4), .id (n+32), .imm 0#64]⟩ : Def) pos.low
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 39 (⟨.carry3, [.id (n+29), .imm 0#64, .id (n+35)]⟩ : Def) pos.test
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 43 (⟨.add3Z, [.id (n+30), .imm 0#64, .id (n+39)]⟩ : Def) pos.zf
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 46 (⟨.cselc 1#4, [.id (n+42), .id (n+43), .id (n+44), .id (n+45), .id (n+32), .imm 0#64]⟩ : Def) pos.select
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 47 (⟨.add3, [.id (n+4), .id (n+46), .imm 0#64]⟩ : Def) pos.r0
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 50 (⟨.carry3, [.id (n+4), .id (n+46), .imm 0#64]⟩ : Def) pos.rc0
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 52 (⟨.add3, [.id (n+9), .imm 0#64, .id (n+50)]⟩ : Def) pos.r1
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 55 (⟨.carry3, [.id (n+9), .imm 0#64, .id (n+50)]⟩ : Def) pos.rc1
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 57 (⟨.add3, [.id (n+18), .imm 0#64, .id (n+55)]⟩ : Def) pos.r2
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 60 (⟨.carry3, [.id (n+18), .imm 0#64, .id (n+55)]⟩ : Def) pos.rc2
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))
  · simpa only [lengthEq,Def.eval,List.map_cons,List.map_nil,Arg.eval] using
      (TableEval.evalDefs_row inputs defs 62 (⟨.add3, [.id (n+24), .imm 0#64, .id (n+60)]⟩ : Def) pos.r3
        (by rw [lengthEq]; simp [Def.Below,Arg.Below] <;> omega))

theorem first_chain (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    Addition.coreChain4 (loadedX v n) (loadedY v n) = (firstWords v n,v (n+27)) := by
  simp only [Addition.coreChain4,loadedX,loadedY,firstWords,
    ← rows.d0,← rows.c0,← rows.d1,← rows.c1,← rows.d2,← rows.c2,← rows.d3,← rows.c3]

theorem select_ne_ignores_flags (nf zf cf vf k : BitVec 64) :
    (Op.cselc 1#4).eval [nf,zf,cf,vf,k,0#64] =
      (Op.cselc 1#4).eval [0#64,zf,0#64,0#64,k,0#64] := rfl

theorem selected_value (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    v (n+46) = selectedCorrection (loadedX v n) (loadedY v n) := by
  rw [rows.select,select_ne_ignores_flags,rows.zf,rows.original,rows.test,
    rows.low,rows.and123,rows.and12,rows.combine,rows.constant,correction_constant]
  unfold selectedCorrection
  rw [first_chain v n rows]
  rfl

theorem rows_coreAdd4 (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    resultWords v n = coreAdd4 (loadedX v n) (loadedY v n) := by
  unfold coreAdd4
  rw [first_chain v n rows,← selected_value v n rows]
  simp only [Addition.coreChain4,firstWords,resultWords,
    ← rows.r0,← rows.rc0,← rows.r1,← rows.rc1,← rows.r2,← rows.rc2,← rows.r3]

/-- Actual original input bytes and internally derived arithmetic rows suffice
for the table result. No Sail run, future physical state or ABI is asserted. -/
theorem table_correct (inputs : List (BitVec 64)) (defs : List Def) (n xs ys : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n)
    (loads : LoadPositions defs xs ys) (xInside : xs+32 ≤ n) (yInside : ys+32 ≤ n)
    (hx : (inputLimbs inputs xs).value < modulus)
    (hy : (inputLimbs inputs ys).value < modulus) :
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value < modulus ∧
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value =
      ((inputLimbs inputs xs).value+(inputLimbs inputs ys).value)%modulus := by
  have equations := equations_of_positions inputs defs n lengthEq pos
  have loaded := loaded_inputs inputs defs n xs ys lengthEq loads xInside yInside
  rw [rows_coreAdd4 _ n equations,loaded.1,loaded.2]
  exact coreAdd4_correct _ _ hx hy

#print axioms equations_of_positions
#print axioms rows_coreAdd4
#print axioms table_correct
end SecpMath.AddSSA
