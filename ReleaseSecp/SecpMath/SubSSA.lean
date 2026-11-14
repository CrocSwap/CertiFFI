-- Arithmetic consumer for the subtraction SSA rows. Actual row certificates
-- and entry-byte assembly are separate from these generic equations.
import SecpMath.CoreSub
import SecpMath.TableEval

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace SecpMath.SubSSA
open ArmCertValue

/-- One actual compiler load row, assembling eight separately snapshotted bytes. -/
def inputWordDef (start : Nat) : Def :=
  ⟨.asm8 [0,0,0,0,0,0,0,0],
    [.id start, .id (start+1), .id (start+2), .id (start+3),
     .id (start+4), .id (start+5), .id (start+6), .id (start+7)]⟩

def inputWord (inputs : List (BitVec 64)) (start : Nat) : BitVec 64 :=
  (inputWordDef start).eval inputs

/-- Four little-endian words made from the original 32 input-byte slots. -/
def inputLimbs (inputs : List (BitVec 64)) (start : Nat) : LimbWords :=
  ⟨inputWord inputs start, inputWord inputs (start+8),
   inputWord inputs (start+16), inputWord inputs (start+24)⟩

theorem inputWordDef_below (start bound : Nat) (inside : start + 8 ≤ bound) :
    (inputWordDef start).Below bound := by
  simp only [inputWordDef, Def.Below, List.mem_cons, List.not_mem_nil, or_false]
  intro a member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    change _ < bound <;> omega

theorem inputWord_preserved (inputs : List (BitVec 64)) (defs : List Def) (start : Nat)
    (inside : start + 8 ≤ inputs.length) :
    inputWord (evalDefs inputs defs) start = inputWord inputs start := by
  apply TableEval.def_eval_same inputs.length
  · intro i hi
    exact TableEval.extend_getD_old inputs defs i hi
  · exact inputWordDef_below start inputs.length inside

theorem inputLimbs_preserved (inputs : List (BitVec 64)) (defs : List Def) (start : Nat)
    (inside : start + 32 ≤ inputs.length) :
    inputLimbs (evalDefs inputs defs) start = inputLimbs inputs start := by
  simp only [inputLimbs,
    inputWord_preserved inputs defs start (by omega),
    inputWord_preserved inputs defs (start+8) (by omega),
    inputWord_preserved inputs defs (start+16) (by omega),
    inputWord_preserved inputs defs (start+24) (by omega)]

def loadedX (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v n, v (n+1), v (n+14), v (n+15)⟩

def loadedY (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+2), v (n+3), v (n+16), v (n+17)⟩

def firstWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+4), v (n+9), v (n+18), v (n+23)⟩

def resultWords (v : Nat → BitVec 64) (n : Nat) : LimbWords :=
  ⟨v (n+31), v (n+36), v (n+41), v (n+46)⟩

/-- Input-load row identities, also derived inside the arithmetic consumer. -/
structure LoadPositions (defs : List Def) (xs ys : Nat) : Prop where
  x0 : defs[0]? = some (inputWordDef xs)
  x1 : defs[1]? = some (inputWordDef (xs+8))
  x2 : defs[14]? = some (inputWordDef (xs+16))
  x3 : defs[15]? = some (inputWordDef (xs+24))
  y0 : defs[2]? = some (inputWordDef ys)
  y1 : defs[3]? = some (inputWordDef (ys+8))
  y2 : defs[16]? = some (inputWordDef (ys+16))
  y3 : defs[17]? = some (inputWordDef (ys+24))

theorem loaded_input_word (inputs : List (BitVec 64)) (defs : List Def) (i start : Nat)
    (row : defs[i]? = some (inputWordDef start)) (inside : start + 8 ≤ inputs.length) :
    (evalDefs inputs defs).getD (inputs.length + i) 0 = inputWord inputs start := by
  have eq := TableEval.evalDefs_row inputs defs i (inputWordDef start) row
    (inputWordDef_below start (inputs.length + i) (by omega))
  exact eq.trans (inputWord_preserved inputs defs start inside)

/-- All four input words retain their original entry-byte snapshots, including
in-place/aliased layouts. No input-memory frame after stores is asserted. -/
theorem loaded_inputs (inputs : List (BitVec 64)) (defs : List Def) (n xs ys : Nat)
    (lengthEq : inputs.length = n) (pos : LoadPositions defs xs ys)
    (xInside : xs+32 ≤ n) (yInside : ys+32 ≤ n) :
    loadedX (fun i => (evalDefs inputs defs).getD i 0) n = inputLimbs inputs xs ∧
    loadedY (fun i => (evalDefs inputs defs).getD i 0) n = inputLimbs inputs ys := by
  subst n
  have firstX := loaded_input_word inputs defs 0 xs pos.x0 (by omega)
  simp only [Nat.add_zero] at firstX
  constructor
  · simp only [loadedX, inputLimbs,
      firstX,
      loaded_input_word inputs defs 1 (xs+8) pos.x1 (by omega),
      loaded_input_word inputs defs 14 (xs+16) pos.x2 (by omega),
      loaded_input_word inputs defs 15 (xs+24) pos.x3 (by omega)]
  · simp only [loadedY, inputLimbs,
      loaded_input_word inputs defs 2 ys pos.y0 (by omega),
      loaded_input_word inputs defs 3 (ys+8) pos.y1 (by omega),
      loaded_input_word inputs defs 16 (ys+16) pos.y2 (by omega),
      loaded_input_word inputs defs 17 (ys+24) pos.y3 (by omega)]

/-- Only the arithmetic-relevant rows; all are to be derived from the actual
compiler table, never supplied as deployment/caller hypotheses. -/
structure Equations (v : Nat → BitVec 64) (n : Nat) : Prop where
  d0 : v (n+4) = Op.sbc3.eval [v n, v (n+2), 1#64]
  c0 : v (n+7) = Op.sbc3C.eval [v n, v (n+2), 1#64]
  d1 : v (n+9) = Op.sbc3.eval [v (n+1), v (n+3), v (n+7)]
  c1 : v (n+12) = Op.sbc3C.eval [v (n+1), v (n+3), v (n+7)]
  d2 : v (n+18) = Op.sbc3.eval [v (n+14), v (n+16), v (n+12)]
  c2 : v (n+21) = Op.sbc3C.eval [v (n+14), v (n+16), v (n+12)]
  d3 : v (n+23) = Op.sbc3.eval [v (n+15), v (n+17), v (n+21)]
  c3 : v (n+26) = Op.sbc3C.eval [v (n+15), v (n+17), v (n+21)]
  constant : v (n+28) = 977#64
  combine : v (n+29) = Op.orr.eval [v (n+28), 4294967296#64]
  select : v (n+30) = (Op.cselc 3#4).eval
    [v (n+24), v (n+25), v (n+26), v (n+27), v (n+29), 0#64]
  r0 : v (n+31) = Op.sbc3.eval [v (n+4), v (n+30), 1#64]
  rc0 : v (n+34) = Op.sbc3C.eval [v (n+4), v (n+30), 1#64]
  r1 : v (n+36) = Op.sbc3.eval [v (n+9), 0#64, v (n+34)]
  rc1 : v (n+39) = Op.sbc3C.eval [v (n+9), 0#64, v (n+34)]
  r2 : v (n+41) = Op.sbc3.eval [v (n+18), 0#64, v (n+39)]
  rc2 : v (n+44) = Op.sbc3C.eval [v (n+18), 0#64, v (n+39)]
  r3 : v (n+46) = Op.sbc3.eval [v (n+23), 0#64, v (n+44)]

/-- Exact positions in a compiler table. Consumers derive this record from the
producer's small kernel-checked lookup certificates; it is not a release input. -/
structure RowPositions (defs : List Def) (n : Nat) : Prop where
  d0 : defs[4]? = some (⟨.sbc3, [.id n, .id (n+2), .imm 1#64]⟩ : Def)
  c0 : defs[7]? = some (⟨.sbc3C, [.id n, .id (n+2), .imm 1#64]⟩ : Def)
  d1 : defs[9]? = some (⟨.sbc3, [.id (n+1), .id (n+3), .id (n+7)]⟩ : Def)
  c1 : defs[12]? = some (⟨.sbc3C, [.id (n+1), .id (n+3), .id (n+7)]⟩ : Def)
  d2 : defs[18]? = some (⟨.sbc3, [.id (n+14), .id (n+16), .id (n+12)]⟩ : Def)
  c2 : defs[21]? = some (⟨.sbc3C, [.id (n+14), .id (n+16), .id (n+12)]⟩ : Def)
  d3 : defs[23]? = some (⟨.sbc3, [.id (n+15), .id (n+17), .id (n+21)]⟩ : Def)
  c3 : defs[26]? = some (⟨.sbc3C, [.id (n+15), .id (n+17), .id (n+21)]⟩ : Def)
  constant : defs[28]? = some (⟨.const 977#64, []⟩ : Def)
  combine : defs[29]? = some (⟨.orr, [.id (n+28), .imm 4294967296#64]⟩ : Def)
  select : defs[30]? = some (⟨.cselc 3#4, [.id (n+24), .id (n+25), .id (n+26), .id (n+27), .id (n+29), .imm 0#64]⟩ : Def)
  r0 : defs[31]? = some (⟨.sbc3, [.id (n+4), .id (n+30), .imm 1#64]⟩ : Def)
  rc0 : defs[34]? = some (⟨.sbc3C, [.id (n+4), .id (n+30), .imm 1#64]⟩ : Def)
  r1 : defs[36]? = some (⟨.sbc3, [.id (n+9), .imm 0#64, .id (n+34)]⟩ : Def)
  rc1 : defs[39]? = some (⟨.sbc3C, [.id (n+9), .imm 0#64, .id (n+34)]⟩ : Def)
  r2 : defs[41]? = some (⟨.sbc3, [.id (n+18), .imm 0#64, .id (n+39)]⟩ : Def)
  rc2 : defs[44]? = some (⟨.sbc3C, [.id (n+18), .imm 0#64, .id (n+39)]⟩ : Def)
  r3 : defs[46]? = some (⟨.sbc3, [.id (n+23), .imm 0#64, .id (n+44)]⟩ : Def)

private theorem const_eval (values : List (BitVec 64)) (c : BitVec 64) :
    (⟨.const c, []⟩ : Def).eval values = c := rfl

/-- Discharge the arithmetic equations from actual table rows. -/
theorem equations_of_positions (inputs : List (BitVec 64)) (defs : List Def) (n : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n) :
    Equations (fun i => (evalDefs inputs defs).getD i 0) n := by
  constructor
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 4 (⟨.sbc3, [.id n, .id (n+2), .imm 1#64]⟩ : Def) pos.d0
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 7 (⟨.sbc3C, [.id n, .id (n+2), .imm 1#64]⟩ : Def) pos.c0
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 9 (⟨.sbc3, [.id (n+1), .id (n+3), .id (n+7)]⟩ : Def) pos.d1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 12 (⟨.sbc3C, [.id (n+1), .id (n+3), .id (n+7)]⟩ : Def) pos.c1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 18 (⟨.sbc3, [.id (n+14), .id (n+16), .id (n+12)]⟩ : Def) pos.d2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 21 (⟨.sbc3C, [.id (n+14), .id (n+16), .id (n+12)]⟩ : Def) pos.c2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 23 (⟨.sbc3, [.id (n+15), .id (n+17), .id (n+21)]⟩ : Def) pos.d3
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 26 (⟨.sbc3C, [.id (n+15), .id (n+17), .id (n+21)]⟩ : Def) pos.c3
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · have h := TableEval.evalDefs_row inputs defs 28 (⟨.const 977#64, []⟩ : Def) pos.constant
      (by rw [lengthEq]; simp [Def.Below, Arg.Below])
    rw [lengthEq, const_eval] at h
    exact h
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 29 (⟨.orr, [.id (n+28), .imm 4294967296#64]⟩ : Def) pos.combine
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 30 (⟨.cselc 3#4, [.id (n+24), .id (n+25), .id (n+26), .id (n+27), .id (n+29), .imm 0#64]⟩ : Def) pos.select
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 31 (⟨.sbc3, [.id (n+4), .id (n+30), .imm 1#64]⟩ : Def) pos.r0
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 34 (⟨.sbc3C, [.id (n+4), .id (n+30), .imm 1#64]⟩ : Def) pos.rc0
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 36 (⟨.sbc3, [.id (n+9), .imm 0#64, .id (n+34)]⟩ : Def) pos.r1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 39 (⟨.sbc3C, [.id (n+9), .imm 0#64, .id (n+34)]⟩ : Def) pos.rc1
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 41 (⟨.sbc3, [.id (n+18), .imm 0#64, .id (n+39)]⟩ : Def) pos.r2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 44 (⟨.sbc3C, [.id (n+18), .imm 0#64, .id (n+39)]⟩ : Def) pos.rc2
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))
  · simpa only [lengthEq, Def.eval, List.map_cons, List.map_nil, Arg.eval] using
      (TableEval.evalDefs_row inputs defs 46 (⟨.sbc3, [.id (n+23), .imm 0#64, .id (n+44)]⟩ : Def) pos.r3
        (by rw [lengthEq]; simp [Def.Below, Arg.Below] <;> omega))

theorem first_chain (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    coreChain4 (loadedX v n) (loadedY v n) = (firstWords v n, v (n+26)) := by
  simp only [coreChain4, loadedX, loadedY, firstWords,
    ← rows.d0, ← rows.c0, ← rows.d1, ← rows.c1,
    ← rows.d2, ← rows.c2, ← rows.d3, ← rows.c3]

theorem select_correction (nf zf cf vf : BitVec 64) :
    (Op.cselc 3#4).eval [nf, zf, cf, vf, BitVec.ofNat 64 correction, 0#64] =
      if cf == 0#64 then BitVec.ofNat 64 correction else 0#64 := by
  change (if !(cf != 0#64) then BitVec.ofNat 64 correction else 0#64) = _
  simp only [bne, Bool.not_not]

theorem selected_value (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    v (n+30) = if v (n+26) == 0#64 then BitVec.ofNat 64 correction else 0#64 := by
  rw [rows.select, rows.combine, rows.constant, correction_constant]
  exact select_correction _ _ _ _

theorem rows_coreSub4 (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n) :
    resultWords v n = coreSub4 (loadedX v n) (loadedY v n) := by
  unfold coreSub4
  rw [first_chain v n rows]
  simp only [coreChain4, firstWords, correctionWords,
    ← selected_value v n rows, ← rows.r0, ← rows.rc0, ← rows.r1,
    ← rows.rc1, ← rows.r2, ← rows.rc2, ← rows.r3, resultWords]

/-- The arithmetic result once actual compiler rows and loaded input limbs
have been connected. No Sail execution, layout, final memory or ABI is asserted. -/
theorem rows_modular_sub (v : Nat → BitVec 64) (n : Nat) (rows : Equations v n)
    (hx : (loadedX v n).value < modulus) (hy : (loadedY v n).value < modulus) :
    (resultWords v n).value = subCore modulus (loadedX v n).value (loadedY v n).value := by
  rw [rows_coreSub4 v n rows]
  exact coreSub4_eq_core _ _ hx hy

/-- Generic consumer of the actual producer row identities. Input bounds concern
the ORIGINAL byte slots. Row/load identities are discharged by compiler proofs
when this theorem is instantiated for a function/layout. -/
theorem table_correct (inputs : List (BitVec 64)) (defs : List Def) (n xs ys : Nat)
    (lengthEq : inputs.length = n) (pos : RowPositions defs n)
    (loads : LoadPositions defs xs ys) (xInside : xs+32 ≤ n) (yInside : ys+32 ≤ n)
    (hx : (inputLimbs inputs xs).value < modulus)
    (hy : (inputLimbs inputs ys).value < modulus) :
    (resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value < modulus ∧
    ((resultWords (fun i => (evalDefs inputs defs).getD i 0) n).value : Int) =
      (((inputLimbs inputs xs).value : Int) - ((inputLimbs inputs ys).value : Int)) %
        (modulus : Int) := by
  have equations := equations_of_positions inputs defs n lengthEq pos
  have loaded := loaded_inputs inputs defs n xs ys lengthEq loads xInside yInside
  have result := rows_coreSub4 (fun i => (evalDefs inputs defs).getD i 0) n equations
  rw [loaded.1, loaded.2] at result
  rw [result]
  exact coreSub4_correct _ _ hx hy

#print axioms loaded_inputs
#print axioms equations_of_positions
#print axioms first_chain
#print axioms inputLimbs_preserved
#print axioms rows_coreSub4
#print axioms rows_modular_sub
#print axioms table_correct

end SecpMath.SubSSA
