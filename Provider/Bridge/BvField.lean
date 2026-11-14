/-! Bridge.BvField (a design decision (a), d194 LNSym-free): the bv_field tactic, Lean core only. The former
`import Arm.Exec` (LNSym) is dropped; nothing in this module used it. -/
open BitVec

macro "bv_field" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  repeat (first | (exfalso; omega) | split)
  all_goals (first | (exfalso; omega) | (congr 1; omega) | rfl)))

example (sf : BitVec 1) (opc : BitVec 2) (hw : BitVec 2) (imm16 : BitVec 16) (Rd : BitVec 5) :
    extractLsb' 5 16 (sf ++ opc ++ 37#6 ++ hw ++ imm16 ++ Rd) = imm16 := by bv_field
example (sf : BitVec 1) (opc : BitVec 2) (hw : BitVec 2) (imm16 : BitVec 16) (Rd : BitVec 5) :
    extractLsb' 0 5 (sf ++ opc ++ 37#6 ++ hw ++ imm16 ++ Rd) = Rd := by bv_field
example (sf : BitVec 1) (opc : BitVec 2) (hw : BitVec 2) (imm16 : BitVec 16) (Rd : BitVec 5) :
    extractLsb' 31 1 (sf ++ opc ++ 37#6 ++ hw ++ imm16 ++ Rd) = sf := by bv_field
example (sf : BitVec 1) (opc : BitVec 2) (hw : BitVec 2) (imm16 : BitVec 16) (Rd : BitVec 5) :
    extractLsb' 21 2 (sf ++ opc ++ 37#6 ++ hw ++ imm16 ++ Rd) = hw := by bv_field
