import TranslateSpan.DefaultScalarTrace
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace DitShim243.Geometry

/-- Relative shim PCs, with the load offset supplied by the ELF binding. -/
def shimPC (start j : Nat) : BitVec 64 := BitVec.ofNat 64 (start + 4 * j)

theorem shimPC_succ (start j : Nat) : shimPC start (j + 1) = shimPC start j + 4#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [shimPC, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Interleave the seven prefix instructions, the raw body (including RET),
then the four epilogue instructions. L counts the body instructions before RET. -/
def runOffset (start body L j : Nat) : BitVec 64 :=
  if j < 7 then shimPC start j
  else if j < L + 8 then BitVec.ofNat 64 (body + 4 * (j - 7))
  else shimPC start (j - (L + 1))

theorem prefix_pc (start body L j : Nat) (bound : j ≤ 6) :
    runOffset start body L j = shimPC start j := by
  simp only [runOffset, if_pos (show j < 7 by omega)]

theorem epilogue (start body L j : Nat) (lower : L + 8 ≤ j) :
    runOffset start body L j = shimPC start (j - (L + 1)) := by
  simp only [runOffset, if_neg (show ¬ j < 7 by omega), if_neg (show ¬ j < L + 8 by omega)]

theorem continuation (start body L : Nat) :
    runOffset start body L (L + 8) = runOffset start body L 6 + 4#64 := by
  rw [epilogue start body L _ (Nat.le_refl _), prefix_pc start body L 6 (by omega),
    show L + 8 - (L + 1) = 7 by omega]
  exact shimPC_succ start 6

/-- The signed BL immediate in the exact Add shim is relative to the BL PC. -/
theorem add_bl : (8116#64) + sign_extend ((67108257#26) ++ 0#2) 64 = 5688#64 := by decide

theorem add_entry : runOffset 8092 5688 23 0 = 8092#64 := by decide
theorem add_body : runOffset 8092 5688 23 7 = 5688#64 := by decide
theorem add_ret : runOffset 8092 5688 23 30 = 5780#64 := by decide
theorem add_continuation : runOffset 8092 5688 23 31 = 8120#64 := by decide
theorem add_restore : runOffset 8092 5688 23 33 = 8128#64 := by decide
theorem add_caller_ret : runOffset 8092 5688 23 34 = 8132#64 := by decide

#print axioms shimPC_succ
#print axioms continuation
#print axioms add_bl
end DitShim243.Geometry
