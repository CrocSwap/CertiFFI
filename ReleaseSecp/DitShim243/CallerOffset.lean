import DitShim243.Geometry
open Sail
set_option autoImplicit false
namespace DitShim243.Geometry

/-- The final state returns to the caller's initial LR, outside the shim trace. -/
def wholeOffset (start body L : Nat) (base callerLR : BitVec 64) (j : Nat) : BitVec 64 :=
  if j = L + 12 then callerLR - base else runOffset start body L j

theorem whole_prefix (start body L j : Nat) (base callerLR : BitVec 64) (bound : j ≤ 6) :
    wholeOffset start body L base callerLR j = shimPC start j := by
  rw [wholeOffset, if_neg (show j ≠ L + 12 by omega)]
  exact prefix_pc start body L j bound

theorem whole_epilogue (start body L j : Nat) (base callerLR : BitVec 64)
    (lower : L + 8 ≤ j) (upper : j ≤ L + 11) :
    wholeOffset start body L base callerLR j = shimPC start (j - (L + 1)) := by
  rw [wholeOffset, if_neg (show j ≠ L + 12 by omega)]
  exact epilogue start body L j lower

theorem caller_target (start body L : Nat) (base callerLR : BitVec 64) :
    callerLR = base + wholeOffset start body L base callerLR (L + 12) := by
  simp only [wholeOffset, if_pos rfl]
  exact ((BitVec.add_comm base (callerLR - base)).trans (BitVec.sub_add_cancel callerLR base)).symm

#print axioms caller_target
end DitShim243.Geometry
