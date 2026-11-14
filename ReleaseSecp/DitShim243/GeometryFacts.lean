import DitShim243.CallerOffset
open Sail
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace DitShim243.Geometry

theorem pc_aligned (start j : Nat) (aligned : start % 4 = 0) :
    (shimPC start j).toNat % 4 = 0 := by
  simp only [shimPC,BitVec.toNat_ofNat]
  omega

theorem whole_aligned (start body L : Nat) (base callerLR : BitVec 64)
    (startAligned : start % 4 = 0) (bodyAligned : body % 4 = 0)
    (j : Nat) (bound : j < L + 12) :
    (wholeOffset start body L base callerLR j).toNat % 4 = 0 := by
  rw [wholeOffset,if_neg (show j ≠ L + 12 by omega)]
  unfold runOffset
  split
  · exact pc_aligned start j startAligned
  · split
    · simp only [BitVec.toNat_ofNat]; omega
    · exact pc_aligned start _ startAligned

theorem whole_body (start body L : Nat) (base callerLR : BitVec 64)
    (k : Nat) (bound : k ≤ L) :
    wholeOffset start body L base callerLR (7 + k) = BitVec.ofNat 64 (body + 4 * k) := by
  rw [wholeOffset,if_neg (show 7 + k ≠ L + 12 by omega)]
  simp only [runOffset,if_neg (show ¬ 7 + k < 7 by omega),if_pos (show 7 + k < L + 8 by omega),
    show 7 + k - 7 = k by omega]

#print axioms whole_aligned
#print axioms whole_body
end DitShim243.Geometry
