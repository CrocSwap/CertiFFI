import ArmCertWalk.Profile

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

theorem stage_join_nat (base va size : Nat) (bound : base < 2^56) (valid : size ≤ 56) :
    (base / 2^size % 2^(56-size)) * 2^size + va % 2^size =
      (base / 2^size * 2^size + va % 2^size) % 2^56 := by
  have positive : 0 < 2^size := Nat.pow_pos (by decide)
  have powers : 2^(56-size) * 2^size = 2^56 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have quotient : base / 2^size < 2^(56-size) := by
    apply (Nat.div_lt_iff_lt_mul positive).mpr
    rw [powers]
    exact bound
  have low : va % 2^size < 2^size := Nat.mod_lt _ positive
  have total : base / 2^size * 2^size + va % 2^size < 2^56 := by
    calc
      _ < base / 2^size * 2^size + 2^size := Nat.add_lt_add_left low _
      _ = (base / 2^size + 1) * 2^size := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 2^(56-size) * 2^size := Nat.mul_le_mul_right _ quotient
      _ = 2^56 := powers
  rw [Nat.mod_eq_of_lt quotient, Nat.mod_eq_of_lt total]

#print axioms stage_join_nat
end ArmCertWalk
