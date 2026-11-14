import ArmCertWalk.Profile

set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCertWalk

theorem bv2_match_eq {α : Type} (selector : BitVec 2) (zero one two other : α) :
    (match selector with
      | 0b00 => zero
      | 0b01 => one
      | 0b10 => two
      | _ => other) =
    (if selector = 0#2 then zero else if selector = 1#2 then one
      else if selector = 2#2 then two else other) := by
  have possibilities : selector = 0#2 ∨ selector = 1#2 ∨
      selector = 2#2 ∨ selector = 3#2 := by
    have bound := selector.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    omega
  rcases possibilities with rfl | rfl | rfl | rfl <;> simp

#print axioms bv2_match_eq
end ArmCertWalk
