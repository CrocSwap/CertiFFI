import ArmCertValue.ExprStep

open HeapV2StepCerts.RegBind (Reg St regVal)
open ArmCertValue
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

namespace TranslateSpan.ExprOfVHold

theorem reg_output (source fin : St) (destination : Reg) (update : VUpd) (term : Expr.Term)
    (value : update.eval source = Expr.eval (srcVal source) term)
    (holds : VHolds [(destination, some update)] none source fin) :
    Expr.OutputHolds [(.reg destination, term)] source fin := by
  constructor
  · intro location expression member
    simp only [List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj member
    have result := holds.1 destination
    have assigned : regVal fin destination = update.eval source := by
      simpa only [List.find?, decide_true, Option.map_some] using result
    exact assigned.trans value
  · intro location absent
    cases location with
    | flag index => exact holds.2 index
    | reg other =>
      have different : destination ≠ other := by
        intro equal
        subst other
        exact absent term (by simp)
      have result := holds.1 other
      simpa [List.find?, different, Expr.locationValue] using result

theorem reg_flags_output (source fin : St) (destination : Reg)
    (update n z c v : VUpd) (term fn fz fc fv : Expr.Term)
    (value : update.eval source = Expr.eval (srcVal source) term)
    (negative : n.eval source = Expr.eval (srcVal source) fn)
    (zero : z.eval source = Expr.eval (srcVal source) fz)
    (carry : c.eval source = Expr.eval (srcVal source) fc)
    (overflow : v.eval source = Expr.eval (srcVal source) fv)
    (holds : VHolds [(destination, some update)] (some (n,z,c,v)) source fin) :
    Expr.OutputHolds [(.reg destination,term),(.flag 0,fn),(.flag 1,fz),
      (.flag 2,fc),(.flag 3,fv)] source fin := by
  have assigned : regVal fin destination = Expr.eval (srcVal source) term := by
    have result := holds.1 destination
    have written : regVal fin destination = update.eval source := by
      simpa only [List.find?, decide_true, Option.map_some] using result
    exact written.trans value
  constructor
  · intro location expression member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with member | member | member | member | member
    all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj member
    · exact assigned
    · exact holds.2.1.trans negative
    · exact holds.2.2.1.trans zero
    · exact holds.2.2.2.1.trans carry
    · exact holds.2.2.2.2.trans overflow
  · intro location absent
    cases location with
    | reg other =>
      have different : destination ≠ other := by
        intro equal
        subst other
        exact absent term (by simp)
      have result := holds.1 other
      simpa [List.find?, different, Expr.locationValue] using result
    | flag index =>
      match index with
      | 0 => exact False.elim (absent fn (by simp))
      | 1 => exact False.elim (absent fz (by simp))
      | 2 => exact False.elim (absent fc (by simp))
      | 3 => exact False.elim (absent fv (by simp))

#print axioms reg_output
#print axioms reg_flags_output

end TranslateSpan.ExprOfVHold
