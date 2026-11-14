import Walk.S2MPAMMap
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2MPAMRange
def limit (r : BitVec 3) : Int := Sail.Int.shiftl (r.toNat : Int) 2 + 3
def virt (v : BitVec 16) (r : BitVec 3) : Int :=
  if limit r < v.toNat then fmod_int v.toNat (limit r + 1) else v.toNat

theorem limit_bounds (r : BitVec 3) : 3 ≤ limit r ∧ limit r ≤ 31 := by
  have hb := r.isLt
  simp only [limit, Sail.Int.shiftl, Sail.Nat.iterate]
  omega

theorem fmod_eq_emod (n m : Int) (hn : 0 ≤ n) (hm : 0 < m) :
    fmod_int n m = n % m := by
  simp [fmod_int, fdiv_int, Int.tdiv_eq_ediv_of_nonneg hn,
    show ¬ n < 0 from by omega, show ¬ m < 0 from by omega, Int.emod_def]

theorem bounded (v : BitVec 16) (r : BitVec 3) : 0 ≤ virt v r ∧ virt v r < 64 := by
  have hl := limit_bounds r
  have hv : (0 : Int) ≤ v.toNat := by omega
  unfold virt
  split
  · rw [fmod_eq_emod _ _ hv (by omega)]
    have hn := Int.emod_nonneg (v.toNat : Int) (b := limit r + 1) (by omega)
    have hm := Int.emod_lt_of_pos (v.toNat : Int) (b := limit r + 1) (by omega)
    omega
  · omega
#print axioms bounded

abbrev State := SequentialState Regs oracleChoiceSource
abbrev Result := EStateM.Result (Sail.Error exception) State (BitVec 16 × Bool)
def value : Result → BitVec 16 × Bool
  | .ok v _ => v
  | .error _ _ => (0#16, false)
def occ : Result → Std.ExtHashMap Nat Nat
  | .ok _ s => s.choiceOcc
  | .error _ s => s.choiceOcc
noncomputable def normal (v : BitVec 16) (s : State) : Result :=
  .ok (value (S2MPAMMap.native v s)) {s with choiceOcc := occ (S2MPAMMap.native v s)}

theorem pack_state (s : State) (p : Prop) {_ : Decidable p}
    (a b : Std.ExtHashMap Nat Nat) :
    (if p then {s with choiceOcc := a} else {s with choiceOcc := b}) =
      {s with choiceOcc := (if p then {s with choiceOcc := a} else {s with choiceOcc := b}).choiceOcc} := by
  split <;> rfl
theorem pack_state_dep (s : State) (p : Prop) {_ : Decidable p}
    (a : p → Std.ExtHashMap Nat Nat) (b : ¬p → Std.ExtHashMap Nat Nat) :
    (dite p (fun h => {s with choiceOcc := a h}) (fun h => {s with choiceOcc := b h})) =
      {s with choiceOcc := (dite p (fun h => {s with choiceOcc := a h})
        (fun h => {s with choiceOcc := b h})).choiceOcc} := by
  split <;> rfl

theorem packed (v : BitVec 16) (s : State) : S2MPAMMap.native v s = normal v s := by
  have hb := bounded v (Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 .MPAMIDR_EL1) 20 18)
  dsimp only [virt, limit] at hb
  delta normal S2MPAMMap.native value occ
  simp only [ite_eq_left hb, dite_eq_left hb]
  repeat (first | rfl | split)
  all_goals simp_all [value, occ, _get_MPAMIDR_EL1_Type_VPMR_MAX]
  all_goals first | rfl | exact pack_state s _ _ _ | exact pack_state_dep s _ _ _ | ((repeat' apply And.intro) <;> first | rfl | (split <;> rfl)) | (simp only [apply_ite]; simp)

theorem complete (v : BitVec 16) (s : State) : MAP_vPARTID v s = normal v s :=
  (S2MPAMMap.complete v s).trans (packed v s)
attribute [-step_summary] S2MPAMMap.complete
attribute [step_summary] complete
#print axioms complete
end S2MPAMRange
