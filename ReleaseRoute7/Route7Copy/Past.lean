-- Route 7 unit 3: counting the memory steps of the copy schedule (MTE tag-status budget).
import Route7Copy.Context
set_option autoImplicit false
namespace Route7Copy

theorem memStep_body (n i j : Nat) (hi : i < n) (hj : j < 6) :
    memStep n (2 + 6 * i + j) = decide (j < 2) := by
  unfold memStep
  have h1 : (2 + 6 * i + j - 2) % 6 = j := by omega
  have h2 : (2 + 6 * i + j - 2) / 6 = i := by omega
  rw [h1, h2]
  by_cases h : j < 2
  · simp [h, hi]; omega
  · simp [h]

theorem memStep_pre (n k : Nat) (hk : k < 2) : memStep n k = false := by
  unfold memStep; simp; omega

theorem memPast_step (n i j : Nat) (hi : i < n) (hj : j < 6) :
    memPast n (2 + 6 * i + j + 1) = memPast n (2 + 6 * i + j) + (if j < 2 then 1 else 0) := by
  rw [memPast_succ, memStep_body n i j hi hj]
  by_cases h : j < 2 <;> simp [h]

theorem memPast_two (n : Nat) : memPast n 2 = 0 := by
  show memPast n 1 + _ = 0
  rw [memStep_pre n 1 (by omega)]
  show memPast n 0 + _ + _ = 0
  rw [memStep_pre n 0 (by omega)]; rfl

/-- At the start of body iteration i the loads and stores of iterations < i have drawn 2i statuses. -/
theorem memPast_body (n i : Nat) (hi : i ≤ n) : memPast n (2 + 6 * i) = 2 * i := by
  induction i with
  | zero => simpa using memPast_two n
  | succ i ih =>
    have lt : i < n := by omega
    have e0 := memPast_step n i 0 lt (by omega)
    have e1 := memPast_step n i 1 lt (by omega)
    have e2 := memPast_step n i 2 lt (by omega)
    have e3 := memPast_step n i 3 lt (by omega)
    have e4 := memPast_step n i 4 lt (by omega)
    have e5 := memPast_step n i 5 lt (by omega)
    simp only [Nat.add_zero, show (0 : Nat) < 2 from by omega, show (1 : Nat) < 2 from by omega,
      show ¬ (2 : Nat) < 2 from by omega, show ¬ (3 : Nat) < 2 from by omega, show ¬ (4 : Nat) < 2 from by omega,
      show ¬ (5 : Nat) < 2 from by omega, ite_true, ite_false] at e0 e1 e2 e3 e4 e5
    have a : 2 + 6 * (i + 1) = 2 + 6 * i + 5 + 1 := by omega
    have b1 : 2 + 6 * i + 0 + 1 = 2 + 6 * i + 1 := by omega
    rw [a, e5]
    rw [show 2 + 6 * i + 5 = 2 + 6 * i + 4 + 1 by omega, e4, show 2 + 6 * i + 4 = 2 + 6 * i + 3 + 1 by omega, e3,
      show 2 + 6 * i + 3 = 2 + 6 * i + 2 + 1 by omega, e2, show 2 + 6 * i + 2 = 2 + 6 * i + 1 + 1 by omega, e1, e0,
      ih (by omega)]
    omega

end Route7Copy
#print axioms Route7Copy.memPast_body
