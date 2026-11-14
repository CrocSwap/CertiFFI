import ArmCertValue.Core

/-! Per-op Nat facts for ArmCertValue.Op.eval (the value layer's SSA ops over BitVec 64), stated as the
integer equations the normalizer uses, plus the prefix facts about the append-fold that builds tables. -/

set_option autoImplicit false
namespace TranslateValue
open ArmCertValue

def pow64 : Nat := 18446744073709551616

theorem pow64_eq : pow64 = 2 ^ 64 := by decide

theorem add_nat (a b : BitVec 64) : (a + b).toNat + pow64 * ((a.toNat + b.toNat) / pow64) = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, pow64_eq]; exact Nat.mod_add_div _ _

theorem sub_nat (a b : BitVec 64) :
    (a - b).toNat + b.toNat = a.toNat + pow64 * (if a.toNat < b.toNat then 1 else 0) := by
  rw [BitVec.toNat_sub, pow64_eq]
  have ha := a.isLt; have hb := b.isLt
  split <;> omega

theorem mul_nat (a b : BitVec 64) : (a * b).toNat + pow64 * ((a.toNat * b.toNat) / pow64) = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, pow64_eq]; exact Nat.mod_add_div _ _

theorem umulh_nat (a b : BitVec 64) : (Op.eval .umulh [a, b]).toNat = (a.toNat * b.toNat) / pow64 := by
  have e : Op.eval .umulh [a, b] = BitVec.ofNat 64 ((a.toNat * b.toNat) / 2 ^ 64) := rfl
  rw [e, BitVec.toNat_ofNat, pow64_eq]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  exact Nat.mul_lt_mul'' a.isLt b.isLt

theorem add3_nat (a b c : BitVec 64) :
    (a + b + c).toNat + pow64 * ((a.toNat + b.toNat + c.toNat) / pow64) = a.toNat + b.toNat + c.toNat := by
  have h : (a + b + c).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, Nat.mod_add_mod]
  rw [h, pow64_eq]; exact Nat.mod_add_div _ _

theorem carry3_nat (a b c : BitVec 64) (hc : c.toNat ≤ 1) :
    (Op.eval .carry3 [a, b, c]).toNat = (a.toNat + b.toNat + c.toNat) / pow64 := by
  have ha := a.isLt; have hb := b.isLt
  have e : Op.eval .carry3 [a, b, c] = b01 (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) := rfl
  rw [e, pow64_eq]
  unfold b01
  split <;> simp_all <;> omega

theorem not_nat (a : BitVec 64) : (~~~a).toNat + a.toNat = pow64 - 1 := by
  rw [BitVec.toNat_not, pow64_eq]; have := a.isLt; omega

theorem lsl_nat (a : BitVec 64) (k : Nat) :
    (a <<< k).toNat + pow64 * ((a.toNat * 2 ^ k) / pow64) = a.toNat * 2 ^ k := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, pow64_eq]; exact Nat.mod_add_div _ _

theorem const_nat (c : BitVec 64) (args : List (BitVec 64)) : (Op.eval (.const c) args).toNat = c.toNat := by
  cases args <;> rfl

theorem csel_nat (w a b : BitVec 64) (hw : w.toNat ≤ 1) :
    ((Op.eval .csel [w, a, b]).toNat : Int) = w.toNat * a.toNat + (1 - (w.toNat : Int)) * b.toNat := by
  have e : Op.eval .csel [w, a, b] = if w ≠ 0 then a else b := rfl
  rw [e]
  by_cases h : w = 0
  · subst h; simp
  · have : w.toNat = 1 := by
      have : w.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq (by simpa using h0))
      omega
    have h' : ¬ w = 0#64 := h
    simp [h', this]

/-- Values of the boolean-producing ops are 0 or 1. -/
theorem b01_le (b : Bool) : (b01 b).toNat ≤ 1 := by cases b <;> decide

/-! ### The append-fold -/

theorem foldlApp_length {α : Type} (f : List α → Def → α) (init : List α) (defs : List Def) :
    (defs.foldl (fun acc d => acc ++ [f acc d]) init).length = init.length + defs.length := by
  induction defs generalizing init with
  | nil => simp
  | cons d defs ih => simp only [List.foldl_cons]; rw [ih]; simp; omega

theorem foldlApp_prefix {α : Type} (f : List α → Def → α) (init : List α) (defs : List Def) (i : Nat) (d0 : α)
    (hi : i < init.length) :
    (defs.foldl (fun acc d => acc ++ [f acc d]) init).getD i d0 = init.getD i d0 := by
  induction defs generalizing init with
  | nil => rfl
  | cons d defs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- The entry at init.length + k is f applied to the k-step prefix table and defs[k]. -/
theorem foldlApp_entry {α : Type} (f : List α → Def → α) (init : List α) (defs : List Def) (k : Nat) (d0 : α)
    (d : Def) (hk : defs[k]? = some d) :
    (defs.foldl (fun acc d => acc ++ [f acc d]) init).getD (init.length + k) d0 =
      f ((defs.take k).foldl (fun acc d => acc ++ [f acc d]) init) d := by
  induction defs generalizing init k with
  | nil => simp at hk
  | cons e defs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp only [List.foldl_cons, List.take_zero, List.foldl_nil, Nat.add_zero]
      rw [foldlApp_prefix _ _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      simp only [List.foldl_cons, List.take_succ_cons, List.foldl_cons]
      have := ih (init ++ [f init e]) k hk
      simp only [List.length_append, List.length_singleton] at this
      rw [show init.length + (k + 1) = init.length + 1 + k by omega, this]

theorem sbc3_nat (a b c : BitVec 64) :
    (Op.eval .sbc3 [a, b, c]).toNat + pow64 * ((a.toNat + (pow64 - 1 - b.toNat) + c.toNat) / pow64) =
      a.toNat + (pow64 - 1 - b.toNat) + c.toNat := by
  have e : Op.eval .sbc3 [a, b, c] = a + ~~~b + c := rfl
  have hn : (~~~b).toNat = pow64 - 1 - b.toNat := by rw [BitVec.toNat_not, pow64_eq]
  have h : (a + ~~~b + c).toNat = (a.toNat + (~~~b).toNat + c.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, Nat.mod_add_mod]
  rw [e, h, hn, pow64_eq]; exact Nat.mod_add_div _ _

theorem sbc3C_nat (a b c : BitVec 64) (hc : c.toNat ≤ 1) :
    (Op.eval .sbc3C [a, b, c]).toNat = (a.toNat + (pow64 - 1 - b.toNat) + c.toNat) / pow64 := by
  have ha := a.isLt; have hb := b.isLt
  have e : Op.eval .sbc3C [a, b, c] = b01 (2 ^ 64 ≤ a.toNat + (~~~b).toNat + c.toNat) := rfl
  have hn : (~~~b).toNat = pow64 - 1 - b.toNat := by rw [BitVec.toNat_not, pow64_eq]
  rw [e, hn, pow64_eq]
  unfold b01
  split <;> simp_all <;> omega

theorem cselc_nat (cc : BitVec 4) (n z cf v a b : BitVec 64) :
    ((Op.eval (.cselc cc) [n, z, cf, v, a, b]).toNat : Int) =
      (if condHolds cc n z cf v then 1 else 0) * a.toNat + (1 - (if condHolds cc n z cf v then 1 else 0 : Int)) * b.toNat := by
  have e : Op.eval (.cselc cc) [n, z, cf, v, a, b] = if condHolds cc n z cf v then a else b := rfl
  rw [e]; split <;> simp

#print axioms carry3_nat
#print axioms csel_nat
#print axioms foldlApp_entry
end TranslateValue
