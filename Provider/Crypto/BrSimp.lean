import Pilot.EvalProfile
/-! Small closed-case simp lemmas for the flat branch natives (armcert-crypto). -/
namespace Crypto.BrSimp

theorem ite21_beq0 (c : Prop) [Decidable c] : ((if c then (2#2 : BitVec 2) else 1#2) == 0#2) = false := by
  split <;> decide
theorem ite21_eq0 (c : Prop) [Decidable c] : ((if c then (2#2 : BitVec 2) else 1#2) = 0#2) = False := by
  split <;> simp

theorem bit_low (a : BitVec 64) (h : a.toNat < 2 ^ 55) (i : Nat) (hi : 55 ≤ i) : a.getLsbD i = false := by
  simp only [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hi))

theorem obl1 (c : Bool) : (BitVec.ofBoolListBE (List.map (fun x : BitVec 1 => x[0]) [BitVec.ofBool c]))[0] = c := by
  cases c <;> decide

/-- The native's "bit 55 of the branch target" test is false for a target below 2^55. -/
theorem b55_false (x : BitVec 64) (h : x.toNat < 2 ^ 55) :
    (Sail.BitVec.join1 [Sail.BitVec.access (Sail.BitVec.extractLsb x 63 0) 55] = 1#1) = False := by
  have hb := bit_low x h 55 (by decide)
  apply propext; constructor
  · intro hc
    have := congrArg (fun v => v.getLsbD 0) hc
    simp [Sail.BitVec.join1, Sail.BitVec.access, Sail.BitVec.extractLsb, getElem!_def] at this
    rw [obl1] at this
    have e2 : (BitVec.extractLsb 63 0 x)[55]! = x[55] := by
      simp [getElem!_def]
    rw [e2] at this
    simp_all
  · intro hf; exact hf.elim

/-- The flat natives index FeatureImpl through GetElem?.toGetElem (instGetElem?OfGetElemOfDecidable ..);
    normalize to the plain Vector instance. -/
theorem gi259 (v : Vector Bool 259) (k : Nat) (h : k < 259) :
    @getElem (Vector Bool 259) Nat Bool (fun _ i => i < 259)
      (@GetElem?.toGetElem (Vector Bool 259) Nat Bool (fun _ i => i < 259)
        (@instGetElem?OfGetElemOfDecidable (Vector Bool 259) Nat Bool (fun _ i => i < 259)
          (@Vector.instGetElemNatLt Bool 259) (fun _ i => i.decLt 259))) v k h = v[k] := rfl

theorem tt_ff (b : Bool) (p : Prop) : (b = true ∧ b = false ∧ p) = False := by
  cases b <;> simp
theorem tt_ff2 (b : Bool) : (b = true ∧ b = false) = False := by
  cases b <;> simp

/-- Dependent implications on a known-true / known-false premise (simp cannot rewrite the domain of a
    dependent pi). -/
theorem fa_true {p : Prop} (hp : p) {q : p → Prop} : (∀ x : p, q x) = q hp :=
  propext ⟨fun f => f hp, fun hq _ => hq⟩
theorem fa_false {p : Prop} (hn : ¬ p) {q : p → Prop} : (∀ x : p, q x) = True :=
  propext ⟨fun _ => trivial, fun _ x => (hn x).elim⟩

/-- Lift a common `ok` constructor out of conditionals. -/
theorem ok_ite {ε σ α : Type} (c : Prop) [Decidable c] (a : α) (x y : σ) :
    (if c then (EStateM.Result.ok a x : EStateM.Result ε σ α) else EStateM.Result.ok a y) =
      EStateM.Result.ok a (if c then x else y) := by
  split <;> rfl
theorem ok_dite {ε σ α : Type} (c : Prop) [Decidable c] (a : α) (x : c → σ) (y : ¬c → σ) :
    (if h : c then (EStateM.Result.ok a (x h) : EStateM.Result ε σ α) else EStateM.Result.ok a (y h)) =
      EStateM.Result.ok a (if h : c then x h else y h) := by
  split <;> rfl
theorem ok_exists {ε σ α : Type} (a : α) (x : σ) (P : σ → Prop) :
    (∃ t, (EStateM.Result.ok a x : EStateM.Result ε σ α) = EStateM.Result.ok a t ∧ P t) = P x := by
  apply propext; constructor
  · rintro ⟨t, h, hp⟩; cases h; exact hp
  · intro hp; exact ⟨x, rfl, hp⟩

theorem idx_55_63 (c : Prop) [Decidable c] :
    (0 ≤ (if c then (55 : Int) else 63) ∧ (if c then (55 : Int) else 63) < 64) = True := by
  split <;> decide

theorem bitN_false (x : BitVec 64) (h : x.toNat < 2 ^ 55) (i : Nat) (hi : 55 ≤ i) (hi2 : i < 64) :
    (Sail.BitVec.join1 [Sail.BitVec.access (Sail.BitVec.extractLsb x 63 0) i] = 1#1) = False := by
  have hb := bit_low x h i hi
  apply propext; constructor
  · intro hc
    have := congrArg (fun v => v.getLsbD 0) hc
    simp [Sail.BitVec.join1, Sail.BitVec.access, Sail.BitVec.extractLsb, getElem!_def] at this
    rw [obl1] at this
    have e2 : (BitVec.extractLsb 63 0 x)[i]! = x[i]'(by omega) := by
      simp [getElem!_def, hi2]
    rw [e2] at this
    simp_all
  · intro hf; exact hf.elim

/-- The native AArch64 branch-target TBI computation is the identity on a target below 2^55,
    whichever top-bit index (55 or 63) the regime selects. -/
theorem tbi_low (T : BitVec 64) (hT : T.toNat < 2 ^ 55) (c : Bool) :
    (if Sail.BitVec.join1 [Sail.BitVec.access (Sail.BitVec.extractLsb T 63 0)
          (Sail.Int.toNatChecked (if c = true then 55 else 63))] = 1#1 then
        sign_extend (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb T 63 0)
          (Sail.Int.toNatChecked (if c = true then 55 else 63)) 0) 64
      else Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb T 63 0)
          (Sail.Int.toNatChecked (if c = true then 55 else 63)) 0) 64) = T := by
  cases c
  · show (if Sail.BitVec.join1 [Sail.BitVec.access (Sail.BitVec.extractLsb T 63 0) 63] = 1#1 then
        sign_extend (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb T 63 0) 63 0) 64
      else Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb T 63 0) 63 0) 64) = T
    have hn : ¬ (Sail.BitVec.join1 [Sail.BitVec.access (Sail.BitVec.extractLsb T 63 0) 63] = 1#1) := by
      rw [bitN_false T hT 63 (by decide) (by decide)]; exact id
    rw [if_neg hn]
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
    omega
  · show (if Sail.BitVec.join1 [Sail.BitVec.access (Sail.BitVec.extractLsb T 63 0) 55] = 1#1 then
        sign_extend (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb T 63 0) 55 0) 64
      else Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb T 63 0) 55 0) 64) = T
    have hn : ¬ (Sail.BitVec.join1 [Sail.BitVec.access (Sail.BitVec.extractLsb T 63 0) 55] = 1#1) := by
      rw [bitN_false T hT 55 (by decide) (by decide)]; exact id
    rw [if_neg hn]
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
    omega

theorem w_ok (sf : BitVec 1) :
    (Sail.Int.toNatChecked (if sf = 1#1 then 64 else 32) = 8 ∨ Sail.Int.toNatChecked (if sf = 1#1 then 64 else 32) = 16 ∨
      Sail.Int.toNatChecked (if sf = 1#1 then 64 else 32) = 32 ∨ Sail.Int.toNatChecked (if sf = 1#1 then 64 else 32) = 64) = True := by
  apply eq_true
  by_cases h : sf = 1#1 <;> simp [h, Sail.Int.toNatChecked]

end Crypto.BrSimp
