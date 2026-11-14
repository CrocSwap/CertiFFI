import TranslateValue.SymMain
import TranslateValue.ByteNat

/-! ArmCert value layer: a static WIDTH analysis of an SSA table. Each id gets
(bits, lowz): value < 2^bits and 2^lowz ∣ value. Inputs' widths are a premise (e.g. bytes: bits 8). It drives
the byte-assembly cases of the normalizer: disjoint orr = add, non-overflowing lsl, and masks. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateValue
open ArmCertValue

def immBits (c : BitVec 64) : Nat := Nat.log2 c.toNat + 1

/-- `some k` if c = 2^k − 1. -/
def maskBits (c : BitVec 64) : Option Nat :=
  if c.toNat + 1 = 2 ^ Nat.log2 (c.toNat + 1) then some (Nat.log2 (c.toNat + 1)) else none

def widthArg (W : List (Nat × Nat)) : Arg → Nat × Nat
  | .id a => W.getD a (64, 0)
  | .imm c => (immBits c, 0)

def widthDef (W : List (Nat × Nat)) (d : Def) : Nat × Nat :=
  let w := widthArg W
  match d.op with
  | .and => match d.args with
    | [x, .imm m] => match maskBits m with | some k => (min (w x).1 k, 0) | none => ((w x).1, 0)
    | [x, y] => (min (w x).1 (w y).1, 0)
    | _ => (64, 0)
  | .lsl k => match d.args with
    | [x] => if (w x).1 + k ≤ 64 then ((w x).1 + k, (w x).2 + k) else (64, 0)
    | _ => (64, 0)
  | .lsr k => match d.args with | [x] => ((w x).1 - k, 0) | _ => (64, 0)
  | .orr => match d.args with | [a, b] => (max (w a).1 (w b).1, 0) | _ => (64, 0)
  | .byteAt _ => match d.args with | [_] => (8, 0) | _ => (64, 0)
  | .carry3 => match d.args with | [_, _, _] => (1, 0) | _ => (64, 0)
  | .ovf3 => match d.args with | [_, _, _] => (1, 0) | _ => (64, 0)
  | .eqz => match d.args with | [_] => (1, 0) | _ => (64, 0)
  | .msb => match d.args with | [_] => (1, 0) | _ => (64, 0)
  | .cond _ => match d.args with | [_, _, _, _] => (1, 0) | _ => (64, 0)
  | _ => (64, 0)

def widthTable (iw : List (Nat × Nat)) (defs : List Def) : List (Nat × Nat) :=
  defs.foldl (fun W d => W ++ [widthDef W d]) iw

/-- What a width pair asserts about a value. -/
def WidthOK (v : BitVec 64) (w : Nat × Nat) : Prop := v.toNat < 2 ^ w.1 ∧ 2 ^ w.2 ∣ v.toNat

theorem widthOK_64 (v : BitVec 64) : WidthOK v (64, 0) := ⟨v.isLt, by simp⟩

theorem immBits_ok (c : BitVec 64) : WidthOK c (immBits c, 0) :=
  ⟨Nat.lt_log2_self, by simp⟩

theorem maskBits_spec {c : BitVec 64} {k : Nat} (h : maskBits c = some k) : c.toNat = 2 ^ k - 1 := by
  unfold maskBits at h
  by_cases he : c.toNat + 1 = 2 ^ Nat.log2 (c.toNat + 1)
  · rw [if_pos he] at h; cases h; omega
  · rw [if_neg he] at h; cases h

theorem or_disjoint (a b k : Nat) (ha : a < 2 ^ k) (hb : 2 ^ k ∣ b) : a ||| b = a + b := by
  obtain ⟨c, rfl⟩ := hb
  rw [Nat.or_comm, show 2 ^ k * c = c <<< k by rw [Nat.shiftLeft_eq, Nat.mul_comm],
    ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.add_comm]

/-- Per-def width soundness, from the args' widths. -/
theorem widthDef_sound (W : List (Nat × Nat)) (d : Def) (vals : List (BitVec 64))
    (hA : ∀ x ∈ d.args, WidthOK (Arg.eval vals x) (widthArg W x)) :
    WidthOK (d.op.eval (d.args.map (Arg.eval vals))) (widthDef W d) := by
  obtain ⟨op, args⟩ := d
  have b2 : ∀ (b : Bool), WidthOK (b01 b) (1, 0) := fun b => ⟨Nat.lt_of_le_of_lt (b01_le b) (by decide), by simp⟩
  cases op <;> simp only [widthDef] <;> (try exact widthOK_64 _)
  case and =>
    split
    · next x m =>
      have hx := (hA x (by simp)).1
      have e : Op.eval .and [Arg.eval vals x, Arg.eval vals (.imm m)] = Arg.eval vals x &&& m := rfl
      simp only [List.map]; rw [e]
      split
      · next k hk =>
        refine ⟨?_, by simp⟩
        rw [BitVec.toNat_and, maskBits_spec hk, Nat.and_two_pow_sub_one_eq_mod]
        have := Nat.mod_lt (Arg.eval vals x).toNat (Nat.two_pow_pos k)
        rcases Nat.le_total (widthArg W x).1 k with h | h
        · rw [Nat.min_eq_left h]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx
        · rw [Nat.min_eq_right h]; exact this
      · exact ⟨by rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_left hx, by simp⟩
    · next x y _ =>
      have hx := (hA x (by simp)).1; have hy := (hA y (by simp)).1
      have e : Op.eval .and [Arg.eval vals x, Arg.eval vals y] = Arg.eval vals x &&& Arg.eval vals y := rfl
      simp only [List.map]; rw [e]
      refine ⟨?_, by simp⟩
      rw [BitVec.toNat_and]
      rcases Nat.le_total (widthArg W x).1 (widthArg W y).1 with h | h
      · rw [Nat.min_eq_left h]; exact Nat.lt_of_le_of_lt Nat.and_le_left hx
      · rw [Nat.min_eq_right h]; exact Nat.lt_of_le_of_lt Nat.and_le_right hy
    · exact widthOK_64 _
  case lsl k =>
    split
    · next x =>
      have hx := hA x (by simp)
      have e : Op.eval (.lsl k) [Arg.eval vals x] = Arg.eval vals x <<< k := rfl
      simp only [List.map]; rw [e]
      split
      · next hk =>
        have lt : (Arg.eval vals x).toNat * 2 ^ k < 2 ^ 64 := by
          calc (Arg.eval vals x).toNat * 2 ^ k < 2 ^ (widthArg W x).1 * 2 ^ k :=
                Nat.mul_lt_mul_of_pos_right hx.1 (Nat.two_pow_pos k)
            _ = 2 ^ ((widthArg W x).1 + k) := (Nat.pow_add _ _ _).symm
            _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
        unfold WidthOK
        rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt lt]
        refine ⟨?_, ?_⟩
        · rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hx.1 (Nat.two_pow_pos k)
        · rw [Nat.pow_add]; exact Nat.mul_dvd_mul hx.2 (Nat.dvd_refl _)
      · exact widthOK_64 _
    · exact widthOK_64 _
  case lsr k =>
    split
    · next x =>
      have hx := hA x (by simp)
      have e : Op.eval (.lsr k) [Arg.eval vals x] = Arg.eval vals x >>> k := rfl
      simp only [List.map]; rw [e]
      refine ⟨?_, by simp⟩
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
      calc (Arg.eval vals x).toNat < 2 ^ (widthArg W x).1 := hx.1
        _ ≤ 2 ^ ((widthArg W x).1 - k + k) := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 ^ ((widthArg W x).1 - k) * 2 ^ k := Nat.pow_add _ _ _
    · exact widthOK_64 _
  case orr =>
    split
    · next a b =>
      have ha := (hA a (by simp)).1; have hb := (hA b (by simp)).1
      have e : Op.eval .orr [Arg.eval vals a, Arg.eval vals b] = Arg.eval vals a ||| Arg.eval vals b := rfl
      simp only [List.map]; rw [e]
      refine ⟨?_, by simp⟩
      rw [BitVec.toNat_or]
      apply Nat.or_lt_two_pow
      · exact Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
      · exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
    · exact widthOK_64 _
  case byteAt k =>
    split
    · next a =>
      simp only [List.map]
      exact ⟨by rw [byteAt_nat]; exact byteN_lt _ _, by simp⟩
    · exact widthOK_64 _
  case carry3 => split <;> first | exact b2 _ | exact widthOK_64 _
  case ovf3 => split <;> first | exact b2 _ | exact widthOK_64 _
  case eqz => split <;> first | exact b2 _ | exact widthOK_64 _
  case msb => split <;> first | exact b2 _ | exact widthOK_64 _
  case cond => split <;> first | exact b2 _ | exact widthOK_64 _

/-- Width soundness on the actual table, from input widths. -/
theorem width_sound (inputs : List (BitVec 64)) (defs : List Def) (iw : List (Nat × Nat))
    (hlen : iw.length = inputs.length) (hin : ∀ i, i < inputs.length → WidthOK (inputs.getD i 0) (iw.getD i (64, 0)))
    (wf : WF inputs.length defs = true) :
    ∀ t, t < inputs.length + defs.length →
      WidthOK ((evalDefs inputs defs).getD t 0) ((widthTable iw defs).getD t (64, 0)) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
  intro ht
  by_cases hn : t < inputs.length
  · have hw : (widthTable iw defs).getD t (64, 0) = iw.getD t (64, 0) := by
      unfold widthTable; exact foldlApp_prefix _ _ _ _ _ (by omega)
    have hv : (evalDefs inputs defs).getD t 0 = inputs.getD t 0 := by
      unfold evalDefs extend; exact foldlApp_prefix _ _ _ _ _ hn
    rw [hw, hv]; exact hin t hn
  · obtain ⟨k, rfl⟩ : ∃ k, t = inputs.length + k := ⟨t - inputs.length, by omega⟩
    have hk : k < defs.length := by omega
    obtain ⟨d, hd⟩ : ∃ d, defs[k]? = some d := ⟨defs[k], List.getElem?_eq_getElem hk⟩
    have args : ∀ x ∈ d.args, ∀ a, x = .id a → a < inputs.length + k := by
      have := List.all_eq_true.1 wf k (List.mem_range.2 hk)
      simp only [hd] at this
      intro x m a hx
      have := List.all_eq_true.1 this x m
      subst hx; simpa using this
    let F := fun (W : List (Nat × Nat)) (d : Def) => widthDef W d
    let pW := (defs.take k).foldl (fun acc d => acc ++ [F acc d]) iw
    have hw : (widthTable iw defs).getD (inputs.length + k) (64, 0) = widthDef pW d := by
      have := foldlApp_entry F iw defs k (64, 0) d hd
      rw [hlen] at this; exact this
    rw [hw, vals_entry inputs defs wf k d hd]
    apply widthDef_sound
    intro x m
    cases x with
    | id a =>
      have ha := args _ m a rfl
      have pre : pW.getD a (64, 0) = (widthTable iw defs).getD a (64, 0) :=
        foldlApp_take F iw defs k a (64, 0) (by omega) (by rw [hlen]; exact ha)
      simp only [widthArg, Arg.eval]
      rw [pre]; exact ih a ha (by omega)
    | imm c => exact immBits_ok c

#print axioms width_sound

#print axioms or_disjoint
#print axioms widthDef_sound
end TranslateValue
