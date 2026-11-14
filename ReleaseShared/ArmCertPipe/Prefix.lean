-- d199 pipeline: the program-generic chain `extra` = the value layer's Agrees at the k-step plan prefix.
-- AgreesAt k x: the actual state x agrees with the symbolic state after compiling plan.take k, on the table extended
-- by the prefix's definitions. It generalises heap-v2's RegBind (registers hold their table values, pointer and loaded
-- index registers included) and DataPresent (tracked region bytes mapped and present with their table values).
-- Preservation is certiffi's step_agrees on the step's VHolds + MemVHolds (agreesAt_succ), so no program proves it by hand.
import ArmCertValue.Run
import ArmCertValue.StepAgrees
set_option autoImplicit false
namespace ArmCertPipe
open ArmCertValue
open HeapV2StepCerts.RegBind (St)

theorem compileRun_append (regions : List Region) :
    ∀ (l1 l2 : List StepV) (σ : Sym) (n : Nat),
      compileRun regions σ n (l1 ++ l2) = (compileRun regions σ n l1).bind fun p =>
        (compileRun regions p.2 (n + p.1.length) l2).map fun q => (p.1 ++ q.1, q.2) := by
  intro l1
  induction l1 with
  | nil => intro l2 σ n; simp [compileRun]
  | cons st rest ih =>
    intro l2 σ n
    simp only [List.cons_append, compileRun]
    cases h : compile σ n regions st with
    | none => rfl
    | some p =>
      obtain ⟨ds, σ1⟩ := p
      simp only [ih]
      cases h2 : compileRun regions σ1 (n + ds.length) rest with
      | none => rfl
      | some q =>
        obtain ⟨ds', σf⟩ := q
        simp only [Option.bind_some, Option.map_some, List.length_append, Nat.add_assoc, List.append_assoc]
        cases compileRun regions σf (n + (ds.length + ds'.length)) l2 <;> rfl

/-- Agrees at the k-step prefix (the chain extra). -/
def AgreesAt (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (σ0 : Sym)
    (inputs : List (BitVec 64)) (plan : List StepV) (k : Nat) (x : St) : Prop :=
  ∃ ds σ, compileRun regions σ0 inputs.length (plan.take k) = some (ds, σ) ∧
    Agrees mapping pinv (extend inputs ds) σ x ∧ σ.Bounded (extend inputs ds).length

/-- At k = 0: the entry agreement. -/
theorem agreesAt_zero {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {x : St}
    (hA : Agrees mapping pinv inputs σ0 x) (hB : σ0.Bounded inputs.length) :
    AgreesAt mapping pinv regions σ0 inputs plan 0 x :=
  ⟨[], σ0, by simp [compileRun], by simpa [extend] using hA, by simpa [extend] using hB⟩

/-- **The chain extra is preserved** by any step satisfying its plan entry's VHolds and MemVHolds, as long as the whole
    plan compiles (P1's compiles_D). -/
theorem agreesAt_succ {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {k : Nat} {x y : St}
    (hcoh : RegionCoherent mapping pinv) (hk : k < plan.length)
    (hall : (compileRun regions σ0 inputs.length plan).isSome = true)
    (h : AgreesAt mapping pinv regions σ0 inputs plan k x)
    (hv : VHolds plan[k].us plan[k].fl x y) (hm : MemVHolds mapping pinv regions plan[k].mem x y) :
    AgreesAt mapping pinv regions σ0 inputs plan (k + 1) y := by
  obtain ⟨ds, σ, hc, hA, hB⟩ := h
  have split : plan = plan.take k ++ (plan[k] :: plan.drop (k + 1)) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  -- the k-th step compiles (from the whole plan compiling)
  have hstep : ∃ ds' σ', compile σ (inputs.length + ds.length) regions plan[k] = some (ds', σ') := by
    rw [split, compileRun_append, hc] at hall
    simp only [Option.bind_some, Option.isSome_map, compileRun] at hall
    cases h1 : compile σ (inputs.length + ds.length) regions plan[k] with
    | none => rw [h1] at hall; simp at hall
    | some p => exact ⟨p.1, p.2, rfl⟩
  obtain ⟨ds', σ', h1⟩ := hstep
  have hlen : (extend inputs ds).length = inputs.length + ds.length := extend_length inputs ds
  have hc' : compile σ (extend inputs ds).length regions plan[k] = some (ds', σ') := by rw [hlen]; exact h1
  obtain ⟨hA', hB'⟩ := step_agrees hcoh hA hB hv hm hc'
  refine ⟨ds ++ ds', σ', ?_, by rw [extend_append]; exact hA', by rw [extend_append]; exact hB'⟩
  rw [List.take_succ_eq_append_getElem hk, compileRun_append, hc]
  simp [compileRun, h1]

/-- `extend` only appends. -/
theorem extend_prefix (vals : List (BitVec 64)) : ∀ ds : List Def, ∃ t, extend vals ds = vals ++ t := by
  intro ds
  induction ds generalizing vals with
  | nil => exact ⟨[], by simp [extend]⟩
  | cons d rest ih =>
    obtain ⟨t, ht⟩ := ih (vals ++ [d.eval vals])
    exact ⟨[d.eval vals] ++ t, by simp only [extend, List.foldl_cons] at ht ⊢; rw [ht, List.append_assoc]⟩

/-- An input entry of the table. -/
theorem getD_extend_input (vals : List (BitVec 64)) (ds : List Def) {i : Nat} (h : i < vals.length) :
    (extend vals ds).getD i 0 = vals.getD i 0 := by
  obtain ⟨t, ht⟩ := extend_prefix vals ds
  rw [ht, List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

/-- A definition's entry of the table: its definition evaluated on the whole table (arguments below it). -/
theorem getD_extend_def (vals : List (BitVec 64)) (ds : List Def) {j : Nat} (hj : j < ds.length)
    (hb : ds[j].Below (vals.length + j)) :
    (extend vals ds).getD (vals.length + j) 0 = ds[j].eval (extend vals ds) := by
  have split : ds = ds.take j ++ (ds[j] :: ds.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hP : (extend vals (ds.take j)).length = vals.length + j := by
    rw [extend_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  obtain ⟨t, ht⟩ := extend_prefix (extend vals (ds.take j) ++ [ds[j].eval (extend vals (ds.take j))]) (ds.drop (j + 1))
  have full : extend vals ds = extend vals (ds.take j) ++ ([ds[j].eval (extend vals (ds.take j))] ++ t) := by
    conv => lhs; rw [split]
    rw [extend_append]
    simp only [extend, List.foldl_cons] at ht ⊢
    rw [ht, List.append_assoc]
  rw [full, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  rw [hP, Nat.sub_self]
  simp only [List.singleton_append, List.getElem?_cons_zero, Option.getD_some]
  rw [Def.eval_append _ _ _ (by rw [hP]; exact hb)]

/-- A register tracked at step k holds its entry of the WHOLE plan's table (the prefix table is a prefix of it). -/
theorem regVal_of_agreesAt {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {k : Nat} {x : St} {D : List Def} {σf : Sym}
    (h : AgreesAt mapping pinv regions σ0 inputs plan k x)
    (hall : compileRun regions σ0 inputs.length plan = some (D, σf))
    {r : HeapV2StepCerts.RegBind.Reg} {i : Nat}
    (hr : (compileRun regions σ0 inputs.length (plan.take k)).map (fun p => p.2.regs r) = some (some i)) :
    HeapV2StepCerts.RegBind.regVal x r = (extend inputs D).getD i 0 := by
  obtain ⟨ds, σ, hc, hA, hB⟩ := h
  rw [hc] at hr
  simp only [Option.map_some, Option.some.injEq] at hr
  have hv := hA.1 r i hr
  have hlt := hB.1 r i hr
  -- D = ds ++ rest
  have split := compileRun_append regions (plan.take k) (plan.drop k) σ0 inputs.length
  rw [List.take_append_drop, hall, hc] at split
  simp only [Option.bind_some] at split
  cases hrest : compileRun regions σ (inputs.length + ds.length) (plan.drop k) with
  | none => rw [hrest] at split; simp at split
  | some q =>
    rw [hrest] at split
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at split
    rw [hv, split.1, extend_append, getD_extend_input _ _ hlt]

#print axioms getD_extend_input
#print axioms getD_extend_def
#print axioms regVal_of_agreesAt
#print axioms compileRun_append
#print axioms agreesAt_zero
#print axioms agreesAt_succ
end ArmCertPipe
