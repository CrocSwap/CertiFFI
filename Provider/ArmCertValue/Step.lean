-- ArmCert VALUE LAYER: one step. `compile` turns a plan step into SSA definitions and
-- the next symbolic state; `step_agrees` (proved once) says that the actual step's value facts
-- (VHolds / MemVHolds) carry `Agrees` across it. ArmCert-only.
import ArmCertValue.Core
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue
open HeapV2StepCerts.RegBind (Reg St regVal)

/-! ## Arguments -/

def nzcvId (q : Nat × Nat × Nat × Nat) : Fin 4 → Nat
  | 0 => q.1
  | 1 => q.2.1
  | 2 => q.2.2.1
  | 3 => q.2.2.2

def argOf (σ : Sym) : Src → Option Arg
  | .reg r => (σ.regs r).map Arg.id
  | .flag i => σ.nzcv.map fun q => Arg.id (nzcvId q i)
  | .lit c => some (.imm c)

def argsOf (σ : Sym) : List Src → Option (List Arg)
  | [] => some []
  | s :: t => match argOf σ s, argsOf σ t with
    | some a, some as => some (a :: as)
    | _, _ => none

def defOf (σ : Sym) (u : VUpd) : Option Def := (argsOf σ u.args).map fun as => ⟨u.op, as⟩

/-- An argument whose ids are below n. -/
def Arg.Below (n : Nat) : Arg → Prop
  | .id i => i < n
  | .imm _ => True

theorem flag_agrees {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {vals : List (BitVec 64)}
    {σ : Sym} {x : St} (hA : Agrees mapping pinv vals σ x) {q : Nat × Nat × Nat × Nat}
    (hq : σ.nzcv = some q) (i : Fin 4) : vals.getD (nzcvId q i) 0 = flagWord x i := by
  obtain ⟨a, b, c, d⟩ := q
  obtain ⟨h0, h1, h2, h3⟩ := hA.2.1 a b c d hq
  match i with
  | 0 => exact h0.symm
  | 1 => exact h1.symm
  | 2 => exact h2.symm
  | 3 => exact h3.symm

theorem argOf_sound {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {vals : List (BitVec 64)}
    {σ : Sym} {x : St} (hA : Agrees mapping pinv vals σ x) (hB : σ.Bounded vals.length) :
    ∀ (s : Src) (a : Arg), argOf σ s = some a → a.eval vals = srcVal x s ∧ a.Below vals.length := by
  intro s a h
  cases s with
  | reg r =>
    simp only [argOf, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    exact ⟨(hA.1 r i hi).symm, hB.1 r i hi⟩
  | flag f =>
    simp only [argOf, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    refine ⟨flag_agrees hA hq f, ?_⟩
    obtain ⟨a, b, c, d⟩ := q
    obtain ⟨ha, hb, hc, hd⟩ := hB.2.1 a b c d hq
    show nzcvId (a, b, c, d) f < vals.length
    match f with
    | 0 => exact ha
    | 1 => exact hb
    | 2 => exact hc
    | 3 => exact hd
  | lit c =>
    simp only [argOf, Option.some.injEq] at h
    subst h
    exact ⟨rfl, trivial⟩

theorem argsOf_sound {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {vals : List (BitVec 64)}
    {σ : Sym} {x : St} (hA : Agrees mapping pinv vals σ x) (hB : σ.Bounded vals.length) :
    ∀ (ss : List Src) (as : List Arg), argsOf σ ss = some as →
      as.map (Arg.eval vals) = ss.map (srcVal x) ∧ ∀ a ∈ as, a.Below vals.length := by
  intro ss
  induction ss with
  | nil => intro as h; simp only [argsOf, Option.some.injEq] at h; subst h; simp
  | cons s t ih =>
    intro as h
    simp only [argsOf] at h
    split at h
    · next a as' ha hs =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨e1, b1⟩ := argOf_sound hA hB s a ha
      obtain ⟨e2, b2⟩ := ih as' hs
      refine ⟨by simp [e1, e2], ?_⟩
      intro a' ma'
      simp only [List.mem_cons] at ma'
      rcases ma' with rfl | m
      · exact b1
      · exact b2 a' m
    · simp at h

/-- A definition whose arguments are all below n. -/
def Def.Below (n : Nat) (d : Def) : Prop := ∀ a ∈ d.args, a.Below n

theorem defOf_sound {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {vals : List (BitVec 64)}
    {σ : Sym} {x : St} (hA : Agrees mapping pinv vals σ x) (hB : σ.Bounded vals.length)
    (u : VUpd) (d : Def) (h : defOf σ u = some d) : d.eval vals = u.eval x ∧ d.Below vals.length := by
  simp only [defOf, Option.map_eq_some_iff] at h
  obtain ⟨as, has, rfl⟩ := h
  obtain ⟨e, b⟩ := argsOf_sound hA hB u.args as has
  exact ⟨by simp only [Def.eval, VUpd.eval, e], b⟩

/-! ## Table extension -/

theorem Arg.eval_append (vals pre : List (BitVec 64)) (a : Arg) (h : a.Below vals.length) :
    a.eval (vals ++ pre) = a.eval vals := by
  cases a with
  | id i => simp only [Arg.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < vals.length from h)]
  | imm c => rfl

theorem Def.eval_append (vals pre : List (BitVec 64)) (d : Def) (h : d.Below vals.length) :
    d.eval (vals ++ pre) = d.eval vals := by
  unfold Def.eval
  congr 1
  apply List.map_congr_left
  intro a ma
  exact Arg.eval_append vals pre a (h a ma)

/-- Definitions whose arguments are all in the pre-step table append their own values. -/
theorem extend_pre (vals : List (BitVec 64)) :
    ∀ (ds : List Def) (pre : List (BitVec 64)), (∀ d ∈ ds, d.Below vals.length) →
      extend (vals ++ pre) ds = vals ++ pre ++ ds.map (Def.eval vals) := by
  intro ds
  induction ds with
  | nil => intro pre _; simp [extend]
  | cons d t ih =>
    intro pre h
    have hd := Def.eval_append vals pre d (h d (List.mem_cons_self ..))
    have step : extend (vals ++ pre) (d :: t) = extend (vals ++ (pre ++ [d.eval vals])) t := by
      simp only [extend, List.foldl_cons, List.append_assoc, hd]
    rw [step, ih (pre ++ [d.eval vals]) (fun d' m => h d' (List.mem_cons_of_mem _ m))]
    simp

end ArmCertValue
