-- ArmCert VALUE LAYER: `compile` one plan step and prove `step_agrees` once.
import ArmCertValue.Step
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue
open HeapV2StepCerts.RegBind (Reg St regVal)

/-! ## Register updates -/

/-- Definitions for the `some` entries of `us`, in order. -/
def regDefs (σ : Sym) : List (Reg × Option VUpd) → Option (List Def)
  | [] => some []
  | (_, none) :: t => regDefs σ t
  | (_, some u) :: t => match defOf σ u, regDefs σ t with
    | some d, some ds => some (d :: ds)
    | _, _ => none

/-- New register ids; the first entry for a register wins (as in `VHolds`). `k` is the next id. -/
def regMap (σ : Sym) : Nat → List (Reg × Option VUpd) → Reg → Option Nat
  | _, [] => σ.regs
  | k, (r, none) :: t => fun r' => if r' = r then none else regMap σ k t r'
  | k, (r, some _) :: t => fun r' => if r' = r then some k else regMap σ (k + 1) t r'

def lookupUpd (us : List (Reg × Option VUpd)) (r : Reg) : Option (Option VUpd) :=
  (us.find? (·.1 = r)).map (·.2)

theorem regMap_spec (σ : Sym) :
    ∀ (us : List (Reg × Option VUpd)) (k : Nat) (ds : List Def), regDefs σ us = some ds →
      ∀ r i, regMap σ k us r = some i →
        (lookupUpd us r = none ∧ σ.regs r = some i) ∨
        (∃ u d j, lookupUpd us r = some (some u) ∧ defOf σ u = some d ∧ ds[j]? = some d ∧ i = k + j) := by
  intro us
  induction us with
  | nil =>
    intro k ds _ r i h
    exact Or.inl ⟨rfl, h⟩
  | cons p t ih =>
    obtain ⟨r0, o⟩ := p
    intro k ds hd r i h
    cases o with
    | none =>
      simp only [regDefs] at hd
      simp only [regMap] at h
      by_cases hr : r = r0
      · simp [hr] at h
      · rw [if_neg hr] at h
        have hl : lookupUpd ((r0, none) :: t) r = lookupUpd t r := by
          simp [lookupUpd, List.find?_cons, Ne.symm hr]
        rw [hl]
        exact ih k ds hd r i h
    | some u =>
      simp only [regDefs] at hd
      split at hd
      · next d ds' hdu hdt =>
        simp only [Option.some.injEq] at hd
        subst hd
        simp only [regMap] at h
        by_cases hr : r = r0
        · subst hr
          have hk : i = k := by simpa using h.symm
          refine Or.inr ⟨u, d, 0, ?_, hdu, rfl, by omega⟩
          simp [lookupUpd]
        · rw [if_neg hr] at h
          have hl : lookupUpd ((r0, some u) :: t) r = lookupUpd t r := by
            simp [lookupUpd, List.find?_cons, Ne.symm hr]
          rw [hl]
          rcases ih (k + 1) ds' hdt r i h with h1 | ⟨u', d', j, h1, h2, h3, h4⟩
          · exact Or.inl h1
          · exact Or.inr ⟨u', d', j + 1, h1, h2, by simpa using h3, by omega⟩
      · simp at hd

theorem regDefs_below {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {vals : List (BitVec 64)}
    {σ : Sym} {x : St} (hA : Agrees mapping pinv vals σ x) (hB : σ.Bounded vals.length) :
    ∀ (us : List (Reg × Option VUpd)) (ds : List Def), regDefs σ us = some ds → ∀ d ∈ ds, d.Below vals.length := by
  intro us
  induction us with
  | nil => intro ds h; simp only [regDefs, Option.some.injEq] at h; subst h; simp
  | cons p t ih =>
    obtain ⟨r0, o⟩ := p
    intro ds h
    cases o with
    | none => exact ih ds h
    | some u =>
      simp only [regDefs] at h
      split at h
      · next d ds' hdu hdt =>
        simp only [Option.some.injEq] at h
        subst h
        intro d' m
        simp only [List.mem_cons] at m
        rcases m with rfl | m
        · exact (defOf_sound hA hB u d' hdu).2
        · exact ih ds' hdt d' m
      · simp at h

/-! ## Flags, loads, stores -/

def flagDefs (σ : Sym) : Option (VUpd × VUpd × VUpd × VUpd) → Option (List Def)
  | none => some []
  | some (a, b, c, d) => match defOf σ a, defOf σ b, defOf σ c, defOf σ d with
    | some a', some b', some c', some d' => some [a', b', c', d']
    | _, _, _, _ => none

/-! ## Memory effects (find?-based: robust to new MemEff constructors) -/

def MemEff.reg : MemEff → Reg
  | .load rt _ _ | .store rt _ _ | .loadb rt _ _ | .storeb rt _ _ | .load32 rt _ _ | .store32 rt _ _ => rt

def isStoreAt (g : Region) (w : Nat) : MemEff → Bool
  | .store _ g' w' => g' == g && w' == w
  | _ => false

def isStorebAt (g : Region) (j : Nat) : MemEff → Bool
  | .storeb _ g' j' => g' == g && j' == j
  | _ => false

def isStore32Cov (g : Region) (j : Nat) : MemEff → Bool
  | .store32 _ g' j' => g' == g && j' ≤ j && j < j' + 4
  | _ => false

def MemEff.off32 : MemEff → Nat
  | .store32 _ _ j' => j'
  | _ => 0

def storeOf (effs : List MemEff) (g : Region) (w : Nat) : Option Reg :=
  (effs.find? (isStoreAt g w)).map MemEff.reg

def storebOf (effs : List MemEff) (g : Region) (j : Nat) : Option Reg :=
  (effs.find? (isStorebAt g j)).map MemEff.reg

def store32Of (effs : List MemEff) (g : Region) (j : Nat) : Option (Reg × Nat) :=
  (effs.find? (isStore32Cov g j)).map fun e => (e.reg, j - e.off32)

theorem storeOf_mem (effs : List MemEff) (g : Region) (w : Nat) (rt : Reg)
    (h : storeOf effs g w = some rt) : MemEff.store rt g w ∈ effs := by
  simp only [storeOf, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have m := List.mem_of_find?_eq_some he
  have p := List.find?_some he
  cases e <;> simp_all [isStoreAt, MemEff.reg]

theorem storeOf_none (effs : List MemEff) (g : Region) (w : Nat)
    (h : storeOf effs g w = none) : ∀ rt, MemEff.store rt g w ∉ effs := by
  intro rt m
  simp only [storeOf, Option.map_eq_none_iff, List.find?_eq_none] at h
  have := h _ m
  simp [isStoreAt] at this

theorem storebOf_mem (effs : List MemEff) (g : Region) (j : Nat) (rt : Reg)
    (h : storebOf effs g j = some rt) : MemEff.storeb rt g j ∈ effs := by
  simp only [storebOf, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have m := List.mem_of_find?_eq_some he
  have p := List.find?_some he
  cases e <;> simp_all [isStorebAt, MemEff.reg]

theorem storebOf_none (effs : List MemEff) (g : Region) (j : Nat)
    (h : storebOf effs g j = none) : ∀ rt, MemEff.storeb rt g j ∉ effs := by
  intro rt m
  simp only [storebOf, Option.map_eq_none_iff, List.find?_eq_none] at h
  have := h _ m
  simp [isStorebAt] at this

theorem store32Of_mem (effs : List MemEff) (g : Region) (j : Nat) (rt : Reg) (t : Nat)
    (h : store32Of effs g j = some (rt, t)) :
    ∃ j', MemEff.store32 rt g j' ∈ effs ∧ j = j' + t ∧ t < 4 := by
  simp only [store32Of, Option.map_eq_some_iff] at h
  obtain ⟨e, he, hrt⟩ := h
  have m := List.mem_of_find?_eq_some he
  have p := List.find?_some he
  cases e with
  | store32 rt0 g0 j0 =>
    simp only [isStore32Cov, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at p
    obtain ⟨⟨rfl, h1⟩, h2⟩ := p
    simp only [MemEff.reg, MemEff.off32, Prod.mk.injEq] at hrt
    obtain ⟨rfl, rfl⟩ := hrt
    exact ⟨j0, m, by omega, by omega⟩
  | _ => simp [isStore32Cov] at p

theorem store32Of_none (effs : List MemEff) (g : Region) (j : Nat)
    (h : store32Of effs g j = none) : ∀ rt j', MemEff.store32 rt g j' ∈ effs → ¬ (j' ≤ j ∧ j < j' + 4) := by
  intro rt j' m hc
  simp only [store32Of, Option.map_eq_none_iff, List.find?_eq_none] at h
  have := h _ m
  simp [isStore32Cov] at this
  omega

/-! ## Load definitions (memory -> registers) -/

/-- The 8 tracked bytes of word w of region g, as (args, byte positions). -/
def bytesOf (σ : Sym) (g : Region) (w : Nat) : Option (List Arg × List Nat) :=
  match σ.memB g (8 * w), σ.memB g (8 * w + 1), σ.memB g (8 * w + 2), σ.memB g (8 * w + 3),
      σ.memB g (8 * w + 4), σ.memB g (8 * w + 5), σ.memB g (8 * w + 6), σ.memB g (8 * w + 7) with
  | some (i0, k0), some (i1, k1), some (i2, k2), some (i3, k3),
    some (i4, k4), some (i5, k5), some (i6, k6), some (i7, k7) =>
      some ([.id i0, .id i1, .id i2, .id i3, .id i4, .id i5, .id i6, .id i7], [k0, k1, k2, k3, k4, k5, k6, k7])
  | _, _, _, _, _, _, _, _ => none

/-- The 4 tracked bytes j..j+3 of region g. -/
def bytes4Of (σ : Sym) (g : Region) (j : Nat) : Option (List Arg × List Nat) :=
  match σ.memB g (j + 0), σ.memB g (j + 1), σ.memB g (j + 2), σ.memB g (j + 3) with
  | some (i0, k0), some (i1, k1), some (i2, k2), some (i3, k3) =>
      some ([.id i0, .id i1, .id i2, .id i3], [k0, k1, k2, k3])
  | _, _, _, _ => none

/-- The definition a load effect needs (none: untracked source, or not a load). -/
def loadDef (σ : Sym) : MemEff → Option Def
  | .load _ g w => (bytesOf σ g w).map fun p => ⟨.asm8 p.2, p.1⟩
  | .loadb _ g j => (σ.memB g j).map fun p => ⟨.byteAt p.2, [.id p.1]⟩
  | .load32 _ g j => (bytes4Of σ g j).map fun p => ⟨.asm4 p.2, p.1⟩
  | _ => none

def loadReg : MemEff → Option Reg
  | .load rt _ _ => some rt
  | .loadb rt _ _ => some rt
  | .load32 rt _ _ => some rt
  | _ => none

def memDefs (σ : Sym) : List MemEff → List Def
  | [] => []
  | e :: t => match loadDef σ e with
    | some d => d :: memDefs σ t
    | none => memDefs σ t

/-- Register ids after the loads: `some x` = r is loaded (x = its id, none if untracked); first load wins. -/
def memMap (σ : Sym) : Nat → List MemEff → Reg → Option (Option Nat)
  | _, [], _ => none
  | k, e :: t, r => match loadReg e, loadDef σ e with
    | some rt, some _ => if rt = r then some (some k) else memMap σ (k + 1) t r
    | some rt, none => if rt = r then some none else memMap σ k t r
    | none, some _ => memMap σ (k + 1) t r
    | none, none => memMap σ k t r

theorem loadDef_none_of_reg {σ : Sym} {e : MemEff} (h : loadReg e = none) : loadDef σ e = none := by
  cases e <;> simp_all [loadReg, loadDef]

theorem memMap_spec (σ : Sym) : ∀ (effs : List MemEff) (k : Nat) (r : Reg) (i : Nat),
    memMap σ k effs r = some (some i) →
      ∃ e d j, e ∈ effs ∧ loadReg e = some r ∧ loadDef σ e = some d ∧ (memDefs σ effs)[j]? = some d ∧ i = k + j := by
  intro effs
  induction effs with
  | nil => intro k r i h; simp [memMap] at h
  | cons e t ih =>
    intro k r i h
    simp only [memMap] at h
    cases hr : loadReg e with
    | none =>
      rw [hr, loadDef_none_of_reg hr] at h
      obtain ⟨e', d, j, m, h1, h2, h3, h4⟩ := ih k r i h
      refine ⟨e', d, j, List.mem_cons_of_mem _ m, h1, h2, ?_, h4⟩
      simp only [memDefs, loadDef_none_of_reg hr]; exact h3
    | some rt =>
      rw [hr] at h
      cases hd : loadDef σ e with
      | none =>
        simp only [hd] at h
        by_cases hrt : rt = r
        · rw [if_pos hrt] at h; cases h
        · rw [if_neg hrt] at h
          obtain ⟨e', d, j, m, h1, h2, h3, h4⟩ := ih k r i h
          refine ⟨e', d, j, List.mem_cons_of_mem _ m, h1, h2, ?_, h4⟩
          simp only [memDefs, hd]; exact h3
      | some d0 =>
        simp only [hd] at h
        by_cases hrt : rt = r
        · rw [if_pos hrt] at h
          simp only [Option.some.injEq] at h
          refine ⟨e, d0, 0, List.mem_cons_self .., by rw [hr, hrt], hd, ?_, by omega⟩
          simp only [memDefs, hd]; rfl
        · rw [if_neg hrt] at h
          obtain ⟨e', d, j, m, h1, h2, h3, h4⟩ := ih (k + 1) r i h
          refine ⟨e', d, j + 1, List.mem_cons_of_mem _ m, h1, h2, ?_, by omega⟩
          simp only [memDefs, hd]; simpa using h3

theorem memDefs_mem (σ : Sym) : ∀ (effs : List MemEff) (d : Def), d ∈ memDefs σ effs →
    ∃ e ∈ effs, loadDef σ e = some d := by
  intro effs
  induction effs with
  | nil => intro d h; simp [memDefs] at h
  | cons e t ih =>
    intro d h
    simp only [memDefs] at h
    split at h
    · next d0 hd =>
      simp only [List.mem_cons] at h
      rcases h with rfl | m
      · exact ⟨e, List.mem_cons_self .., hd⟩
      · obtain ⟨e', m', h'⟩ := ih d m; exact ⟨e', List.mem_cons_of_mem _ m', h'⟩
    · obtain ⟨e', m', h'⟩ := ih d h; exact ⟨e', List.mem_cons_of_mem _ m', h'⟩

/-! ## One step -/

def compile (σ : Sym) (n : Nat) (regions : List Region) (st : StepV) : Option (List Def × Sym) :=
  match regDefs σ st.us, flagDefs σ st.fl with
  | some rds, some fds => some (rds ++ fds ++ memDefs σ st.mem,
      { regs := fun r => match memMap σ (n + rds.length + fds.length) st.mem r with
          | some x => x
          | none => regMap σ n st.us r
        nzcv := match st.fl with
          | none => σ.nzcv
          | some _ => some (n + rds.length, n + rds.length + 1, n + rds.length + 2, n + rds.length + 3)
        memB := fun g j => match storebOf st.mem g j with
          | some rt => (σ.regs rt).map fun i => (i, 0)
          | none => match storeOf st.mem g (j / 8) with
            | some rt => (σ.regs rt).map fun i => (i, j % 8)
            | none => match store32Of st.mem g j with
              | some (rt, t) => (σ.regs rt).map fun i => (i, t)
              | none => if g ∈ regions ∧ j < 8 * g.words then σ.memB g j else none })
  | _, _ => none

end ArmCertValue
