-- Evaluate every output of one actual instruction in the same source state.
import ArmCertValue.Expr
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertValue.Expr

/-- Materialize an output into a table id, including source/literal-only terms.
The added identity definition is an internal SSA node, not a machine write. -/
def compileValue (σ : Sym) (n : Nat) (term : Term) : Option (List Def × Nat) := do
  let (ds,arg) ← compile σ n term
  pure (ds ++ [⟨.add,[arg,.imm 0#64]⟩], n + ds.length)

theorem compileValue_sound (σ : Sym) (read : Src → BitVec 64)
    (term : Term) (vals : List (BitVec 64)) (ds : List Def) (id : Nat)
    (resolved : Resolved σ vals read) (compiled : compileValue σ vals.length term = some (ds,id)) :
    (extend vals ds).getD id 0 = eval read term ∧ id < (extend vals ds).length := by
  unfold compileValue at compiled
  cases h : compile σ vals.length term with
  | none => simp [h] at compiled
  | some p =>
    obtain ⟨more,arg⟩ := p
    simp [h] at compiled
    obtain ⟨rfl,rfl⟩ := compiled
    obtain ⟨value,bound⟩ := compile_sound σ read term vals more arg resolved h
    have out := emitted vals more ⟨.add,[arg,.imm 0#64]⟩
    refine ⟨out.1.trans ?_,out.2⟩
    change arg.eval (extend vals more) + 0#64 = eval read term
    rw [BitVec.add_zero,value]

/-- All terms see the original symbolic map. Appending temporaries never
substitutes a new machine-register value into a later output expression. -/
def compileValues (σ : Sym) : Nat → List Term → Option (List Def × List Nat)
  | _, [] => some ([],[])
  | n, term :: terms => do
      let (ds,id) ← compileValue σ n term
      let (rest,ids) ← compileValues σ (n + ds.length) terms
      pure (ds ++ rest,id :: ids)

theorem compileValues_sound (σ : Sym) (read : Src → BitVec 64) :
    ∀ terms vals ds ids, Resolved σ vals read → compileValues σ vals.length terms = some (ds,ids) →
      ids.map (fun i => (extend vals ds).getD i 0) = terms.map (eval read) ∧
      ∀ i ∈ ids, i < (extend vals ds).length := by
  intro terms
  induction terms with
  | nil =>
    intro vals ds ids _ compiled
    simp only [compileValues,Option.some.injEq,Prod.mk.injEq] at compiled
    obtain ⟨rfl,rfl⟩ := compiled
    exact ⟨rfl,by simp⟩
  | cons term terms ih =>
    intro vals ds ids resolved compiled
    simp only [compileValues] at compiled
    cases first : compileValue σ vals.length term with
    | none => simp [first] at compiled
    | some p =>
      obtain ⟨more,id⟩ := p
      cases rest : compileValues σ (vals.length + more.length) terms with
      | none => simp [first,rest] at compiled
      | some q =>
        obtain ⟨tail,tailIds⟩ := q
        simp [first,rest] at compiled
        obtain ⟨rfl,rfl⟩ := compiled
        obtain ⟨value,bound⟩ := compileValue_sound σ read term vals more id resolved first
        have rest' : compileValues σ (extend vals more).length terms = some (tail,tailIds) := by
          rw [extend_length]; exact rest
        obtain ⟨values,bounds⟩ := ih (extend vals more) tail tailIds (resolved_extend resolved more) rest'
        have firstValue := (arg_extend (extend vals more) tail (.id id) bound).trans value
        refine ⟨?_,?_⟩
        · simp only [extend_append,List.map_cons,← values]
          exact congrArg (fun v => v :: tailIds.map (fun i => (extend (extend vals more) tail).getD i 0)) firstValue
        · intro i member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · rw [extend_length] at bound ⊢
            simp only [List.length_append]
            omega
          · rw [extend_append]
            exact bounds i member

theorem compileValues_physical {bytePA : Physical.BytePA} {vals : List (BitVec 64)} {σ : Sym}
    {x : HeapV2StepCerts.RegBind.St} (agree : Physical.Agrees bytePA vals σ x)
    (bounded : σ.Bounded vals.length) (terms : List Term) (ds : List Def) (ids : List Nat)
    (compiled : compileValues σ vals.length terms = some (ds,ids)) :
    ids.map (fun i => (extend vals ds).getD i 0) = terms.map (eval (srcVal x)) ∧
      ∀ i ∈ ids, i < (extend vals ds).length :=
  compileValues_sound σ (srcVal x) terms vals ds ids (Physical.argOf_sound agree bounded) compiled

/-- Machine locations affected by arithmetic instructions; memory remains framed. -/
inductive Location where
  | reg (r : HeapV2StepCerts.RegBind.Reg)
  | flag (i : Fin 4)
  deriving DecidableEq, Repr

def locationId (σ : Sym) : Location → Option Nat
  | .reg r => σ.regs r
  | .flag f => σ.nzcv.map fun q => nzcvId q f

def locationValue (x : HeapV2StepCerts.RegBind.St) : Location → BitVec 64
  | .reg r => HeapV2StepCerts.RegBind.regVal x r
  | .flag f => flagWord x f

/-- Static correspondence of the output map to compiled expression ids.
This contains no machine state, run, or execution hypothesis. -/
structure OutputBindings (σ τ : Sym) (outputs : List (Location × Term)) (ids : List Nat) : Prop where
  memory : τ.memB = σ.memB
  locations : ∀ l j, locationId τ l = some j →
    (locationId σ l = some j ∧ ∀ e, (l,e) ∉ outputs) ∨
    ∃ (k : Nat) (e : Term), outputs[k]? = some (l,e) ∧ ids[k]? = some j

/-- Actual instruction results and frame, to be derived from its native Sail theorem. -/
def OutputHolds (outputs : List (Location × Term))
    (x y : HeapV2StepCerts.RegBind.St) : Prop :=
  (∀ l e, (l,e) ∈ outputs → locationValue y l = eval (srcVal x) e) ∧
  (∀ l, (∀ e, (l,e) ∉ outputs) → locationValue y l = locationValue x l)

theorem location_agrees {bytePA : Physical.BytePA} {vals : List (BitVec 64)} {σ : Sym}
    {x : HeapV2StepCerts.RegBind.St} (agree : Physical.Agrees bytePA vals σ x)
    (bounded : σ.Bounded vals.length) (l : Location) (id : Nat) (tracked : locationId σ l = some id) :
    locationValue x l = vals.getD id 0 ∧ id < vals.length := by
  cases l with
  | reg r => exact ⟨agree.1 r id tracked,bounded.1 r id tracked⟩
  | flag f =>
    obtain ⟨q,hq,he⟩ := Option.map_eq_some_iff.1 tracked
    subst he
    refine ⟨(Physical.flag_agrees agree hq f).symm,?_⟩
    obtain ⟨a,b,c,d⟩ := q
    obtain ⟨ha,hb,hc,hd⟩ := bounded.2.1 a b c d hq
    match f with
    | 0 => exact ha
    | 1 => exact hb
    | 2 => exact hc
    | 3 => exact hd

/-- Generic arithmetic-step transport. The static map certificate, expression
compiler correctness, and actual native result/frame establish the next physical
SSA relation, without any invented machine instruction or register write. -/
theorem outputs_agree {bytePA : Physical.BytePA} {vals : List (BitVec 64)} {σ τ : Sym}
    {x y : HeapV2StepCerts.RegBind.St} (agree : Physical.Agrees bytePA vals σ x)
    (bounded : σ.Bounded vals.length) (outputs : List (Location × Term)) (ds : List Def) (ids : List Nat)
    (compiled : compileValues σ vals.length (outputs.map (·.2)) = some (ds,ids))
    (bindings : OutputBindings σ τ outputs ids) (holds : OutputHolds outputs x y)
    (memory : y.mem = x.mem) :
    Physical.Agrees bytePA (extend vals ds) τ y ∧ τ.Bounded (extend vals ds).length := by
  obtain ⟨values,bounds⟩ := compileValues_physical agree bounded (outputs.map (·.2)) ds ids compiled
  have locations : ∀ l id, locationId τ l = some id →
      locationValue y l = (extend vals ds).getD id 0 ∧ id < (extend vals ds).length := by
    intro l id tracked
    rcases bindings.locations l id tracked with ⟨old,unchanged⟩ | ⟨k,e,outputAt,idAt⟩
    · obtain ⟨value,bound⟩ := location_agrees agree bounded l id old
      refine ⟨?_,?_⟩
      · have preserved := arg_extend vals ds (.id id) bound
        exact (holds.2 l unchanged).trans (value.trans preserved.symm)
      · rw [extend_length]; omega
    · have selected := congrArg (fun xs => xs[k]?) values
      simp only [List.map_map,List.getElem?_map,idAt,outputAt,Option.map_some,Option.some.injEq] at selected
      exact ⟨(holds.1 l e (List.mem_of_getElem? outputAt)).trans selected.symm,
        bounds id (List.mem_of_getElem? idAt)⟩
  refine ⟨⟨?_,?_,?_⟩,⟨?_,?_,?_⟩⟩
  · intro r id tracked
    exact (locations (.reg r) id tracked).1
  · intro a b c d tracked
    exact ⟨(locations (.flag 0) a (by simp [locationId,tracked,nzcvId])).1,
      (locations (.flag 1) b (by simp [locationId,tracked,nzcvId])).1,
      (locations (.flag 2) c (by simp [locationId,tracked,nzcvId])).1,
      (locations (.flag 3) d (by simp [locationId,tracked,nzcvId])).1⟩
  · intro r j id k tracked
    rw [bindings.memory] at tracked
    have old := agree.2.2 r j id k tracked
    have keep := arg_extend vals ds (.id id) (bounded.2.2 r j id k tracked)
    change (extend vals ds).getD id 0 = vals.getD id 0 at keep
    rw [keep]
    simpa only [Physical.regionByte,memory] using old
  · intro r id tracked
    exact (locations (.reg r) id tracked).2
  · intro a b c d tracked
    exact ⟨(locations (.flag 0) a (by simp [locationId,tracked,nzcvId])).2,
      (locations (.flag 1) b (by simp [locationId,tracked,nzcvId])).2,
      (locations (.flag 2) c (by simp [locationId,tracked,nzcvId])).2,
      (locations (.flag 3) d (by simp [locationId,tracked,nzcvId])).2⟩
  · intro r j id k tracked
    rw [bindings.memory] at tracked
    have bound := bounded.2.2 r j id k tracked
    rw [extend_length]; omega

/-- A single arithmetic destination, preserving every other symbolic location. -/
def writeRegMap (σ : Sym) (r : HeapV2StepCerts.RegBind.Reg) (id : Nat) : Sym where
  regs := fun q => if q = r then some id else σ.regs q
  nzcv := σ.nzcv
  memB := σ.memB

theorem writeReg_bindings (σ : Sym) (r : HeapV2StepCerts.RegBind.Reg) (term : Term) (id : Nat) :
    OutputBindings σ (writeRegMap σ r id) [(.reg r,term)] [id] := by
  refine ⟨rfl,?_⟩
  intro l j tracked
  cases l with
  | reg q =>
    by_cases same : q = r
    · subst q
      simp only [locationId,writeRegMap,ite_true,Option.some.injEq] at tracked
      subst j
      exact Or.inr ⟨0,term,rfl,rfl⟩
    · refine Or.inl ⟨?_,?_⟩
      · simpa only [locationId,writeRegMap,if_neg same] using tracked
      · intro e; simp [same,Ne.symm same]
  | flag f => exact Or.inl ⟨tracked,by intro e; simp⟩

def writeFlagsMap (σ : Sym) (a b c d : Nat) : Sym where
  regs := σ.regs
  nzcv := some (a,b,c,d)
  memB := σ.memB

theorem writeFlags_bindings (σ : Sym) (fn fz fc fv : Term) (a b c d : Nat) :
    OutputBindings σ (writeFlagsMap σ a b c d)
      [(.flag 0,fn),(.flag 1,fz),(.flag 2,fc),(.flag 3,fv)] [a,b,c,d] := by
  refine ⟨rfl,?_⟩
  intro l j tracked
  cases l with
  | reg r => exact Or.inl ⟨tracked,by intro e; simp⟩
  | flag f =>
    match f with
    | 0 =>
      have same : a = j := by simpa only [locationId,writeFlagsMap,Option.map_some,nzcvId,Option.some.injEq] using tracked
      subst j; exact Or.inr ⟨0,fn,rfl,rfl⟩
    | 1 =>
      have same : b = j := by simpa only [locationId,writeFlagsMap,Option.map_some,nzcvId,Option.some.injEq] using tracked
      subst j; exact Or.inr ⟨1,fz,rfl,rfl⟩
    | 2 =>
      have same : c = j := by simpa only [locationId,writeFlagsMap,Option.map_some,nzcvId,Option.some.injEq] using tracked
      subst j; exact Or.inr ⟨2,fc,rfl,rfl⟩
    | 3 =>
      have same : d = j := by simpa only [locationId,writeFlagsMap,Option.map_some,nzcvId,Option.some.injEq] using tracked
      subst j; exact Or.inr ⟨3,fv,rfl,rfl⟩

theorem writeRegFlags_bindings (σ : Sym) (r : HeapV2StepCerts.RegBind.Reg)
    (term fn fz fc fv : Term) (id a b c d : Nat) :
    OutputBindings σ (writeFlagsMap (writeRegMap σ r id) a b c d)
      [(.reg r,term),(.flag 0,fn),(.flag 1,fz),(.flag 2,fc),(.flag 3,fv)] [id,a,b,c,d] := by
  refine ⟨rfl,?_⟩
  intro l j tracked
  cases l with
  | reg q =>
    by_cases same : q = r
    · subst q
      simp only [locationId,writeFlagsMap,writeRegMap,ite_true,Option.some.injEq] at tracked
      subst j; exact Or.inr ⟨0,term,rfl,rfl⟩
    · refine Or.inl ⟨?_,?_⟩
      · simpa only [locationId,writeFlagsMap,writeRegMap,if_neg same] using tracked
      · intro e; simp [same,Ne.symm same]
  | flag f =>
    match f with
    | 0 =>
      have same : a = j := by simpa only [locationId,writeFlagsMap,Option.map_some,nzcvId,Option.some.injEq] using tracked
      subst j; exact Or.inr ⟨1,fn,rfl,rfl⟩
    | 1 =>
      have same : b = j := by simpa only [locationId,writeFlagsMap,Option.map_some,nzcvId,Option.some.injEq] using tracked
      subst j; exact Or.inr ⟨2,fz,rfl,rfl⟩
    | 2 =>
      have same : c = j := by simpa only [locationId,writeFlagsMap,Option.map_some,nzcvId,Option.some.injEq] using tracked
      subst j; exact Or.inr ⟨3,fc,rfl,rfl⟩
    | 3 =>
      have same : d = j := by simpa only [locationId,writeFlagsMap,Option.map_some,nzcvId,Option.some.injEq] using tracked
      subst j; exact Or.inr ⟨4,fv,rfl,rfl⟩

#print axioms compileValue_sound
#print axioms compileValues_sound
#print axioms compileValues_physical
#print axioms location_agrees
#print axioms outputs_agree
#print axioms writeReg_bindings
#print axioms writeFlags_bindings
#print axioms writeRegFlags_bindings
end ArmCertValue.Expr
