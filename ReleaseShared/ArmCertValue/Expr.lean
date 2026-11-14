-- Additive instruction-local expressions compiled to the existing Core SSA.
import ArmCertValue.PhysicalSSA
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertValue.Expr

inductive Term where
  | source (s : Src)
  | literal (c : BitVec 64)
  | flat (u : VUpd)
  | unary (op : Op) (a : Term)
  | binary (op : Op) (a b : Term)
  | ternary (op : Op) (a b c : Term)
  deriving Repr

def eval (read : Src → BitVec 64) : Term → BitVec 64
  | .source s => read s
  | .literal c => c
  | .flat u => u.op.eval (u.args.map read)
  | .unary op a => op.eval [eval read a]
  | .binary op a b => op.eval [eval read a, eval read b]
  | .ternary op a b c => op.eval [eval read a, eval read b, eval read c]

/-- Internal SSA temporaries do not correspond to extra machine instructions or writes. -/
def compile (σ : Sym) (n : Nat) : Term → Option (List Def × Arg)
  | .source s => (argOf σ s).map fun a => ([], a)
  | .literal c => some ([], .imm c)
  | .flat u => (defOf σ u).map fun d => ([d], .id n)
  | .unary op a => do
      let (ds, arg) ← compile σ n a
      pure (ds ++ [⟨op, [arg]⟩], .id (n + ds.length))
  | .binary op a b => do
      let (da, aa) ← compile σ n a
      let (db, ab) ← compile σ (n + da.length) b
      pure (da ++ db ++ [⟨op, [aa, ab]⟩], .id (n + da.length + db.length))
  | .ternary op a b c => do
      let (da, aa) ← compile σ n a
      let (db, ab) ← compile σ (n + da.length) b
      let (dc, ac) ← compile σ (n + da.length + db.length) c
      pure (da ++ db ++ dc ++ [⟨op, [aa, ab, ac]⟩], .id (n + da.length + db.length + dc.length))

def Resolved (σ : Sym) (vals : List (BitVec 64)) (read : Src → BitVec 64) : Prop :=
  ∀ s a, argOf σ s = some a → a.eval vals = read s ∧ a.Below vals.length

private theorem input_prefix : ∀ (ds : List Def) (vals : List (BitVec 64)) (i : Nat),
    i < vals.length → (extend vals ds).getD i 0 = vals.getD i 0
  | [], _, _, _ => rfl
  | d :: ds, vals, i, h => by
    show (extend (vals ++ [d.eval vals]) ds).getD i 0 = _
    rw [input_prefix ds (vals ++ [d.eval vals]) i (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem arg_extend (vals : List (BitVec 64)) (ds : List Def) (a : Arg)
    (bound : a.Below vals.length) : a.eval (extend vals ds) = a.eval vals := by
  cases a with
  | imm _ => rfl
  | id i => exact input_prefix ds vals i bound

theorem resolved_extend {σ : Sym} {vals : List (BitVec 64)} {read : Src → BitVec 64}
    (h : Resolved σ vals read) (ds : List Def) : Resolved σ (extend vals ds) read := by
  intro s a ha
  obtain ⟨value, bound⟩ := h s a ha
  refine ⟨(arg_extend vals ds a bound).trans value, ?_⟩
  cases a with
  | imm _ => trivial
  | id i =>
    change i < vals.length at bound
    show i < (extend vals ds).length
    rw [extend_length]; omega

theorem args_sound {σ : Sym} {vals : List (BitVec 64)} {read : Src → BitVec 64}
    (h : Resolved σ vals read) : ∀ ss as, argsOf σ ss = some as →
      as.map (Arg.eval vals) = ss.map read := by
  intro ss
  induction ss with
  | nil => intro as hs; simp only [argsOf, Option.some.injEq] at hs; subst hs; rfl
  | cons s ss ih =>
    intro as hs
    simp only [argsOf] at hs
    split at hs
    · next a rest ha hr =>
      simp only [Option.some.injEq] at hs
      subst hs
      simp only [List.map_cons, (h s a ha).1, ih rest hr]
    · simp at hs

theorem emitted (vals : List (BitVec 64)) (ds : List Def) (d : Def) :
    (Arg.id (vals.length + ds.length)).eval (extend vals (ds ++ [d])) = d.eval (extend vals ds) ∧
      (Arg.id (vals.length + ds.length)).Below (extend vals (ds ++ [d])).length := by
  rw [extend_append]
  have len := extend_length vals ds
  constructor
  · change (extend (extend vals ds) [d]).getD (vals.length + ds.length) 0 = _
    rw [← len]
    simpa only [extend, List.foldl_cons, List.foldl_nil, Nat.add_zero, List.getD_cons_zero]
      using getD_right (extend vals ds) [d.eval (extend vals ds)] 0
  · change vals.length + ds.length < (extend (extend vals ds) [d]).length
    rw [extend_length, len]; simp

/-- Every compound instruction expression has the ordinary existing SSA semantics.
No property of the Sail interpreter is assumed by this compiler theorem. -/
theorem compile_sound (σ : Sym) (read : Src → BitVec 64) :
    ∀ term vals ds arg, Resolved σ vals read → compile σ vals.length term = some (ds,arg) →
      arg.eval (extend vals ds) = eval read term ∧ arg.Below (extend vals ds).length := by
  intro term
  induction term with
  | source s =>
    intro vals ds arg hr hc
    simp only [compile, Option.map_eq_some_iff] at hc
    obtain ⟨a,ha,he⟩ := hc
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    simpa only [extend, List.foldl_nil, eval] using hr s a ha
  | literal c =>
    intro vals ds arg hr hc
    simp only [compile, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl,rfl⟩ := hc
    exact ⟨rfl,trivial⟩
  | flat u =>
    intro vals ds arg hr hc
    simp only [compile, Option.map_eq_some_iff] at hc
    obtain ⟨d,hd,he⟩ := hc
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    have value : d.eval vals = eval read (.flat u) := by
      obtain ⟨as,has,rfl⟩ := Option.map_eq_some_iff.1 hd
      exact congrArg (Op.eval u.op) (args_sound hr u.args as has)
    simpa only [List.nil_append, List.length_nil, Nat.add_zero, extend, List.foldl_nil] using
      And.intro ((emitted vals [] d).1.trans value) (emitted vals [] d).2
  | unary op a ih =>
    intro vals ds arg hr hc
    simp only [compile] at hc
    cases ha : compile σ vals.length a with
    | none => simp [ha] at hc
    | some p =>
      obtain ⟨da,aa⟩ := p
      simp [ha] at hc
      obtain ⟨rfl,rfl⟩ := hc
      obtain ⟨va,ba⟩ := ih vals da aa hr ha
      exact ⟨(emitted vals da ⟨op,[aa]⟩).1.trans (by simp only [Def.eval,List.map_cons,List.map_nil,va,eval]),
        (emitted vals da ⟨op,[aa]⟩).2⟩
  | binary op a b iha ihb =>
    intro vals ds arg hr hc
    simp only [compile] at hc
    cases ha : compile σ vals.length a with
    | none => simp [ha] at hc
    | some pa =>
      obtain ⟨da,aa⟩ := pa
      cases hb : compile σ (vals.length + da.length) b with
      | none => simp [ha,hb] at hc
      | some pb =>
        obtain ⟨db,ab⟩ := pb
        simp [ha,hb] at hc
        obtain ⟨rfl,rfl⟩ := hc
        obtain ⟨va,ba⟩ := iha vals da aa hr ha
        have hb' : compile σ (extend vals da).length b = some (db,ab) := by rw [extend_length]; exact hb
        obtain ⟨vb,bb⟩ := ihb (extend vals da) db ab (resolved_extend hr da) hb'
        have va' := (arg_extend (extend vals da) db aa ba).trans va
        have out := emitted vals (da ++ db) ⟨op,[aa,ab]⟩
        simp only [List.length_append, ← Nat.add_assoc, List.append_assoc] at out
        refine ⟨?_,out.2⟩
        rw [out.1]
        simp only [Def.eval,List.map_cons,List.map_nil,extend_append,va',vb,eval]
  | ternary op a b c iha ihb ihc =>
    intro vals ds arg hr hc
    simp only [compile] at hc
    cases ha : compile σ vals.length a with
    | none => simp [ha] at hc
    | some pa =>
      obtain ⟨da,aa⟩ := pa
      cases hb : compile σ (vals.length + da.length) b with
      | none => simp [ha,hb] at hc
      | some pb =>
        obtain ⟨db,ab⟩ := pb
        cases hd : compile σ (vals.length + da.length + db.length) c with
        | none => simp [ha,hb,hd] at hc
        | some pc =>
          obtain ⟨dc,ac⟩ := pc
          simp [ha,hb,hd] at hc
          obtain ⟨rfl,rfl⟩ := hc
          obtain ⟨va,ba⟩ := iha vals da aa hr ha
          have hb' : compile σ (extend vals da).length b = some (db,ab) := by rw [extend_length]; exact hb
          obtain ⟨vb,bb⟩ := ihb (extend vals da) db ab (resolved_extend hr da) hb'
          have vd : (extend (extend vals da) db).length = vals.length + da.length + db.length := by rw [extend_length,extend_length]
          have hd' : compile σ (extend (extend vals da) db).length c = some (dc,ac) := by rw [vd]; exact hd
          obtain ⟨vc,bc⟩ := ihc (extend (extend vals da) db) dc ac (resolved_extend (resolved_extend hr da) db) hd'
          have va' := (arg_extend (extend vals da) (db ++ dc) aa ba).trans va
          have vb' := (arg_extend (extend (extend vals da) db) dc ab bb).trans vb
          have out := emitted vals (da ++ db ++ dc) ⟨op,[aa,ab,ac]⟩
          simp only [List.length_append, ← Nat.add_assoc, List.append_assoc] at out
          refine ⟨?_,out.2⟩
          rw [out.1]
          simp only [extend_append] at va'
          simp only [Def.eval,List.map_cons,List.map_nil,extend_append,va',vb',vc,eval]

/-- The only machine-facing premise is the existing physical SSA agreement. -/
theorem compile_physical {bytePA : Physical.BytePA} {vals : List (BitVec 64)} {σ : Sym}
    {x : HeapV2StepCerts.RegBind.St} (agree : Physical.Agrees bytePA vals σ x)
    (bounded : σ.Bounded vals.length) (term : Term) (ds : List Def) (arg : Arg)
    (compiled : compile σ vals.length term = some (ds,arg)) :
    arg.eval (extend vals ds) = eval (srcVal x) term ∧ arg.Below (extend vals ds).length :=
  compile_sound σ (srcVal x) term vals ds arg (Physical.argOf_sound agree bounded) compiled

/-- Instruction-local forms; these introduce only internal value-table entries. -/
def madd (a b c : Src) : Term :=
  .binary .add (.binary .mul (.source a) (.source b)) (.source c)

def low32 (a : Src) : Term := .binary .and (.source a) (.literal 0xffffffff#64)
def umaddl (a b c : Src) : Term := .binary .add (.binary .mul (low32 a) (low32 b)) (.source c)

def extr (shift : Nat) (high low : Src) : Term :=
  .binary .orr (.unary (.lsr shift) (.source low)) (.unary (.lsl (64-shift)) (.source high))

def condition (cc : BitVec 4) : Term := .flat ⟨.cond cc, [.flag 0,.flag 1,.flag 2,.flag 3]⟩
def csinv (cc : BitVec 4) (a b : Src) : Term :=
  .ternary .csel (condition cc) (.source a) (.unary .not (.source b))
def csneg (cc : BitVec 4) (a b : Src) : Term :=
  .ternary .csel (condition cc) (.source a) (.binary .sub (.literal 0#64) (.source b))
def bic (a b : Src) : Term := .binary .and (.source a) (.unary .not (.source b))

def addsShift (op : Op) (shift : Nat) (a b : Src) : Term :=
  .ternary op (.source a) (.unary (.lsl shift) (.source b)) (.literal 0#64)

theorem madd_eval (read : Src → BitVec 64) (a b c : Src) :
    eval read (madd a b c) = read a * read b + read c := rfl

theorem umaddl_eval (read : Src → BitVec 64) (a b c : Src) :
    eval read (umaddl a b c) = (read a &&& 0xffffffff#64) * (read b &&& 0xffffffff#64) + read c := rfl

theorem extr_eval (read : Src → BitVec 64) (shift : Nat) (high low : Src) :
    eval read (extr shift high low) = (read low >>> shift) ||| (read high <<< (64-shift)) := rfl

theorem csinv_eval (read : Src → BitVec 64) (cc : BitVec 4) (a b : Src) :
    eval read (csinv cc a b) =
      if b01 (condHolds cc (read (.flag 0)) (read (.flag 1)) (read (.flag 2)) (read (.flag 3))) ≠ 0#64
      then read a else ~~~(read b) := rfl

theorem csneg_eval (read : Src → BitVec 64) (cc : BitVec 4) (a b : Src) :
    eval read (csneg cc a b) =
      if b01 (condHolds cc (read (.flag 0)) (read (.flag 1)) (read (.flag 2)) (read (.flag 3))) ≠ 0#64
      then read a else 0#64 - read b := rfl

theorem bic_eval (read : Src → BitVec 64) (a b : Src) :
    eval read (bic a b) = read a &&& ~~~(read b) := rfl

theorem addsShift_eval (read : Src → BitVec 64) (op : Op) (shift : Nat) (a b : Src) :
    eval read (addsShift op shift a b) = op.eval [read a,read b <<< shift,0#64] := rfl

#print axioms compile_sound
#print axioms compile_physical
#print axioms madd_eval
#print axioms umaddl_eval
#print axioms extr_eval
#print axioms csinv_eval
#print axioms csneg_eval
#print axioms bic_eval
#print axioms addsShift_eval
end ArmCertValue.Expr
