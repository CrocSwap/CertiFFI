import Bridge.ModelStep
import Std.Data.ExtHashMap.Lemmas

open Sail Sail.ConcurrencyInterfaceV1 ArmFull
namespace NativeSourceInit
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false

abbrev NativeState := SequentialState Regs oracleChoiceSource
abbrev RAM := Std.ExtHashMap Nat (BitVec 8)
abbrev PhysicalByte := Nat × BitVec 8
abbrev Plan := List PhysicalByte

/- Source initialization of the ACTUAL native RAM field, not an ISA/runtime
memory evaluator. Addresses are Nat; neither PA0 nor any arbitrary outside RAM
is excluded. The source/mapping producer must supply the actual physical plan. -/
def materialize : Plan → RAM → RAM
  | [], ram => ram
  | row :: rest, ram => (materialize rest ram).insert row.1 row.2

def initState (plan : Plan) (state : NativeState) : NativeState :=
  { state with mem := materialize plan state.mem }

def Consistent (plan : Plan) : Prop :=
  ∀ a ∈ plan, ∀ b ∈ plan, a.1 = b.1 → a.2 = b.2

def Satisfies (plan : Plan) (ram : RAM) : Prop :=
  ∀ row ∈ plan, ram[row.1]? = some row.2

theorem consistent_tail (head : PhysicalByte) (tail : Plan) (h : Consistent (head :: tail)) :
    Consistent tail := by
  intro a ha b hb eq
  exact h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) eq

/- Repeated physical aliases are retained. Agreement, rather than separation,
lets the constructor satisfy every original byte constraint at that address. -/
theorem materialize_satisfies (plan : Plan) (ram : RAM) (h : Consistent plan) :
    Satisfies plan (materialize plan ram) := by
  induction plan with
  | nil => simp [Satisfies]
  | cons head tail ih =>
    intro row member
    rcases List.mem_cons.mp member with eq | member
    · subst row
      simp [materialize]
    · have old := ih (consistent_tail head tail h) row member
      by_cases alias : head.1 = row.1
      · have same : head.2 = row.2 := h head (by simp) row (by simp [member]) alias
        simp [materialize, alias, same]
      · simpa [materialize, Std.ExtHashMap.getElem?_insert, alias] using old

theorem materialize_outside (plan : Plan) (ram : RAM) (pa : Nat)
    (outside : ∀ row ∈ plan, row.1 ≠ pa) :
    (materialize plan ram)[pa]? = ram[pa]? := by
  induction plan with
  | nil => rfl
  | cons head tail ih =>
    have different := outside head (by simp)
    have rest : ∀ row ∈ tail, row.1 ≠ pa := fun row member => outside row (by simp [member])
    simpa [materialize, Std.ExtHashMap.getElem?_insert, different] using ih rest

theorem consistent_of_satisfies (plan : Plan) (ram : RAM) (h : Satisfies plan ram) :
    Consistent plan := by
  intro a ha b hb eq
  have left := h a ha
  have right := h b hb
  rw [eq] at left
  exact Option.some.inj (left.symm.trans right)

/- Coverage/reconstruction ingredient: an already satisfying actual RAM is
returned EXACTLY, with arbitrary outside RAM retained. No source-domain case is
discarded and no None/default/zero premise is used. -/
theorem materialize_reconstruct (plan : Plan) (ram : RAM) (h : Satisfies plan ram) :
    materialize plan ram = ram := by
  induction plan with
  | nil => rfl
  | cons head tail ih =>
    have rest : Satisfies tail ram := fun row member => h row (by simp [member])
    have same := h head (by simp)
    change (materialize tail ram).insert head.1 head.2 = ram
    rw [ih rest]
    apply Std.ExtHashMap.ext_getElem?
    intro pa
    by_cases alias : head.1 = pa
    · subst pa
      simpa using same.symm
    · simp [Std.ExtHashMap.getElem?_insert, alias]

theorem initState_satisfies (plan : Plan) (state : NativeState) (h : Consistent plan) :
    Satisfies plan (initState plan state).mem := materialize_satisfies plan state.mem h

theorem initState_outside (plan : Plan) (state : NativeState) (pa : Nat)
    (outside : ∀ row ∈ plan, row.1 ≠ pa) :
    (initState plan state).mem[pa]? = state.mem[pa]? := materialize_outside plan state.mem pa outside

/- Literal connection to the model's existing byte insertion primitive. This
is source initialization; no architectural access/translation result follows. -/
theorem singleton_writeByte (state : NativeState) (row : PhysicalByte) :
    (Sail.ConcurrencyInterfaceV1.PreSail.writeByte row.1 row.2 : ArmFull.SailM PUnit) state =
      .ok ⟨⟩ (initState [row] state) := rfl

theorem initState_reconstruct (plan : Plan) (state : NativeState)
    (h : Satisfies plan state.mem) : initState plan state = state := by
  unfold initState
  rw [materialize_reconstruct plan state.mem h]

theorem initState_frame (plan : Plan) (state : NativeState) :
    (initState plan state).regs = state.regs ∧
    (initState plan state).choiceState = state.choiceState ∧
    (initState plan state).choiceOcc = state.choiceOcc ∧
    (initState plan state).tags = state.tags ∧
    (initState plan state).cycleCount = state.cycleCount ∧
    (initState plan state).sailOutput = state.sailOutput ∧
    (initState plan state).events = state.events := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms materialize_satisfies
#print axioms materialize_outside
#print axioms consistent_of_satisfies
#print axioms materialize_reconstruct
#print axioms initState_satisfies
#print axioms initState_outside
#print axioms singleton_writeByte
#print axioms initState_reconstruct
#print axioms initState_frame
end NativeSourceInit
