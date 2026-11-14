import Init

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024

namespace ReleaseProfile.MachineSource

/-- Classification of an authority reference, not a proof of physical authority. -/
inductive AuthorityKind where
  | rawTrm
  | conditionalTrm
  | osReadback
  | modelDefinition
  | ratifiedControl
  deriving DecidableEq, Repr

/-- An acquisition/claim key must later be joined to scoped physical evidence. -/
structure AuthorityRef where
  key : String
  kind : AuthorityKind
  deriving DecidableEq, Repr

/-- Finite recipe data. There is no callback, state initializer or fallback value. -/
inductive Slot (valueType : Type) where
  | literal (value : valueType) (authority : AuthorityRef)
  | unresolved (symbolKey : String)
  | caller (slotKey : String)

namespace Slot

def isUnknown {valueType : Type} : Slot valueType → Bool
  | .unresolved _ => true
  | _ => false

def isCaller {valueType : Type} : Slot valueType → Bool
  | .caller _ => true
  | _ => false

end Slot

variable {coordinate : Type} {Value : coordinate → Type}

/-- Only unresolved coordinates have an unknown input; declared values cannot be overridden. -/
abbrev UnknownValues (recipe : (c : coordinate) → Slot (Value c)) :=
  (c : coordinate) → Slot.isUnknown (recipe c) = true → Value c

/-- Caller slots are separate, outer entry parameters, never model-witness choices. -/
abbrev CallerValues (recipe : (c : coordinate) → Slot (Value c)) :=
  (c : coordinate) → Slot.isCaller (recipe c) = true → Value c

#check "CURRENT_DECL Recipe.interpret"
def interpret (recipe : (c : coordinate) → Slot (Value c))
    (unknowns : UnknownValues recipe) (caller : CallerValues recipe)
    (c : coordinate) : Value c :=
  match h : recipe c with
  | .literal value _ => value
  | .unresolved _ => unknowns c (by rw [h]; rfl)
  | .caller _ => caller c (by rw [h]; rfl)

theorem interpret_literal (recipe : (c : coordinate) → Slot (Value c))
    (unknowns : UnknownValues recipe) (caller : CallerValues recipe)
    (c : coordinate) (value : Value c) (authority : AuthorityRef)
    (declared : recipe c = .literal value authority) :
    interpret recipe unknowns caller c = value := by
  unfold interpret
  split <;> try simp_all <;> rfl

theorem interpret_unknown (recipe : (c : coordinate) → Slot (Value c))
    (unknowns : UnknownValues recipe) (caller : CallerValues recipe)
    (c : coordinate) (symbolKey : String)
    (unresolved : recipe c = .unresolved symbolKey) :
    interpret recipe unknowns caller c =
      unknowns c (by rw [unresolved]; rfl) := by
  unfold interpret
  split
  · rename_i value authority branch
    cases branch.symm.trans unresolved
  · rfl
  · rename_i slotKey branch
    cases branch.symm.trans unresolved

theorem interpret_caller (recipe : (c : coordinate) → Slot (Value c))
    (unknowns : UnknownValues recipe) (caller : CallerValues recipe)
    (c : coordinate) (slotKey : String)
    (entrySlot : recipe c = .caller slotKey) :
    interpret recipe unknowns caller c =
      caller c (by rw [entrySlot]; rfl) := by
  unfold interpret
  split
  · rename_i value authority branch
    cases branch.symm.trans entrySlot
  · rename_i symbolKey branch
    cases branch.symm.trans entrySlot
  · rfl

end ReleaseProfile.MachineSource

#print axioms ReleaseProfile.MachineSource.interpret_literal
#print axioms ReleaseProfile.MachineSource.interpret_unknown
#print axioms ReleaseProfile.MachineSource.interpret_caller
