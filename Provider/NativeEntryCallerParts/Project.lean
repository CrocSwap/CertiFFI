import NativeEntryCallerParts.Bindings
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
namespace NativeEntryCallerParts
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option Elab.async false

theorem resultState_ok {α : Type} (value : α) (s : NativeState) :
    nativeResultState (.ok value s) = s := rfl
theorem resultState_error {α : Type} (err : Sail.Error exception) (s : NativeState) :
    nativeResultState (α := α) (.error err s) = s := rfl

theorem wordValue_ok (value : BitVec 64) (s : NativeState) :
    wordResultValue (.ok value s) = value := rfl
theorem wordValue_error (err : Sail.Error exception) (s : NativeState) :
    wordResultValue (.error err s) = 0#64 := rfl
theorem wordValue_ite (p : Prop) [Decidable p]
    (x y : EStateM.Result (Sail.Error exception) NativeState (BitVec 64)) :
    wordResultValue (if p then x else y) =
      (if p then wordResultValue x else wordResultValue y) := apply_ite _ p x y
theorem wordValue_dite (p : Prop) [Decidable p]
    (x : p → EStateM.Result (Sail.Error exception) NativeState (BitVec 64))
    (y : ¬p → EStateM.Result (Sail.Error exception) NativeState (BitVec 64)) :
    wordResultValue (dite p x y) =
      (dite p (fun h => wordResultValue (x h)) (fun h => wordResultValue (y h))) := apply_dite _ p x y

theorem state_regs_ite (p : Prop) [Decidable p] (x y : NativeState) :
    (if p then x else y).regs = (if p then x.regs else y.regs) :=
  apply_ite (fun s : NativeState => s.regs) p x y

theorem result_regs_ite {α : Type} (p : Prop) [Decidable p] (x y : EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (if p then x else y)).regs = (if p then (nativeResultState x).regs else (nativeResultState y).regs) :=
  apply_ite (fun r => (nativeResultState r).regs) p x y

theorem state_regs_dite (p : Prop) [Decidable p] (x : p → NativeState) (y : ¬p → NativeState) :
    (dite p x y).regs = (dite p (fun h => (x h).regs) (fun h => (y h).regs)) :=
  apply_dite (fun s : NativeState => s.regs) p x y

theorem result_regs_dite {α : Type} (p : Prop) [Decidable p] (x : p → EStateM.Result (Sail.Error exception) NativeState α) (y : ¬p → EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (dite p x y)).regs = (dite p (fun h => (nativeResultState (x h)).regs) (fun h => (nativeResultState (y h)).regs)) :=
  apply_dite (fun r => (nativeResultState r).regs) p x y

theorem state_mem_ite (p : Prop) [Decidable p] (x y : NativeState) :
    (if p then x else y).mem = (if p then x.mem else y.mem) :=
  apply_ite (fun s : NativeState => s.mem) p x y

theorem result_mem_ite {α : Type} (p : Prop) [Decidable p] (x y : EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (if p then x else y)).mem = (if p then (nativeResultState x).mem else (nativeResultState y).mem) :=
  apply_ite (fun r => (nativeResultState r).mem) p x y

theorem state_mem_dite (p : Prop) [Decidable p] (x : p → NativeState) (y : ¬p → NativeState) :
    (dite p x y).mem = (dite p (fun h => (x h).mem) (fun h => (y h).mem)) :=
  apply_dite (fun s : NativeState => s.mem) p x y

theorem result_mem_dite {α : Type} (p : Prop) [Decidable p] (x : p → EStateM.Result (Sail.Error exception) NativeState α) (y : ¬p → EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (dite p x y)).mem = (dite p (fun h => (nativeResultState (x h)).mem) (fun h => (nativeResultState (y h)).mem)) :=
  apply_dite (fun r => (nativeResultState r).mem) p x y

theorem state_events_ite (p : Prop) [Decidable p] (x y : NativeState) :
    (if p then x else y).events = (if p then x.events else y.events) :=
  apply_ite (fun s : NativeState => s.events) p x y

theorem result_events_ite {α : Type} (p : Prop) [Decidable p] (x y : EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (if p then x else y)).events = (if p then (nativeResultState x).events else (nativeResultState y).events) :=
  apply_ite (fun r => (nativeResultState r).events) p x y

theorem state_events_dite (p : Prop) [Decidable p] (x : p → NativeState) (y : ¬p → NativeState) :
    (dite p x y).events = (dite p (fun h => (x h).events) (fun h => (y h).events)) :=
  apply_dite (fun s : NativeState => s.events) p x y

theorem result_events_dite {α : Type} (p : Prop) [Decidable p] (x : p → EStateM.Result (Sail.Error exception) NativeState α) (y : ¬p → EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (dite p x y)).events = (dite p (fun h => (nativeResultState (x h)).events) (fun h => (nativeResultState (y h)).events)) :=
  apply_dite (fun r => (nativeResultState r).events) p x y

theorem state_tags_ite (p : Prop) [Decidable p] (x y : NativeState) :
    (if p then x else y).tags = (if p then x.tags else y.tags) :=
  apply_ite (fun s : NativeState => s.tags) p x y

theorem result_tags_ite {α : Type} (p : Prop) [Decidable p] (x y : EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (if p then x else y)).tags = (if p then (nativeResultState x).tags else (nativeResultState y).tags) :=
  apply_ite (fun r => (nativeResultState r).tags) p x y

theorem state_tags_dite (p : Prop) [Decidable p] (x : p → NativeState) (y : ¬p → NativeState) :
    (dite p x y).tags = (dite p (fun h => (x h).tags) (fun h => (y h).tags)) :=
  apply_dite (fun s : NativeState => s.tags) p x y

theorem result_tags_dite {α : Type} (p : Prop) [Decidable p] (x : p → EStateM.Result (Sail.Error exception) NativeState α) (y : ¬p → EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (dite p x y)).tags = (dite p (fun h => (nativeResultState (x h)).tags) (fun h => (nativeResultState (y h)).tags)) :=
  apply_dite (fun r => (nativeResultState r).tags) p x y

theorem state_cycleCount_ite (p : Prop) [Decidable p] (x y : NativeState) :
    (if p then x else y).cycleCount = (if p then x.cycleCount else y.cycleCount) :=
  apply_ite (fun s : NativeState => s.cycleCount) p x y

theorem result_cycleCount_ite {α : Type} (p : Prop) [Decidable p] (x y : EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (if p then x else y)).cycleCount = (if p then (nativeResultState x).cycleCount else (nativeResultState y).cycleCount) :=
  apply_ite (fun r => (nativeResultState r).cycleCount) p x y

theorem state_cycleCount_dite (p : Prop) [Decidable p] (x : p → NativeState) (y : ¬p → NativeState) :
    (dite p x y).cycleCount = (dite p (fun h => (x h).cycleCount) (fun h => (y h).cycleCount)) :=
  apply_dite (fun s : NativeState => s.cycleCount) p x y

theorem result_cycleCount_dite {α : Type} (p : Prop) [Decidable p] (x : p → EStateM.Result (Sail.Error exception) NativeState α) (y : ¬p → EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (dite p x y)).cycleCount = (dite p (fun h => (nativeResultState (x h)).cycleCount) (fun h => (nativeResultState (y h)).cycleCount)) :=
  apply_dite (fun r => (nativeResultState r).cycleCount) p x y

theorem state_sailOutput_ite (p : Prop) [Decidable p] (x y : NativeState) :
    (if p then x else y).sailOutput = (if p then x.sailOutput else y.sailOutput) :=
  apply_ite (fun s : NativeState => s.sailOutput) p x y

theorem result_sailOutput_ite {α : Type} (p : Prop) [Decidable p] (x y : EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (if p then x else y)).sailOutput = (if p then (nativeResultState x).sailOutput else (nativeResultState y).sailOutput) :=
  apply_ite (fun r => (nativeResultState r).sailOutput) p x y

theorem state_sailOutput_dite (p : Prop) [Decidable p] (x : p → NativeState) (y : ¬p → NativeState) :
    (dite p x y).sailOutput = (dite p (fun h => (x h).sailOutput) (fun h => (y h).sailOutput)) :=
  apply_dite (fun s : NativeState => s.sailOutput) p x y

theorem result_sailOutput_dite {α : Type} (p : Prop) [Decidable p] (x : p → EStateM.Result (Sail.Error exception) NativeState α) (y : ¬p → EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (dite p x y)).sailOutput = (dite p (fun h => (nativeResultState (x h)).sailOutput) (fun h => (nativeResultState (y h)).sailOutput)) :=
  apply_dite (fun r => (nativeResultState r).sailOutput) p x y

theorem state_choiceState_ite (p : Prop) [Decidable p] (x y : NativeState) :
    (if p then x else y).choiceState = (if p then x.choiceState else y.choiceState) :=
  apply_ite (fun s : NativeState => s.choiceState) p x y

theorem result_choiceState_ite {α : Type} (p : Prop) [Decidable p] (x y : EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (if p then x else y)).choiceState = (if p then (nativeResultState x).choiceState else (nativeResultState y).choiceState) :=
  apply_ite (fun r => (nativeResultState r).choiceState) p x y

theorem state_choiceState_dite (p : Prop) [Decidable p] (x : p → NativeState) (y : ¬p → NativeState) :
    (dite p x y).choiceState = (dite p (fun h => (x h).choiceState) (fun h => (y h).choiceState)) :=
  apply_dite (fun s : NativeState => s.choiceState) p x y

theorem result_choiceState_dite {α : Type} (p : Prop) [Decidable p] (x : p → EStateM.Result (Sail.Error exception) NativeState α) (y : ¬p → EStateM.Result (Sail.Error exception) NativeState α) :
    (nativeResultState (dite p x y)).choiceState = (dite p (fun h => (nativeResultState (x h)).choiceState) (fun h => (nativeResultState (y h)).choiceState)) :=
  apply_dite (fun r => (nativeResultState r).choiceState) p x y

#print axioms resultState_ok
#print axioms resultState_error
#print axioms wordValue_ok
#print axioms wordValue_error
#print axioms wordValue_ite
#print axioms wordValue_dite
#print axioms state_regs_ite
#print axioms result_regs_ite
#print axioms state_regs_dite
#print axioms result_regs_dite
#print axioms state_mem_ite
#print axioms result_mem_ite
#print axioms state_mem_dite
#print axioms result_mem_dite
#print axioms state_events_ite
#print axioms result_events_ite
#print axioms state_events_dite
#print axioms result_events_dite
#print axioms state_tags_ite
#print axioms result_tags_ite
#print axioms state_tags_dite
#print axioms result_tags_dite
#print axioms state_cycleCount_ite
#print axioms result_cycleCount_ite
#print axioms state_cycleCount_dite
#print axioms result_cycleCount_dite
#print axioms state_sailOutput_ite
#print axioms result_sailOutput_ite
#print axioms state_sailOutput_dite
#print axioms result_sailOutput_dite
#print axioms state_choiceState_ite
#print axioms result_choiceState_ite
#print axioms state_choiceState_dite
#print axioms result_choiceState_dite
end NativeEntryCallerParts
