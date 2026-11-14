import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
namespace S2Frame
abbrev State := SequentialState Regs oracleChoiceSource
@[simp] theorem events_dite (p : Prop) [Decidable p] (a : p → State) (b : ¬p → State) :
    (dite p a b).events = dite p (fun h => (a h).events) (fun h => (b h).events) := by
  split <;> rfl
@[simp] theorem events_ite (p : Prop) [Decidable p] (a b : State) :
    (ite p a b).events = ite p a.events b.events := by split <;> rfl
@[simp] theorem regs_dite (p : Prop) [Decidable p] (a : p → State) (b : ¬p → State) :
    (dite p a b).regs = dite p (fun h => (a h).regs) (fun h => (b h).regs) := by
  split <;> rfl
@[simp] theorem choiceOcc_dite (p : Prop) [Decidable p] (a : p → State) (b : ¬p → State) :
    (dite p a b).choiceOcc = dite p (fun h => (a h).choiceOcc) (fun h => (b h).choiceOcc) := by
  split <;> rfl
@[simp] theorem choiceState_dite (p : Prop) [Decidable p] (a : p → State) (b : ¬p → State) :
    (dite p a b).choiceState = dite p (fun h => (a h).choiceState) (fun h => (b h).choiceState) := by
  split <;> rfl
@[simp] theorem mem_dite (p : Prop) [Decidable p] (a : p → State) (b : ¬p → State) :
    (dite p a b).mem = dite p (fun h => (a h).mem) (fun h => (b h).mem) := by
  split <;> rfl
@[simp] theorem regs_ite (p : Prop) [Decidable p] (a b : State) :
    (ite p a b).regs = ite p a.regs b.regs := by split <;> rfl
@[simp] theorem choiceOcc_ite (p : Prop) [Decidable p] (a b : State) :
    (ite p a b).choiceOcc = ite p a.choiceOcc b.choiceOcc := by split <;> rfl
@[simp] theorem choiceState_ite (p : Prop) [Decidable p] (a b : State) :
    (ite p a b).choiceState = ite p a.choiceState b.choiceState := by split <;> rfl
@[simp] theorem mem_ite (p : Prop) [Decidable p] (a b : State) :
    (ite p a b).mem = ite p a.mem b.mem := by split <;> rfl
end S2Frame
