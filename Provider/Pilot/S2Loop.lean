import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S2Loop
abbrev State := SequentialState Regs oracleChoiceSource

/- A finite execution certificate for the source repeat-until combinator.
   Returned architectural faults use SailME's early return, not a Sail error. -/
inductive Trace {α R : Type} (test : α → Bool) (body : α → SailME R α) :
    Nat → α → State → Except (Sail.Error exception ⊕ R) α → State → Prop where
  | done {x y s t}
      (step : body x s = .ok (.ok y) t) (stop : test y = true) :
      Trace test body 1 x s (.ok y) t
  | returned {x s t r}
      (step : body x s = .ok (.error (.inr r)) t) :
      Trace test body 1 x s (.error (.inr r)) t
  | next {x y s t n result u}
      (step : body x s = .ok (.ok y) t) (again : test y = false)
      (rest : Trace test body n y t result u) :
      Trace test body (n + 1) x s result u

theorem execute {α R : Type} {test : α → Bool} {body : α → SailME R α}
    {n : Nat} {x : α} {s : State} {result : Except (Sail.Error exception ⊕ R) α}
    {t : State} (h : Trace test body n x s result t)
    (fuel : Nat) (enough : n ≤ fuel) :
    sailUntilFuelM (m := SailME R) fuel (fun y => pure (test y)) x body s =
      .ok result t := by
  induction h generalizing fuel with
  | done step stop =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [sailUntilFuelM, Bind.bind, Pure.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
        EStateM.bind, EStateM.pure, step, stop]
  | returned step =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [sailUntilFuelM, Bind.bind, Pure.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        EStateM.bind, EStateM.pure, step]
  | next step again rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hf := Nat.le_of_succ_le_succ enough
      simpa [sailUntilFuelM, Bind.bind, Pure.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
        EStateM.bind, EStateM.pure, step, again] using ih fuel hf

#print axioms execute
end S2Loop
