module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Eqns

@[expose] public section

/- Generalized from the Ed25519 customer small-step interface. -/
/- ISA-neutral deterministic small-step interface. Instances supply actual
   instruction fetching/decoding; the runner never accepts a chosen schedule. -/
namespace CertiFFI.Leakage

structure Machine (State Observation : Type) where
  step : State → Option (State × Observation)

/-- Exact finite execution: unsupported steps fail, rather than manufacture an
    observation or successful response. A zero-step run preserves its input. -/
def run {State Observation : Type} (machine : Machine State Observation) :
    Nat → State → Option (State × List Observation)
  | 0, initial => some (initial, [])
  | fuel+1, initial => do
      let (next, observation) ← machine.step initial
      let (final, observations) ← run machine fuel next
      pure (final, observation :: observations)

-- Generate `run`'s equation and unfolding lemmas in their defining module.
-- Realizing them lazily in independent consumers (e.g. Leakage.AArch64 and
-- Leakage.Composition) serializes the same global name `run.eq_def` twice,
-- which the lean-buildtools gate rejects as an ambiguous declaration.
run_cmd do
  discard <| Lean.Elab.Command.liftTermElabM do
    discard <| Lean.Meta.getEqnsFor? ``run
    discard <| Lean.Meta.getUnfoldEqnFor? ``run (nonRec := true)

/-- Execute to the first explicit return boundary. Larger budgets do not execute
    caller code after a return, and exhaustion is distinguishable from success. -/
def runUntil {State Observation : Type} (machine : Machine State Observation)
    (stop : State → Bool) : Nat → State → Option (State × List Observation)
  | 0, initial => if stop initial then some (initial, []) else none
  | fuel+1, initial =>
      if stop initial then some (initial, []) else do
        let (next, observation) ← machine.step initial
        let (final, observations) ← runUntil machine stop fuel next
        pure (final, observation :: observations)

-- eval addition (agreed with, to land on main): runUntil eqns in the defining module.
run_cmd do
  discard <| Lean.Elab.Command.liftTermElabM do
    discard <| Lean.Meta.getEqnsFor? ``runUntil
    discard <| Lean.Meta.getUnfoldEqnFor? ``runUntil (nonRec := true)

end CertiFFI.Leakage
