import Lean

open Lean Meta Elab Term

-- Extract a compiled result type without re-elaborating large state projections.
-- Every remaining argument must be a proof and the result must be independent
-- of those proofs. The resulting expression is still checked by Lean's kernel.
elab "proof_result% " fn:term : term => do
  let value ← elabTerm fn none
  let type ← inferType value
  forallTelescope type fun proofs result => do
    let result ← instantiateMVars result
    for proof in proofs do
      unless ← isProp (← inferType proof) do
        throwError "proof_result% requires every data argument to be supplied"
      if result.containsFVar proof.fvarId! then
        throwError "proof_result% cannot erase a proof-dependent result"
    unless ← isProp result do
      throwError "proof_result% requires a proposition result"
    return result
