import Lean
import Pilot.StepRuntime
import Lean.Util.ShareCommon
open Lean Meta
namespace Stepping.FiniteControl

structure Result (σ : Type) where
  expr : Expr
  proof : Expr
  state : σ

/-- Closed, kernel-reduced cover; the width limit is a search budget only. -/
def cover (width : Nat) : MetaM (Array Expr × Expr × Expr) := do
  let values := (List.range (2 ^ width)).toArray.map fun n =>
    mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit width) (mkNatLit n)
  let ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit width)
  let proposition ← withLocalDeclD `finiteControl ty fun control => do
    let mut p ← mkEq control values.back!
    for n in (List.range (values.size - 1)).reverse do
      p := mkApp2 (Lean.mkConst ``Or) (← mkEq control values[n]!) p
    mkForallFVars #[control] p
  return (values, proposition, ← mkDecideProof proposition)

/-- Select only small controls actually used by the normalized frontier. -/
def choose (frontier : Expr) (maxWidth : Nat := 4) (excluded : Array Expr := #[]) : MetaM (Option (Expr × Nat)) := do
  let mut chosen : Option (Expr × Nat) := none
  for id in (collectFVars {} frontier).fvarSet.toList do
    let value := mkFVar id
    if excluded.contains value then continue
    let ty ← inferType value
    unless ty.isAppOfArity ``BitVec 1 do continue
    let some width ← getNatValue? ty.appArg! | continue
    if width == 0 || width > maxWidth then continue
    if let some (_, previous) := chosen then
      if previous ≤ width then continue
    chosen := some (value,width)
  return chosen

/-- The callback evaluates under all supplied local facts and returns its state. -/
partial def branches {σ : Type}
    (eval : Expr → Array Expr → σ → MetaM (Result σ))
    (e control : Expr) (values : Array Expr) (index : Nat)
    (casesProof : Expr) (facts : Array Expr) (state : σ) : MetaM (Result σ) := do
  if index ≥ values.size then throwError "finite control cover exhausted"
  if index + 1 == values.size then return ← eval e (facts.push casesProof) state
  let condition ← mkEq control values[index]!
  let mut natives := #[]
  let mut proofs := #[]
  let mut nextState := state
  for branch in [0:2] do
    let hypothesis := if branch == 0 then condition else mkNot condition
    let ((native,proof), resultState) ← withLocalDeclD `finiteBranch hypothesis fun h => do
      let result ← if branch == 0 then eval e (facts.push h) nextState else do
        let remaining ← mkAppM ``Or.resolve_left #[casesProof,h]
        branches eval e control values (index+1) remaining (facts.push h) nextState
      let (native,proof) := ShareCommon.shareCommon (result.expr,result.proof)
      pure ((← mkLambdaFVars #[h] native, ← mkLambdaFVars #[h] proof),result.state)
    nextState := resultState
    natives := natives.push native
    proofs := proofs.push proof
  let proof ← mkAppM ``StepRuntime.split_control
    #[condition,e,natives[0]!,natives[1]!,proofs[0]!,proofs[1]!]
  let some (_,lhs,out) := (← inferType proof).consumeMData.eq? | throwError "finite split is not an equation"
  unless ← isDefEq lhs e do throwError "finite split does not start at its input"
  let left := natives[0]!.bindingBody!
  let right := natives[1]!.bindingBody!
  let dec ← synthInstance (mkApp (Lean.mkConst ``Decidable) condition)
  if !left.hasLooseBVars && !right.hasLooseBVars && left == right then
    let merge := mkAppN (Lean.mkConst ``StepRuntime.merge_dite)
      #[← inferType left,condition,dec,left]
    return ⟨left,← mkEqTrans proof merge,nextState⟩
  let la := left.getAppArgs
  let ra := right.getAppArgs
  if left.getAppFn.isConstOf ``EStateM.Result.ok && right.getAppFn.isConstOf ``EStateM.Result.ok &&
      la.size == 5 && ra.size == 5 then
    let .lam ln lt _ li := natives[0]! | unreachable!
    let .lam rn rt _ ri := natives[1]! | unreachable!
    let inputs := #[la[0]!,la[1]!,la[2]!,condition,dec,
      Expr.lam ln lt la[3]! li,Expr.lam rn rt ra[3]! ri]
    let sameState := !la[4]!.hasLooseBVars && la[4]! == ra[4]!
    let factor := if sameState then
        mkAppN (Lean.mkConst ``StepRuntime.factor_ok_dite) (inputs.push la[4]!)
      else mkAppN (Lean.mkConst ``StepRuntime.factor_ok_states_dite)
        (inputs ++ #[Expr.lam ln lt la[4]! li,Expr.lam rn rt ra[4]! ri])
    let value := mkAppN (Lean.mkConst ``dite [← getLevel la[2]!])
      #[la[2]!,condition,dec,inputs[5]!,inputs[6]!]
    let stateLevel ← getLevel la[1]!
    let outputState := if sameState then la[4]! else
      mkAppN (Lean.mkConst ``dite [stateLevel])
        #[la[1]!,condition,dec,Expr.lam ln lt la[4]! li,Expr.lam rn rt ra[4]! ri]
    let factored := mkAppN left.getAppFn #[la[0]!,la[1]!,la[2]!,value,outputState]
    let resultType := mkAppN (Lean.mkConst ``EStateM.Result left.getAppFn.constLevels!)
      #[la[0]!,la[1]!,la[2]!]
    let combined := mkAppN (Lean.mkConst ``Eq.trans [← getLevel resultType])
      #[resultType,e,out,factored,proof,factor]
    return ⟨factored,combined,nextState⟩
  return ⟨out,proof,nextState⟩
end Stepping.FiniteControl
