import Lean
import CertiFFIClaim.Kinds

/-! `#print premises C`: like `#print axioms`, list every input of the headline theorem `C` by kind and registry id,
the universally quantified data, and the axioms of its closure. An unclassified hypothesis (a `Prop` binder that is not
`RunCheck` / `Premise` / `CallerContract` / `DeploymentObligation`) is an ERROR. The same walk backs the `certify`
extractor (`CertiFFI.Claim.Extract`). -/
namespace CertiFFI.Claim
open Lean Meta Elab Command

inductive InputKind where
  | runCheck | premise | callerContract | deploymentObligation
  deriving Repr, BEq, Inhabited

def InputKind.tag : InputKind → String
  | .runCheck => "RunCheck" | .premise => "Premise" | .callerContract => "CallerContract"
  | .deploymentObligation => "DeploymentObligation"

/-- One binder of the headline statement (types rendered inside the binder telescope). -/
inductive Binder where
  | input (name : Name) (kind : InputKind) (id : String) (grade : Option String) (prop : String)
  | quantified (name : Name) (type : String)
  | unclassified (name : Name) (prop : String)
  deriving Inhabited

private def strLit? : Expr → Option String
  | .lit (.strVal s) => some s
  | .mdata _ e => strLit? e
  | _ => none

/-- Classify a hypothesis type by its head kind structure (syntactic: the card must state the kind explicitly). -/
def classify? (t : Expr) : Option (InputKind × String × Option String × Expr) :=
  let t := t.consumeMData
  match t.getAppFn, t.getAppArgs with
  | .const n _, #[i, p] =>
    if n == ``RunCheck then (strLit? i).map (fun s => (.runCheck, s, none, p))
    else if n == ``CallerContract then (strLit? i).map (fun s => (.callerContract, s, none, p))
    else if n == ``DeploymentObligation then (strLit? i).map (fun s => (.deploymentObligation, s, none, p))
    else none
  | .const n _, #[i, g, p] =>
    if n == ``Premise then
      let gs := match g.consumeMData.getAppFn with | .const gn _ => some (gn.componentsRev.head!.toString) | _ => none
      (strLit? i).map (fun s => (.premise, s, gs, p))
    else none
  | _, _ => none

/-- Walk the binders of a constant's type. -/
def binders (c : Name) : MetaM (Array Binder) := do
  let some ci := (← getEnv).find? c | throwError "unknown constant {c}"
  forallTelescope ci.type fun xs _ => do
    let mut out := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      let ty ← instantiateMVars d.type
      let pp (e : Expr) : MetaM String := return toString (← ppExpr e)
      if ← isProp ty then
        match classify? ty with
        | some (k, i, g, p) => out := out.push (.input d.userName k i g (← pp p))
        | none => out := out.push (.unclassified d.userName (← pp ty))
      else out := out.push (.quantified d.userName (← pp ty))
    return out

syntax (name := printPremises) "#print " &"premises " ident : command

@[command_elab printPremises] def elabPrintPremises : CommandElab := fun stx => do
  let id := stx[2]
  let c ← liftCoreM <| realizeGlobalConstNoOverload id
  let bs ← liftTermElabM <| binders c
  let axs ← liftCoreM <| Lean.collectAxioms c
  let mut lines : Array String := #[s!"'{c}' inputs:"]
  let mut bad : Array String := #[]
  for b in bs do
    match b with
    | .input n k i g p =>
      lines := lines.push s!"  {k.tag} {i}{(g.map (fun s => s!" [{s}]")).getD ""}  ({n}) : {p}"
    | .quantified n t => lines := lines.push s!"  ∀ {n} : {t}"
    | .unclassified n p => bad := bad.push s!"  UNCLASSIFIED ({n}) : {p}"
  lines := lines.push s!"  axioms: {axs.toList}"
  logInfo (String.intercalate "\n" (lines ++ bad).toList)
  unless bad.isEmpty do
    logError s!"#print premises: {bad.size} unclassified hypothesis(es) in '{c}'"

end CertiFFI.Claim
