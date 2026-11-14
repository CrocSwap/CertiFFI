import Lean
open Lean Elab Command

namespace SurveyExport
structure ExportState where
  nodes : Array Json := #[]
  seen : Std.HashMap Expr Nat := {}
  errors : Array Json := #[]
  residuals : Array Json := #[]
  unknown : Array Json := #[]
  visits : Nat := 0
  okLeaves : Nat := 0
  truncated : Bool := false
  deriving Inhabited

abbrev ExportM := StateM ExportState

/-- Exact syntax DAG, including all binder/type/implicit-argument syntax. -/
partial def encode (e : Expr) : ExportM Nat := do
  if let some n := (← get).seen[e]? then return n
  if (← get).nodes.size ≥ 200000 then
    modify fun s => {s with truncated := true}
    return 0
  let fields ← match e with
    | .bvar n => pure [("tag",toJson "bvar"),("index",toJson n)]
    | .fvar id => pure [("tag",toJson "fvar"),("fvar_id",toJson id.name.toString)]
    | .mvar id => pure [("tag",toJson "mvar"),("mvar_id",toJson id.name.toString)]
    | .sort u => pure [("tag",toJson "sort"),("level",toJson (toString u))]
    | .const n us => pure [("tag",toJson "const"),("name",toJson n.toString),("levels",toJson (us.map toString))]
    | .app f a => do
      let f ← encode f; let a ← encode a
      pure [("tag",toJson "app"),("function",toJson f),("argument",toJson a)]
    | .lam n t b bi | .forallE n t b bi => do
      let t ← encode t; let b ← encode b
      pure [("tag",toJson (if e.isLambda then "lambda" else "forall")),("name",toJson n.toString),
        ("binder_info",toJson (reprStr bi)),("type",toJson t),("body",toJson b)]
    | .letE n t v b _ => do
      let t ← encode t; let v ← encode v; let b ← encode b
      pure [("tag",toJson "let"),("name",toJson n.toString),("type",toJson t),("value",toJson v),("body",toJson b)]
    | .lit (.natVal n) => pure [("tag",toJson "nat"),("value",toJson n)]
    | .lit (.strVal s) => pure [("tag",toJson "string"),("value",toJson s)]
    | .mdata _ b => do
      pure [("tag",toJson "metadata"),("body",toJson (← encode b))]
    | .proj n i b => do
      pure [("tag",toJson "projection"),("structure",toJson n.toString),("field",toJson i),("receiver",toJson (← encode b))]
  let id := (← get).nodes.size
  modify fun s => {s with nodes := s.nodes.push (Json.mkObj (("id",toJson id)::fields)),seen := s.seen.insert e id}
  return id

def guard (condition : Expr) (truth : Bool) (depth : Nat) (kind : String) : ExportM Json := do
  return Json.mkObj [("kind",toJson kind),("condition_node",toJson (← encode condition)),
    ("truth",toJson truth),("binder_depth",toJson depth)]

/-- Inspect the result spine only; error-like data inside an `ok` value is not an exit.
Opaque bind errors are explicitly delegated, with no translation credit. -/
partial def scanSpine (e : Expr) (conditions : Array Json) (depth : Nat) : ExportM Unit := do
  modify fun s => {s with visits := s.visits+1}
  if (← get).visits > 100000 then
    modify fun s => {s with unknown := s.unknown.push (Json.mkObj [("reason",toJson "result-spine visit budget exhausted")])}
    return
  match e with
  | .mdata _ b => return ← scanSpine b conditions depth
  | .lam _ _ b _ => return ← scanSpine b conditions (depth+1)
  | .letE _ _ v b _ => return ← scanSpine (b.instantiate1 v) conditions depth
  | _ => pure ()
  let e' := e.headBeta
  if e' != e then return ← scanSpine e' conditions depth
  let f := e.getAppFn
  let args := e.getAppArgs
  if f.isConstOf ``ite || f.isConstOf ``dite then
    if args.size == 5 then
      scanSpine args[3]! (conditions.push (← guard args[1]! true depth "proposition")) depth
      scanSpine args[4]! (conditions.push (← guard args[1]! false depth "proposition")) depth
      return
  if f.isConstOf ``Bool.rec && (args.size == 4 || args.size == 5) then
    scanSpine args[1]! (conditions.push (← guard args[3]! false depth "boolean")) depth
    scanSpine args[2]! (conditions.push (← guard args[3]! true depth "boolean")) depth
    return
  if f.isConstOf ``Bool.casesOn && args.size == 4 then
    scanSpine args[2]! (conditions.push (← guard args[1]! false depth "boolean")) depth
    scanSpine args[3]! (conditions.push (← guard args[1]! true depth "boolean")) depth
    return
  if f.isConstOf ``EStateM.Result.ok then
    modify fun s => {s with okLeaves := s.okLeaves+1}
    return
  if f.isConstOf ``EStateM.Result.error && args.size == 5 then
    let err := args[3]!
    let ctor := err.getAppFn.constName?.map Name.toString |>.getD "symbolic-error"
    let source := match err.getAppArgs.back? with
      | some (.lit (.strVal s)) => toJson s
      | _ => Json.null
    let row := Json.mkObj [("result_node",toJson (← encode e)),("error_node",toJson (← encode err)),
      ("state_node",toJson (← encode args[4]!)),("constructor",toJson ctor),
      ("assertion",toJson (ctor == "Sail.Error.Assertion")),("source_location_or_message",source),("conditions",Json.arr conditions),
      ("binder_depth",toJson depth),("feasibility",toJson "not established; structural native branch")]
    modify fun s => {s with errors := s.errors.push row}
    return
  if f.isConstOf ``EStateM.bind && args.size == 7 then
    let row := Json.mkObj [("bind_node",toJson (← encode e)),("callee_node",toJson (← encode args[4]!)),
      ("input_state_node",toJson (← encode args[6]!)),("conditions",Json.arr conditions),
      ("error_propagation",toJson "callee error/result state propagate unchanged"),
      ("callee_body_inspected_for_errors",toJson false),("translation_credit",toJson false)]
    modify fun s => {s with residuals := s.residuals.push row}
    let success := Json.mkObj [("kind",toJson "residual-bind-success"),("bind_node",toJson (← encode e)),("binder_depth",toJson depth)]
    scanSpine args[5]! (conditions.push success) depth
    return
  if f.isConstOf `StepRuntime.resume && args.size == 6 then
    let node ← encode e
    let row := Json.mkObj [("resume_node",toJson node),("opaque_result_node",toJson (← encode args[5]!)),
      ("conditions",Json.arr conditions),("error_propagation",toJson "opaque result error/state propagate unchanged"),
      ("callee_body_inspected_for_errors",toJson false),("translation_credit",toJson false)]
    modify fun s => {s with residuals := s.residuals.push row}
    let success := Json.mkObj [("kind",toJson "residual-resume-success"),("resume_node",toJson node),("binder_depth",toJson depth)]
    scanSpine args[4]! (conditions.push success) depth
    return
  let node ← encode e
  modify fun s => {s with unknown := s.unknown.push (Json.mkObj [("reason",toJson "unrecognized result spine"),
    ("node",toJson node),("head",toJson (f.constName?.map Name.toString |>.getD "nonconstant")),
    ("conditions",Json.arr conditions),("binder_depth",toJson depth)])}

syntax "export_native_errors " str " to " str : command
elab_rules : command
  | `(export_native_errors $name:str to $path:str) => do
      let n := (name.getString.splitOn ".").foldl Name.str Name.anonymous
      let ci ← getConstInfo n
      let some value := ci.value? | throwError "native declaration has no available value"
      let (root, initial) := (encode value).run {}
      let (_, state) := (scanSpine value #[] 0).run initial
      let report := Json.mkObj [("schema",toJson "armcert-native-errors-v1"),("declaration",toJson n.toString),
        ("native_root",toJson root),("nodes",Json.arr state.nodes),("errors",Json.arr state.errors),
        ("residual_binds",Json.arr state.residuals),("unrecognized",Json.arr state.unknown),
        ("instruction_result_spine_complete",toJson (state.unknown.isEmpty && !state.truncated)),
        ("dag_complete",toJson (!state.truncated)),("dag_node_budget",toJson (200000 : Nat)),
        ("opaque_callee_errors_complete",toJson state.residuals.isEmpty),
        ("ok_leaves",toJson state.okLeaves),("visits",toJson state.visits),
        ("normalization",toJson "head beta and let substitution only"),
        ("condition_encoding",toJson "exact Expr DAG; de Bruijn indices with per-guard binder depth; no truncated prettyprint"),
        ("reachability",toJson "syntactic native branches only; feasibility/architectural admissibility requires B2 review")]
      IO.FS.writeFile path.getString report.compress
      logInfo m!"native-errors error_leaves={state.errors.size} residual_binds={state.residuals.size} complete={state.unknown.isEmpty}"
end SurveyExport
