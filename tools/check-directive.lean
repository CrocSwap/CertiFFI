import Lean
open Lean

/-!
Prints a canonical listing of every constant (private ones included) stored in each `.olean` given on the command line:
one line per constant, `name <TAB> kind <TAB> universe params <TAB> type hash <TAB> value hash`, sorted by name.
The hashes are Lean's structural `Expr.hash`, which does not depend on the build path or the Lake package name.
`tools/check-directive.sh` hashes each listing with SHA-256 and compares it with `tools/DIRECTIVE-MODULES.sha256`.
-/

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

unsafe def main (args : List String) : IO Unit := do
  for f in args do
    let (md, _) ← readModuleData f
    let lines := md.constants.map fun ci =>
      let v := match ci.value? (allowOpaque := true) with
        | some e => toString e.hash
        | none => "-"
      s!"{ci.name}\t{kindOf ci}\t{ci.levelParams}\t{ci.type.hash}\t{v}"
    for l in lines.qsort (· < ·) do
      IO.println l
