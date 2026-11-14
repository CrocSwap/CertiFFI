import CryptoBridge.AddSubImmCore
import Bridge.StepM
import BridgeV2.BoundaryV2
open Lean Meta Elab Tactic
open ArmFull.Functions
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoBridge.LogImmCoreLNSym.
namespace CryptoBridge.LogImmCore

/-- `replace_closed_bv64 v`: find the largest closed subterm of the goal of type `BitVec 64` that
mentions `HighestSetBit` (the root's inlined DecodeBitMasks), prove it equal to the literal `v` by
kernel `decide`, and rewrite with that equation. Nothing is trusted: the equation is kernel-checked. -/
elab "replace_closed_bv64 " v:term : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let mut best : Option Expr := none
  let mut bestSize := 0
  let cands ← (do
    let r ← IO.mkRef (#[] : Array Expr)
    t.forEachWhere (fun e => !e.hasLooseBVars && !e.hasFVar && !e.hasMVar &&
        (e.find? (fun c => c.isConstOf ``ArmFull.Functions.HighestSetBit)).isSome)
      (fun e => r.modify (·.push e))
    r.get)
  for e in cands do
    let ty ← instantiateMVars (← inferType e)
    if ty == bv64 then
      let sz := e.approxDepth.toNat
      if best.isNone || sz > bestSize then
        best := some e; bestSize := sz
  let some e := best | throwError "replace_closed_bv64: no closed BitVec 64 subterm mentions HighestSetBit"
  let lit ← Term.elabTerm v (some bv64)
  let eqTy ← mkEq e lit
  let pf ← mkFreshExprMVar eqTy
  let gs ← Elab.Tactic.run pf.mvarId! (evalTactic (← `(tactic| decide +kernel)))
  unless gs.isEmpty do throwError "replace_closed_bv64: decide left goals"
  let pf ← instantiateMVars pf
  -- structural (pointer/==) replacement of e by a fresh variable, then congrArg: no defeq search
  let motive ← withLocalDeclD `z bv64 fun z => do
    let tz := t.replace fun x => if x == e then some z else none
    mkLambdaFVars #[z] tz
  let newT := (mkApp motive lit).headBeta
  let g' ← g.replaceTargetEq newT (← mkCongrArg motive pf)
  replaceMainGoal [g']

/-! Closed evaluations of LNSym's decode_bit_masks at the heap's bitmask encodings (armcert-crypto).
`highest_set_bit.go` is well-founded, so its equation is unfolded once (immN = 1 sets bit 6). -/

/-- `decide_closed_conds`: for every closed proposition `c` used as the condition of an `ite`/`dite` in
the goal, prove `c` or `¬ c` by kernel `decide` and simplify the branch away (eq_true / eq_false).
Kernel-checked; used for the roots' inlined DecodeBitMasks legality tests at literal encodings. -/
elab "decide_closed_conds" : tactic => withMainContext do
  let doneRef ← IO.mkRef (#[] : Array Expr)
  for _ in [0:12] do
    let t ← instantiateMVars (← getMainTarget)
    let r ← IO.mkRef (#[] : Array Expr)
    t.forEachWhere (fun e => (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) &&
        let c := e.getArg! 1; !c.hasLooseBVars && !c.hasFVar && !c.hasMVar)
      (fun e => r.modify (·.push (e.getArg! 1)))
    let done ← doneRef.get
    let conds := (← r.get).foldl (fun acc c => if acc.contains c || done.contains c then acc else acc.push c) #[]
    if conds.isEmpty then return
    doneRef.modify (· ++ conds)
    let mut lemmas : Array Name := #[]
    for c in conds do
      let cS ← PrettyPrinter.delab c
      let pfT ← mkFreshExprMVar (some c)
      let ok ← (do let gs ← Elab.Tactic.run pfT.mvarId! (evalTactic (← `(tactic| decide +kernel))); pure gs.isEmpty)
        <|> pure false
      if ok then
        let h ← mkFreshUserName `hcT
        let pf ← instantiateMVars pfT
        let g ← getMainGoal
        let (_, g') ← (← g.assert h (← mkEq c (mkConst ``True)) (← mkAppM ``eq_true #[pf])).intro1P
        replaceMainGoal [g']
        lemmas := lemmas.push h
      else
        let nc := mkNot c
        let pfF ← mkFreshExprMVar (some nc)
        let gs ← Elab.Tactic.run pfF.mvarId! (evalTactic (← `(tactic| decide +kernel)))
        unless gs.isEmpty do throwError "decide_closed_conds: cannot decide {cS}"
        let h ← mkFreshUserName `hcF
        let pf ← instantiateMVars pfF
        let g ← getMainGoal
        let (_, g') ← (← g.assert h (← mkEq c (mkConst ``False)) (← mkAppM ``eq_false #[pf])).intro1P
        replaceMainGoal [g']
        lemmas := lemmas.push h
    for h in lemmas do
      withMainContext do
        let hi := mkIdent h
        evalTactic (← `(tactic| try simp only [$hi:ident, dite_true, dite_false, ite_true, ite_false]))

/-- `reduce_closed_matchers`: replace every closed matcher application in the goal (e.g. the roots'
`match opc with ...` at a literal opc) by its weak-head normal form, via `congrArg` on `Eq.refl` (the
kernel re-checks the definitional equality). -/
elab "reduce_closed_matchers" : tactic => withMainContext do
  for _ in [0:8] do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let r ← IO.mkRef (#[] : Array Expr)
    t.forEachWhere (fun e => !e.hasLooseBVars && !e.hasFVar && !e.hasMVar && e.isApp) (fun e => r.modify (·.push e))
    let mut found : Option Expr := none
    for e in (← r.get) do
      if (← Meta.isMatcherApp e) then
        found := some e
        break
    let some e := found | return
    let v ← withTransparency .all <| whnf e
    if v == e then return
    let ty ← inferType e
    let motive ← withLocalDeclD `z ty fun z => do
      mkLambdaFVars #[z] (t.replace fun x => if x == e then some z else none)
    let pf ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e v)
    let newT := (mkApp motive v).headBeta
    replaceMainGoal [← g.replaceTargetEq newT (← mkCongrArg motive pf)]

/-- The native HighestSetBit at the heap's encodings (immN = 1), kernel-evaluated. -/
theorem nhsb_125 : ArmFull.Functions.HighestSetBit (125#7) = 6 := by decide +kernel

theorem nhsb_127 : ArmFull.Functions.HighestSetBit (127#7) = 6 := by decide +kernel

/-! Logical-op flags: the roots build PSTATE.<N,Z,C,V> as extractLsb of `(N ++ Z) ++ '00'`. -/
section

private abbrev cat4 (a b : BitVec 1) : BitVec (1 + 1 + 2) :=
  @HAppend.hAppend (BitVec (1 + 1)) (BitVec 2) (BitVec (1 + 1 + 2)) (@BitVec.instHAppendHAddNat (1 + 1) 2)
    (@HAppend.hAppend (BitVec 1) (BitVec 1) (BitVec (1 + 1)) (@BitVec.instHAppendHAddNat 1 1) a b) 0#2

theorem nzcv_n (a b : BitVec 1) : Sail.BitVec.extractLsb (cat4 a b) 3 3 = a := by
  rcases ArmBridge.Awc.bv1 a with rfl | rfl <;> rcases ArmBridge.Awc.bv1 b with rfl | rfl <;> decide

theorem nzcv_z (a b : BitVec 1) : Sail.BitVec.extractLsb (cat4 a b) 2 2 = b := by
  rcases ArmBridge.Awc.bv1 a with rfl | rfl <;> rcases ArmBridge.Awc.bv1 b with rfl | rfl <;> decide

theorem nzcv_c (a b : BitVec 1) : Sail.BitVec.extractLsb (cat4 a b) 1 1 = 0#1 := by
  rcases ArmBridge.Awc.bv1 a with rfl | rfl <;> rcases ArmBridge.Awc.bv1 b with rfl | rfl <;> decide

theorem nzcv_v (a b : BitVec 1) : Sail.BitVec.extractLsb (cat4 a b) 0 0 = 0#1 := by
  rcases ArmBridge.Awc.bv1 a with rfl | rfl <;> rcases ArmBridge.Awc.bv1 b with rfl | rfl <;> decide

theorem n7N (y : BitVec 64) (k : Nat) (hk : k = 63) :
    BitVec.setWidth 1 (Sail.BitVec.join1 [Sail.BitVec.access (y &&& 7#64) k]) = 0#1 := by
  subst hk
  rw [show Sail.BitVec.access (y &&& 7#64) 63 = 0#1 by unfold Sail.BitVec.access; simp [getElem!_def]]
  rfl

end

/-- Close one logical-op flag field (N/Z/C/V) of the projected PSTATE. -/
macro "logflag_field" : tactic => `(tactic|
  ((try simp only [nzcv_n, nzcv_z, nzcv_c, nzcv_v, DPI.update_logical_imm_pstate, make_pstate, isZeroBit_eq, n7L]) <;>
   first | rfl | exact (n7N _ _ (by decide)).symm | exact n7N _ _ (by decide)))

end CryptoBridge.LogImmCore

