import Walk.S1LeafNormal
import Walk.S1NormalPost
import Pilot.S1DecodeFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open Lean Meta Elab Tactic
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1LeafShape
open S1Normality

theorem leaf_levels (d : BitVec 64) (level : Int)
    (hLeaf : S1DecodeFacts.classify d level = .DescriptorType_Leaf) :
    level = 1 ∨ level = 2 ∨ level = 3 := by
  by_cases h : level = 1 ∨ level = 2 ∨ level = 3
  · exact h
  · have h1 : level ≠ 1 := fun e => h (Or.inl e)
    have h2 : level ≠ 2 := fun e => h (Or.inr (Or.inl e))
    have h3 : level ≠ 3 := fun e => h (Or.inr (Or.inr e))
    by_cases hb0 : S1DecodeFacts.bit d 0 = 0#1 <;>
      by_cases hb1 : S1DecodeFacts.bit d 1 = 1#1 <;>
      simp [S1DecodeFacts.classify, h1, h2, h3, hb0, hb1] at hLeaf

def Shape (wp : S1TTWParams) (current : TTWState) (d : BitVec 64) (next : TTWState) : Prop :=
  next.istable = false ∧ next.level = current.level ∧
  next.baseaddress.address = S1LeafBaseFrame.base d current.level ∧
  next.baseaddress.paspace = .PAS_NonSecure ∧
  next.contiguous = (if ((wp.pnch == 1#1) || (current.disch == 1#1)) then
    0#1 else S1Contiguous.bit d) ∧
  next.nG = BitVec.setWidth 1 (BitVec.join1 [BitVec.access d 11]) ∧
  next.guardedpage = BitVec.setWidth 1 (BitVec.join1 [BitVec.access d 50])

private partial def solveShape (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "leaf shape search depth exhausted"
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if ty.isForall then
    evalTactic (← `(tactic| intro x))
    solveShape (fuel - 1)
    return
  if ty.isAppOf ``S1Normality.Normal then
    evalTactic (← `(tactic| leaf_normality))
    return
  let saved ← saveState
  try
    evalTactic (← `(tactic| solve |
      apply S1NormalPost.pure_post
      simp_all [Shape, apply_ite]))
    return
  catch err =>
    if ty.isAppOf ``S1NormalPost.Ensures &&
        (ty.getAppArgs[1]!).isAppOf ``Pure.pure then throw err
    saved.restore
  evalTactic (← `(tactic| first
    | apply S1NormalPost.bind_post
    | apply S1NormalPost.ite_post))
  let goals ← getGoals
  for branch in goals do
    setGoals [branch]
    solveShape (fuel - 1)
  setGoals []
elab "leaf_shape" : tactic => solveShape 200

theorem normal_shape (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams)
    (d : BitVec 64)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hAIE : wp.aie = 0#1) (hMAIR : wp.mair = 0x000000040044ffff#64)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (hLevel : 1 ≤ current.level ∧ current.level ≤ 3) :
    S1NormalPost.Ensures (AArch64_S1NextWalkStateLeaf current s2fs1mro .Regime_EL20
      .SS_NonSecure wp d) (Shape wp current d) := by
  have hBase : AArch64_LeafBase d 0#1 0#1 .TGx_4KB current.level =
      (pure (S1LeafBaseFrame.base d current.level) : SailM (BitVec 56)) := by
    funext s
    exact S1LeafBaseFrame.total d current.level s (by omega)
  have hAttr : AArch64_MAIRAttr (S1MAIRKernel.index d) wp.mair2 0x000000040044ffff#64 =
      (pure (S1MAIRKernel.value (S1MAIRKernel.index d)) : SailM (BitVec 8)) := by
    funext s
    exact S1MAIRKernel.total _ _ s (S1MAIRKernel.index_bounds d)
  simp only [S1MAIRKernel.index] at hAttr
  have hContig : AArch64_ContiguousBit .TGx_4KB 0#1 current.level d =
      (pure (S1Contiguous.bit d) : SailM (BitVec 1)) := by
    funext s
    exact S1Contiguous.total d current.level s (by omega)
  have hSecure : ((.PAS_NonSecure : PASpace) == .PAS_Secure) = false := by decide
  have hRoot : ((.PAS_NonSecure : PASpace) == .PAS_Root) = false := by decide
  have hRealm : ((.PAS_NonSecure : PASpace) == .PAS_Realm) = false := by decide
  have hSSecure : ((.SS_NonSecure : SecurityState) == .SS_Secure) = false := by decide
  have hUP : HasUnprivileged .Regime_EL20 = true := by decide
  have h01 : ((0#1) == (1#1)) = false := by decide
  have ha4 : (4 <b Sail.BitVec.length d) = true := by
    change (4 <b (64 : Int)) = true
    decide
  have ha9 : (9 <b Sail.BitVec.length d) = true := by
    change (9 <b (64 : Int)) = true
    decide
  have ha11 : (11 <b Sail.BitVec.length d) = true := by
    change (11 <b (64 : Int)) = true
    decide
  have ha50 : (50 <b Sail.BitVec.length d) = true := by
    change (50 <b (64 : Int)) = true
    decide
  have ha52 : (52 <b Sail.BitVec.length d) = true := by
    change (52 <b (64 : Int)) = true
    decide
  have assert_true (message : String) : ArmFull.assert true message = (pure () : SailM Unit) := rfl
  unfold AArch64_S1NextWalkStateLeaf
  simp only [hD128, hDS, hTG, hAIE, hMAIR, hPAS, hSecure, hRoot, hRealm,
    hSSecure, hUP, h01, hBase, hAttr, hContig]
  simp only [Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true,
    Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
    ha4, ha9, ha11, ha50, ha52, assert_true, pure_bind, hAttr, S1NormalPost.ite_pure]
  by_cases hp : wp.pnch = 1#1 <;> by_cases hd : current.disch = 1#1 <;> leaf_shape

#print axioms normal_shape
#print axioms leaf_levels
end S1LeafShape
