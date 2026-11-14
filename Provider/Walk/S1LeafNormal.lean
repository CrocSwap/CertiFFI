import Walk.S1Normality
import Walk.S1MAIRKernel
import Walk.S1LeafBaseFrame
import Walk.S1Contiguous
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open Lean Meta Elab Tactic
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
set_option pp.maxSteps 2500
namespace S1LeafNormal
open S1Normality

/- Proof search assembles only ordinary bind/map/conditional normality lemmas.
   A failed search produces no accepted declaration. -/
private partial def solveNormal (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "leaf normality search depth exhausted"
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if ty.isForall then
    evalTactic (← `(tactic| intro x))
    solveNormal (fuel - 1)
    return
  let saved ← saveState
  try
    evalTactic (← `(tactic| solve | first
      | exact S1Normality.pure_normal _
      | exact S1Normality.occ_normal _
      | exact S1Normality.walk_normal _
      | exact S1Normality.address_normal _
      | exact S1Normality.bits_normal _ _
      | (apply S1Normality.assert_normal; decide)
      | (apply S1Normality.attrs_normal; exact S1MAIRKernel.valid _)
      | (apply S1Normality.permissions_normal; assumption)))
    return
  catch _ => saved.restore
  evalTactic (← `(tactic| first
    | apply S1Normality.bind_normal
    | apply S1Normality.map_normal
    | apply S1Normality.ite_normal))
  let goals ← getGoals
  for branch in goals do
    setGoals [branch]
    solveNormal (fuel - 1)
  setGoals []
elab "leaf_normality" : tactic => solveNormal 200

theorem normal (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams)
    (d : BitVec 64)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hAIE : wp.aie = 0#1) (hMAIR : wp.mair = 0x000000040044ffff#64)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (hLevel : 1 ≤ current.level ∧ current.level ≤ 3) :
    Normal (AArch64_S1NextWalkStateLeaf current s2fs1mro .Regime_EL20
      .SS_NonSecure wp d) := by
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
    ha4, ha9, ha11, ha50, ha52, assert_true, pure_bind, hAttr]
  leaf_normality

theorem total (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams)
    (d : BitVec 64) (s : S1Normality.State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hAIE : wp.aie = 0#1) (hMAIR : wp.mair = 0x000000040044ffff#64)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (hLevel : 1 ≤ current.level ∧ current.level ≤ 3) :
    ∃ (next : TTWState) (t : S1Normality.State),
      AArch64_S1NextWalkStateLeaf current s2fs1mro .Regime_EL20 .SS_NonSecure wp d s =
        .ok next t ∧ t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events :=
  normal current s2fs1mro wp d hD128 hDS hTG hAIE hMAIR hPAS hLevel s
#print axioms total
end S1LeafNormal
