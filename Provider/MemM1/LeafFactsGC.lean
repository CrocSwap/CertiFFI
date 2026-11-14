import MemM1.LeafFactsG
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open Lean Meta Elab Tactic
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.LeafFactsGC
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality S1NormalPost
open MemM1.LeafFactsG (leafBase base_eq bind_post' attrs_ens LeafValue)

/-! Code-page (execute-side) analogue of `MemM1.LeafFactsG.leafG`: UXN, UXNTable and GP
instead of AP / APTable. With `wp.d128 = 0` the model sets GP from descriptor bit 50
unconditionally (no FEAT_BTI or walk-parameter dependency), see `S1LeafShape.Shape`. -/

theorem bit1 (x : BitVec 1) : BitVec.setWidth 1 (BitVec.join1 [x]) = x := by
  revert x; decide

theorem perms_ens (p : Permissions) (d : BitVec 64) (wp : S1TTWParams)
    (hd128 : wp.d128 = 0#1) (hpie : wp.pie = 0#1) (hb51 : Sail.BitVec.access d 51 = 0#1) :
    Ensures (AArch64_S1ApplyOutputPerms p d .Regime_EL20 wp) (fun o =>
      o.uxn_table = p.uxn_table ∧ o.uxn = Sail.BitVec.access d 54) := by
  intro s
  have hf := S1LeafOutputPermsFrame.native_frame p d wp s
  rw [S1LeafOutputPerms.complete p d wp s hd128]
  revert hf
  delta S1LeafOutputPerms.native
  intro hf
  refine ⟨_, _, rfl, hf, ?_, ?_⟩
  all_goals clear hf
  all_goals have hb : ¬ (BitVec.join1 [Sail.BitVec.access d 51] = 1#1) := by rw [hb51]; decide
  · simp [hpie, hb]
    exact MemM1.LeafFactsG.ite_prop (fun q : Permissions => q.uxn_table = p.uxn_table)
      _ _ _ rfl rfl
  · simp [hpie, hb]
    exact MemM1.LeafFactsG.ite_prop (fun q : Permissions => q.uxn = Sail.BitVec.access d 54)
      _ _ _ (bit1 _) (bit1 _)

theorem attrs_mt (sh : BitVec 2) (wp : S1TTWParams) :
    Ensures (S1DecodeMemAttrs 255#8 sh true wp) (fun a => a.memtype = .MemType_Normal) := by
  intro s
  obtain ⟨a, t, h1, h2, h3, -⟩ := attrs_ens sh wp s
  exact ⟨a, t, h1, h2, h3⟩

def Post (wp : S1TTWParams) (cur : TTWState) (d : BitVec 64) (next : TTWState) : Prop :=
  S1LeafShape.Shape wp cur d next ∧
  next.memattrs.memtype = .MemType_Normal ∧
  next.permissions.uxn_table = cur.permissions.uxn_table ∧
  next.permissions.uxn = Sail.BitVec.access d 54

def solvePost : Nat → TacticM Unit
  | 0 => throwError "leaf post search depth exhausted"
  | fuel + 1 => do
    let goal ← getMainGoal
    let ty ← instantiateMVars (← goal.getType)
    if ty.isForall then
      evalTactic (← `(tactic| intro x))
      solvePost fuel
      return
    if ty.isAppOf ``S1Normality.Normal then
      evalTactic (← `(tactic| leaf_normality))
      return
    let saved ← saveState
    try
      evalTactic (← `(tactic| solve |
        apply S1NormalPost.pure_post
        simp_all [Post, S1LeafShape.Shape, apply_ite]))
      return
    catch err =>
      if ty.isAppOf ``S1NormalPost.Ensures &&
          (ty.getAppArgs[1]!).isAppOf ``Pure.pure then
        throw err
      saved.restore
    evalTactic (← `(tactic| first
      | refine bind_post' _ _ _ _ (attrs_mt _ _) ?_
      | refine bind_post' _ _ _ _
          (perms_ens _ _ _ (by assumption) (by assumption) (by assumption)) ?_
      | apply S1NormalPost.bind_post
      | apply S1NormalPost.ite_post))
    let goals ← getGoals
    for branch in goals do
      setGoals [branch]
      solvePost fuel
    setGoals []
elab "leaf_post_gc" : tactic => solvePost 200

theorem post (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hAIE : wp.aie = 0#1) (hMAIR : wp.mair = 0x000000040044ffff#64) (hPIE : wp.pie = 0#1)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (hLevel : 1 ≤ current.level ∧ current.level ≤ 3)
    (hIdx : Sail.BitVec.extractLsb d 4 2 = 0#3 ∨ Sail.BitVec.extractLsb d 4 2 = 1#3)
    (hb51 : Sail.BitVec.access d 51 = 0#1) :
    Ensures (AArch64_S1NextWalkStateLeaf current s2fs1mro .Regime_EL20
      .SS_NonSecure wp d) (Post wp current d) := by
  have hBase : AArch64_LeafBase d 0#1 0#1 .TGx_4KB current.level =
      (pure (S1LeafBaseFrame.base d current.level) : SailM (BitVec 56)) := by
    funext s
    exact S1LeafBaseFrame.total d current.level s (by omega)
  have hval : S1MAIRKernel.value (S1MAIRKernel.index d) = 255#8 := by
    rcases hIdx with h | h <;> simp [S1MAIRKernel.index, S1MAIRKernel.value, h]
  have hAttr : AArch64_MAIRAttr (S1MAIRKernel.index d) wp.mair2 0x000000040044ffff#64 =
      (pure 255#8 : SailM (BitVec 8)) := by
    funext s
    rw [← hval]
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
  by_cases hp : wp.pnch = 1#1 <;> by_cases hd : current.disch = 1#1 <;> leaf_post_gc

/-- Code-page leaf facts for an arbitrary level-3 page descriptor `d`. -/
theorem leafGC (cur : TTWState) (m : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (next : TTWState) (R : Regs)
    (hcur : cur.level = 3) (hpas : cur.baseaddress.paspace = .PAS_NonSecure)
    (hMAIR : wp.mair = 0x000000040044ffff#64) (hd128 : wp.d128 = 0#1)
    (hTG : wp.tgx = .TGx_4KB) (hpie : wp.pie = 0#1)
    (hds : wp.ds = 0#1) (haie : wp.aie = 0#1)
    (hcurUXT : cur.permissions.uxn_table = 0#1)
    (hIdx : Sail.BitVec.extractLsb d 4 2 = 0#3 ∨ Sail.BitVec.extractLsb d 4 2 = 1#3)
    (hDBM : Sail.BitVec.access d 51 = 0#1)
    (hCont : Sail.BitVec.access d 52 = 0#1)
    (h : LeafValue .Regime_EL20 cur m wp d next R) :
    next.memattrs.memtype = .MemType_Normal ∧
    next.permissions.uxn = Sail.BitVec.access d 54 ∧
    next.permissions.uxn_table = 0#1 ∧
    next.guardedpage = Sail.BitVec.access d 50 ∧
    next.level = 3 ∧ next.contiguous = 0#1 ∧
    next.baseaddress = {paspace := .PAS_NonSecure, address := leafBase d} := by
  obtain ⟨s0, s1, -, hrun⟩ := h
  have hL : 1 ≤ cur.level ∧ cur.level ≤ 3 := by omega
  obtain ⟨a, t, ha, -, hP⟩ := post cur m wp d hd128 hds hTG haie hMAIR hpie hpas hL hIdx hDBM s0
  rw [hrun] at ha
  injection ha with hn hs
  subst hn
  obtain ⟨⟨-, hlev, hbase, hpasp, hcont, -, hgp⟩, hmt, huxt, huxn⟩ := hP
  have hbit : S1Contiguous.bit d = 0#1 := by
    unfold S1Contiguous.bit
    rw [hCont]
    rfl
  refine ⟨hmt, huxn, huxt.trans hcurUXT, hgp.trans (bit1 _), hlev.trans hcur, ?_, ?_⟩
  · rw [hcont, hbit]; split <;> rfl
  · rw [hcur, base_eq] at hbase
    rw [← hbase, ← hpasp]

/-- Execute-side corollary in the forms `WitnessIF.WalkOKIF` uses. -/
theorem leafGC_x (cur : TTWState) (m : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (next : TTWState) (R : Regs)
    (hcur : cur.level = 3) (hpas : cur.baseaddress.paspace = .PAS_NonSecure)
    (hMAIR : wp.mair = 0x000000040044ffff#64) (hd128 : wp.d128 = 0#1)
    (hTG : wp.tgx = .TGx_4KB) (hpie : wp.pie = 0#1)
    (hds : wp.ds = 0#1) (haie : wp.aie = 0#1)
    (hcurUXT : cur.permissions.uxn_table = 0#1)
    (hIdx : Sail.BitVec.extractLsb d 4 2 = 0#3 ∨ Sail.BitVec.extractLsb d 4 2 = 1#3)
    (hDBM : Sail.BitVec.access d 51 = 0#1)
    (hCont : Sail.BitVec.access d 52 = 0#1)
    (hUXN : Sail.BitVec.access d 54 = 0#1)
    (hGP : Sail.BitVec.access d 50 = 0#1)
    (h : LeafValue .Regime_EL20 cur m wp d next R) :
    next.memattrs.memtype = .MemType_Normal ∧ next.level = 3 ∧ next.contiguous = 0#1 ∧
    next.baseaddress = {paspace := .PAS_NonSecure, address := leafBase d} ∧
    next.permissions.uxn = 0#1 ∧ next.permissions.uxn_table = 0#1 ∧ next.guardedpage = 0#1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    leafGC cur m wp d next R hcur hpas hMAIR hd128 hTG hpie hds haie hcurUXT hIdx hDBM hCont h
  exact ⟨h1, h5, h6, h7, h2.trans hUXN, h3, h4.trans hGP⟩

/-- Sanity: the J3c code leaf satisfies every bit hypothesis of `leafGC_x`. -/
theorem j3c_bits :
    (Sail.BitVec.extractLsb (0x0020000606000fc3#64) 4 2 = 0#3 ∨
      Sail.BitVec.extractLsb (0x0020000606000fc3#64) 4 2 = 1#3) ∧
    Sail.BitVec.access (0x0020000606000fc3#64) 51 = 0#1 ∧
    Sail.BitVec.access (0x0020000606000fc3#64) 52 = 0#1 ∧
    Sail.BitVec.access (0x0020000606000fc3#64) 54 = 0#1 ∧
    Sail.BitVec.access (0x0020000606000fc3#64) 50 = 0#1 := by decide

theorem j3c_base : leafBase 0x0020000606000fc3#64 = 0x606000000#56 := by decide

#print axioms perms_ens
#print axioms post
#print axioms leafGC
#print axioms leafGC_x
#print axioms j3c_bits
#print axioms j3c_base
end MemM1.LeafFactsGC
