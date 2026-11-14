import MemM1.LeafFactsG
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open Lean Meta Elab Tactic
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.LeafFactsGD
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality S1NormalPost
open MemM1.LeafFactsG (leafBase base_eq bind_post' attrs_ens LeafValue ite_prop)

/-! `MemM1.LeafFactsG.leafG_rw` without the DBM (bit 51) hypothesis, for writable pages
(AP = 01, so AP[2] = 0). With FEAT_HAFDBS (`wp.ha = wp.hd = 1`) and DBM = 1 the model clears
AP[2] in `AArch64_S1ApplyOutputPerms`; since AP[2] is already 0 this changes nothing.
`wp.ha` / `wp.hd` are unconstrained. -/

theorem ap_key (x : BitVec 3) :
    BitVec.setWidth 2 (Sail.BitVec.extractLsb (Sail.BitVec.updateSubrange x 2 1 (1#2)) 2 1) = 1#2 := by
  revert x; decide

theorem ap_key_dbm (x : BitVec 3) :
    BitVec.setWidth 2 (Sail.BitVec.extractLsb
      (BitVec.update (Sail.BitVec.updateSubrange x 2 1 (1#2)) 2 (Bit 0#1)) 2 1) = 1#2 := by
  revert x; decide

theorem perms_ens (p : Permissions) (d : BitVec 64) (wp : S1TTWParams)
    (hd128 : wp.d128 = 0#1) (hpie : wp.pie = 0#1) (hAP : Sail.BitVec.extractLsb d 7 6 = 1#2) :
    Ensures (AArch64_S1ApplyOutputPerms p d .Regime_EL20 wp) (fun o =>
      o.ap_table = p.ap_table ∧
      BitVec.setWidth 2 (Sail.BitVec.extractLsb o.ap 2 1) = 1#2) := by
  intro s
  have hf := S1LeafOutputPermsFrame.native_frame p d wp s
  rw [S1LeafOutputPerms.complete p d wp s hd128]
  revert hf
  delta S1LeafOutputPerms.native
  intro hf
  refine ⟨_, _, rfl, hf, ?_, ?_⟩
  all_goals clear hf
  · simp [hpie, hAP]
    refine ite_prop (fun q : Permissions => q.ap_table = p.ap_table) _ _ _ rfl ?_
    exact ite_prop (fun q : Permissions => q.ap_table = p.ap_table) _ _ _ rfl rfl
  · simp [hpie, hAP]
    refine ite_prop (fun q : Permissions =>
      BitVec.setWidth 2 (Sail.BitVec.extractLsb q.ap 2 1) = 1#2) _ _ _ ?_ ?_
    · exact ite_prop (fun a : BitVec 3 =>
        BitVec.setWidth 2 (Sail.BitVec.extractLsb a 2 1) = 1#2) _ _ _ (ap_key_dbm _) (ap_key _)
    · exact ite_prop (fun q : Permissions =>
        BitVec.setWidth 2 (Sail.BitVec.extractLsb q.ap 2 1) = 1#2) _ _ _ (ap_key_dbm _) (ap_key _)

def Post (wp : S1TTWParams) (cur : TTWState) (d : BitVec 64) (next : TTWState) : Prop :=
  S1LeafShape.Shape wp cur d next ∧
  next.memattrs.memtype = .MemType_Normal ∧
  next.memattrs.tags = (if wp.mtx = 1#1 then .MemTag_CanonicallyTagged else .MemTag_Untagged) ∧
  next.permissions.ap_table = cur.permissions.ap_table ∧
  BitVec.setWidth 2 (Sail.BitVec.extractLsb next.permissions.ap 2 1) = 1#2

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
          (ty.getAppArgs[1]!).isAppOf ``Pure.pure then throw err
      saved.restore
    evalTactic (← `(tactic| first
      | refine bind_post' _ _ _ _ (attrs_ens _ _) ?_
      | refine bind_post' _ _ _ _
          (perms_ens _ _ _ (by assumption) (by assumption) (by assumption)) ?_
      | apply S1NormalPost.bind_post
      | apply S1NormalPost.ite_post))
    let goals ← getGoals
    for branch in goals do
      setGoals [branch]
      solvePost fuel
    setGoals []
elab "leaf_post_gd" : tactic => solvePost 200

theorem post (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hAIE : wp.aie = 0#1) (hMAIR : wp.mair = 0x000000040044ffff#64) (hPIE : wp.pie = 0#1)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (hLevel : 1 ≤ current.level ∧ current.level ≤ 3)
    (hIdx : Sail.BitVec.extractLsb d 4 2 = 0#3 ∨ Sail.BitVec.extractLsb d 4 2 = 1#3)
    (hAP : Sail.BitVec.extractLsb d 7 6 = 1#2) :
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
  by_cases hp : wp.pnch = 1#1 <;> by_cases hd : current.disch = 1#1 <;> leaf_post_gd

/-- `leafG_rw` for writable pages, with no DBM hypothesis: DBM (bit 51), `wp.ha` and `wp.hd`
    are arbitrary. -/
theorem leafGD (cur : TTWState) (m : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (next : TTWState) (R : Regs)
    (hcur : cur.level = 3) (hpas : cur.baseaddress.paspace = .PAS_NonSecure)
    (hMAIR : wp.mair = 0x000000040044ffff#64) (hd128 : wp.d128 = 0#1)
    (hTG : wp.tgx = .TGx_4KB) (hpie : wp.pie = 0#1)
    (hds : wp.ds = 0#1) (haie : wp.aie = 0#1)
    (hcurAPT : cur.permissions.ap_table = 0#2)
    (hIdx : Sail.BitVec.extractLsb d 4 2 = 0#3 ∨ Sail.BitVec.extractLsb d 4 2 = 1#3)
    (hAP : Sail.BitVec.extractLsb d 7 6 = 1#2)
    (hCont : Sail.BitVec.access d 52 = 0#1)
    (h : LeafValue .Regime_EL20 cur m wp d next R) :
    next.memattrs.memtype = .MemType_Normal ∧
    BitVec.setWidth 2 (Sail.BitVec.extractLsb next.permissions.ap 2 1) = 1#2 ∧
    next.permissions.ap_table = 0#2 ∧
    next.level = 3 ∧ next.contiguous = 0#1 ∧
    next.baseaddress = {paspace := .PAS_NonSecure, address := leafBase d} ∧
    next.memattrs.tags = (if wp.mtx = 1#1 then .MemTag_CanonicallyTagged else .MemTag_Untagged) := by
  obtain ⟨s0, s1, -, hrun⟩ := h
  have hL : 1 ≤ cur.level ∧ cur.level ≤ 3 := by omega
  obtain ⟨a, t, ha, -, hP⟩ := post cur m wp d hd128 hds hTG haie hMAIR hpie hpas hL hIdx hAP s0
  rw [hrun] at ha
  injection ha with hn hs
  subst hn
  obtain ⟨⟨-, hlev, hbase, hpasp, hcont, -, -⟩, hmt, htag, hapt, hap⟩ := hP
  have hbit : S1Contiguous.bit d = 0#1 := by
    unfold S1Contiguous.bit
    rw [hCont]
    rfl
  refine ⟨hmt, hap, hapt.trans hcurAPT, hlev.trans hcur, ?_, ?_, htag⟩
  · rw [hcont, hbit]; split <;> rfl
  · rw [hcur, base_eq] at hbase
    rw [← hbase, ← hpasp]

/-- Sanity: a dirty writable page (AP = 01, DBM = 1) meets the bit hypotheses. -/
theorem dirty_bits :
    (Sail.BitVec.extractLsb (0x0008000505000443#64) 4 2 = 0#3 ∨
      Sail.BitVec.extractLsb (0x0008000505000443#64) 4 2 = 1#3) ∧
    Sail.BitVec.extractLsb (0x0008000505000443#64) 7 6 = 1#2 ∧
    Sail.BitVec.access (0x0008000505000443#64) 51 = 1#1 ∧
    Sail.BitVec.access (0x0008000505000443#64) 52 = 0#1 := by decide

#print axioms perms_ens
#print axioms post
#print axioms leafGD
#print axioms dirty_bits
end MemM1.LeafFactsGD
