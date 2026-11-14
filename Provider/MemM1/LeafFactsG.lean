import Walk.S1LeafShape
import Walk.S1LeafOutputPermsFrame
import Walk.S1KernelMemAttrsFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open Lean Meta Elab Tactic
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.LeafFactsG
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality S1NormalPost

/-! Generalization of `MemM1.LeafFacts.leaf` from the concrete descriptor
`0x4304000505000443#64` to any level-3 page descriptor `d` with
* AttrIndx (bits 4:2) selecting MAIR slot 0 or 1 (both `0xff` under the kernel MAIR),
* DBM (bit 51) = 0 (otherwise hardware dirty-state management clears AP[2]),
* Contiguous (bit 52) = 0.
NS (bit 5) is not needed: with `cur.baseaddress.paspace = NS` the model never reads it. -/

/-- The level-3 (4KB) output address of a descriptor: bits 47:12 of `d`, shifted left by 12. -/
def leafBase (d : BitVec 64) : BitVec 56 :=
  BitVec.setWidth 56 (BitVec.extractLsb 47 12 d) <<< 12

theorem leafBase_aligned (d : BitVec 64) : (leafBase d).toNat % 4096 = 0 := by
  simp [leafBase, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]

theorem leafBase_low (d : BitVec 64) : BitVec.extractLsb' 0 12 (leafBase d) = 0#12 := by
  ext i hi
  simp [leafBase, BitVec.getElem_extractLsb', BitVec.getLsbD_shiftLeft]
  omega

theorem leafBase_example : leafBase 0x4304000505000443#64 = 0x505000000#56 := by decide

theorem base_eq (d : BitVec 64) : S1LeafBaseFrame.base d 3 = leafBase d := by
  have h : S1LeafBaseFrame.base d 3 = Sail.BitVec.updateSubrange (0#56) 47 0
      (Sail.BitVec.castWidth (m := 48) ((Sail.BitVec.extractLsb d 47 12) +++ (0#12))) := rfl
  have hc : Sail.BitVec.castWidth (m := 48) ((Sail.BitVec.extractLsb d 47 12) +++ (0#12)) =
      ((Sail.BitVec.extractLsb d 47 12) +++ (0#12)) := Sail.BitVec.castWidth_eq _
  have ha : ∀ j, (Sail.BitVec.extractLsb d 47 12 +++ 0#12).getLsbD j =
      (decide (12 ≤ j) && decide (j ≤ 47) && d.getLsbD j) := by
    intro j
    rw [BitVec.getLsbD_append]
    by_cases hj : j < 12
    · simp [hj]; omega
    · have e : 12 + (j - 12) = j := by omega
      have e2 : 12 ≤ j := by omega
      simp [hj, e, e2, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb]
  rw [h, hc]
  ext i hi
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', leafBase]
  simp [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb, ha]
  by_cases hi12 : i < 12
  · simp [hi12]; omega
  · have e : 12 + (i - 12) = i := by omega
    have e2 : 12 ≤ i := by omega
    simp [hi12, e, e2]

/-- Ensures with a postcondition carried through a bind. -/
theorem bind_post' {α β : Type} (p : SailM α) (k : α → SailM β) (P : α → Prop)
    (q : β → Prop) (hp : Ensures p P) (hk : ∀ a, P a → Ensures (k a) q) :
    Ensures (p >>= k) q := by
  intro s
  rcases hp s with ⟨a, t, ha, ⟨hr1, hm1, he1⟩, hpa⟩
  rcases hk a hpa t with ⟨b, u, hb, ⟨hr2, hm2, he2⟩, hq⟩
  refine ⟨b, u, ?_, ⟨hr2.trans hr1, hm2.trans hm1, he2.trans he1⟩, hq⟩
  simp [Bind.bind, EStateM.bind, ha, hb]

theorem attrs_ens (sh : BitVec 2) (wp : S1TTWParams) :
    Ensures (S1DecodeMemAttrs 255#8 sh true wp) (fun a =>
      a.memtype = .MemType_Normal ∧
      a.tags = (if wp.mtx = 1#1 then .MemTag_CanonicallyTagged else .MemTag_Untagged)) := by
  intro s
  have hf := S1KernelMemAttrsFrame.normal_frame sh wp s
  rw [S1KernelMemAttrs.normal_eq]
  revert hf
  delta S1KernelMemAttrs.normal_native
  intro hf
  refine ⟨_, _, rfl, hf, rfl, ?_⟩
  simp

theorem ite_prop {α : Type} (P : α → Prop) (c : Prop) [Decidable c] (a b : α)
    (ha : P a) (hb : P b) : P (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem ap_key (x : BitVec 3) (y : BitVec 2) :
    BitVec.setWidth 2 (Sail.BitVec.extractLsb (Sail.BitVec.updateSubrange x 2 1 y) 2 1) = y := by
  revert x y; decide

theorem perms_ens (p : Permissions) (d : BitVec 64) (wp : S1TTWParams)
    (hd128 : wp.d128 = 0#1) (hpie : wp.pie = 0#1) (hb51 : Sail.BitVec.access d 51 = 0#1) :
    Ensures (AArch64_S1ApplyOutputPerms p d .Regime_EL20 wp) (fun o =>
      o.ap_table = p.ap_table ∧
      BitVec.setWidth 2 (Sail.BitVec.extractLsb o.ap 2 1) =
        Sail.BitVec.extractLsb d 7 6) := by
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
    exact ite_prop (fun q : Permissions => q.ap_table = p.ap_table) _ _ _ rfl rfl
  · simp [hpie, hb]
    exact ite_prop (fun q : Permissions =>
      BitVec.setWidth 2 (Sail.BitVec.extractLsb q.ap 2 1) = Sail.BitVec.extractLsb d 7 6) _ _ _
      (ap_key _ _) (ap_key _ _)

/-- Everything `leafG` needs about the leaf successor state. -/
def Post (wp : S1TTWParams) (cur : TTWState) (d : BitVec 64) (next : TTWState) : Prop :=
  S1LeafShape.Shape wp cur d next ∧
  next.memattrs.memtype = .MemType_Normal ∧
  next.memattrs.tags = (if wp.mtx = 1#1 then .MemTag_CanonicallyTagged else .MemTag_Untagged) ∧
  next.permissions.ap_table = cur.permissions.ap_table ∧
  BitVec.setWidth 2 (Sail.BitVec.extractLsb next.permissions.ap 2 1) = Sail.BitVec.extractLsb d 7 6

/-- Proof search: ordinary binds use eval's normality lemmas; the memory-attribute and
    output-permission binds carry their postconditions (`attrs_ens`, `perms_ens`). -/
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
elab "leaf_post" : tactic => solvePost 200

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
  by_cases hp : wp.pnch = 1#1 <;> by_cases hd : current.disch = 1#1 <;> leaf_post

/-- Eval's `ArmCert.Eval.M1a.LeafValue`, as in `MemM1.LeafFacts`. -/
def LeafValue (regime : Regime) (current : TTWState) (s2fs1mro : Bool)
    (wp : S1TTWParams) (d : BitVec 64) (next : TTWState) (R : Regs) : Prop :=
  ∃ s0 s1 : State, s0.regs = R ∧
    AArch64_S1NextWalkStateLeaf current s2fs1mro regime .SS_NonSecure wp d s0 = .ok next s1

/-- `MemM1.LeafFacts.leaf` for an arbitrary level-3 page descriptor `d`.
    AP: `next`'s AP[2:1] is the descriptor's bits 7:6 (so RW and RO pages are both covered). -/
theorem leafG (cur : TTWState) (m : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (next : TTWState) (R : Regs)
    (hcur : cur.level = 3) (hpas : cur.baseaddress.paspace = .PAS_NonSecure)
    (hMAIR : wp.mair = 0x000000040044ffff#64) (hd128 : wp.d128 = 0#1)
    (hTG : wp.tgx = .TGx_4KB) (hpie : wp.pie = 0#1)
    (hds : wp.ds = 0#1) (haie : wp.aie = 0#1)
    (hcurAPT : cur.permissions.ap_table = 0#2)
    (hIdx : Sail.BitVec.extractLsb d 4 2 = 0#3 ∨ Sail.BitVec.extractLsb d 4 2 = 1#3)
    (hDBM : Sail.BitVec.access d 51 = 0#1)
    (hCont : Sail.BitVec.access d 52 = 0#1)
    (h : LeafValue .Regime_EL20 cur m wp d next R) :
    next.memattrs.memtype = .MemType_Normal ∧
    BitVec.setWidth 2 (Sail.BitVec.extractLsb next.permissions.ap 2 1) =
      Sail.BitVec.extractLsb d 7 6 ∧
    next.permissions.ap_table = 0#2 ∧
    next.level = 3 ∧ next.contiguous = 0#1 ∧
    next.baseaddress = {paspace := .PAS_NonSecure, address := leafBase d} ∧
    next.memattrs.tags = (if wp.mtx = 1#1 then .MemTag_CanonicallyTagged else .MemTag_Untagged) := by
  obtain ⟨s0, s1, -, hrun⟩ := h
  have hL : 1 ≤ cur.level ∧ cur.level ≤ 3 := by omega
  obtain ⟨a, t, ha, -, hP⟩ := post cur m wp d hd128 hds hTG haie hMAIR hpie hpas hL hIdx hDBM s0
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

/-- The original statement shape (`AP[2:1] = 01`, EL0 read/write). -/
theorem leafG_rw (cur : TTWState) (m : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (next : TTWState) (R : Regs)
    (hcur : cur.level = 3) (hpas : cur.baseaddress.paspace = .PAS_NonSecure)
    (hMAIR : wp.mair = 0x000000040044ffff#64) (hd128 : wp.d128 = 0#1)
    (hTG : wp.tgx = .TGx_4KB) (hpie : wp.pie = 0#1)
    (hds : wp.ds = 0#1) (haie : wp.aie = 0#1)
    (hcurAPT : cur.permissions.ap_table = 0#2)
    (hIdx : Sail.BitVec.extractLsb d 4 2 = 0#3 ∨ Sail.BitVec.extractLsb d 4 2 = 1#3)
    (hAP : Sail.BitVec.extractLsb d 7 6 = 1#2)
    (hDBM : Sail.BitVec.access d 51 = 0#1)
    (hCont : Sail.BitVec.access d 52 = 0#1)
    (h : LeafValue .Regime_EL20 cur m wp d next R) :
    next.memattrs.memtype = .MemType_Normal ∧
    BitVec.setWidth 2 (Sail.BitVec.extractLsb next.permissions.ap 2 1) = 1#2 ∧
    next.permissions.ap_table = 0#2 ∧
    next.level = 3 ∧ next.contiguous = 0#1 ∧
    next.baseaddress = {paspace := .PAS_NonSecure, address := leafBase d} ∧
    next.memattrs.tags = (if wp.mtx = 1#1 then .MemTag_CanonicallyTagged else .MemTag_Untagged) := by
  have := leafG cur m wp d next R hcur hpas hMAIR hd128 hTG hpie hds haie hcurAPT hIdx hDBM hCont h
  rw [hAP] at this
  exact this

/-- Sanity: the concrete J3b leaf satisfies every bit hypothesis. -/
theorem j3b_bits :
    (Sail.BitVec.extractLsb (0x4304000505000443#64) 4 2 = 0#3 ∨
      Sail.BitVec.extractLsb (0x4304000505000443#64) 4 2 = 1#3) ∧
    Sail.BitVec.extractLsb (0x4304000505000443#64) 7 6 = 1#2 ∧
    Sail.BitVec.access (0x4304000505000443#64) 51 = 0#1 ∧
    Sail.BitVec.access (0x4304000505000443#64) 52 = 0#1 := by decide

#print axioms leafBase_aligned
#print axioms leafBase_low
#print axioms leafBase_example
#print axioms base_eq
#print axioms post
#print axioms leafG
#print axioms leafG_rw
#print axioms j3b_bits
end MemM1.LeafFactsG
