import MemM1.LeafFactsGW
import MemM1.LeafFactsGCW
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.LeafFactsL2
abbrev State := SequentialState Regs oracleChoiceSource
open MemM1.LeafFactsG (LeafValue)

/-! Level-2 BLOCK (2 MB, 4K granule) analogues of `LeafFactsGW.leafGW` (data, WB, DBM free)
and `LeafFactsGCW.leafGCW` / `leafGCW_x` (code, WB). The `post` lemmas of GW / GCW are
level-generic (`1 ≤ level ≤ 3`); only the output address differs: eval's
`S1LeafBaseFrame.base d 2` is d[47:21] << 21. `AArch64_S1NextWalkStateLeaf` does not read
descriptor bits [1:0], so the block/page type is not a hypothesis here (the walk's
classification of d as a level-2 leaf is the caller's business). -/

/-- The level-2 (2 MB) output address of a block descriptor: bits 47:21 of `d`, shifted left by 21. -/
def blockBase (d : BitVec 64) : BitVec 56 :=
  BitVec.setWidth 56 (BitVec.extractLsb 47 21 d) <<< 21

theorem blockBase_aligned (d : BitVec 64) : (blockBase d).toNat % 2097152 = 0 := by
  simp [blockBase, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]

theorem blockBase_low (d : BitVec 64) : BitVec.extractLsb' 0 21 (blockBase d) = 0#21 := by
  ext i hi
  simp [blockBase, BitVec.getElem_extractLsb', BitVec.getLsbD_shiftLeft]
  omega

theorem base_eq2 (d : BitVec 64) : S1LeafBaseFrame.base d 2 = blockBase d := by
  have h : S1LeafBaseFrame.base d 2 = Sail.BitVec.updateSubrange (0#56) 47 0
      (Sail.BitVec.castWidth (m := 48) ((Sail.BitVec.extractLsb d 47 21) +++ (0#21))) := rfl
  have hc : Sail.BitVec.castWidth (m := 48) ((Sail.BitVec.extractLsb d 47 21) +++ (0#21)) =
      ((Sail.BitVec.extractLsb d 47 21) +++ (0#21)) := Sail.BitVec.castWidth_eq _
  have ha : ∀ j, (Sail.BitVec.extractLsb d 47 21 +++ 0#21).getLsbD j =
      (decide (21 ≤ j) && decide (j ≤ 47) && d.getLsbD j) := by
    intro j
    rw [BitVec.getLsbD_append]
    by_cases hj : j < 21
    · simp [hj]; omega
    · have e : 21 + (j - 21) = j := by omega
      have e2 : 21 ≤ j := by omega
      simp [hj, e, e2, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb]
  rw [h, hc]
  ext i hi
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', blockBase]
  simp [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb, ha]
  by_cases hi21 : i < 21
  · simp [hi21]; omega
  · have e : 21 + (i - 21) = i := by omega
    have e2 : 21 ≤ i := by omega
    simp [hi21, e, e2]

theorem contig0 (d : BitVec 64) (hCont : Sail.BitVec.access d 52 = 0#1) :
    S1Contiguous.bit d = 0#1 := by
  unfold S1Contiguous.bit
  rw [hCont]
  rfl

/-- Data block (writable, AP = 01; DBM / ha / hd unconstrained), Normal WB. -/
theorem leafL2 (cur : TTWState) (m : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (next : TTWState) (R : Regs)
    (hcur : cur.level = 2) (hpas : cur.baseaddress.paspace = .PAS_NonSecure)
    (hMAIR : wp.mair = 0x000000040044ffff#64) (hd128 : wp.d128 = 0#1)
    (hTG : wp.tgx = .TGx_4KB) (hpie : wp.pie = 0#1)
    (hds : wp.ds = 0#1) (haie : wp.aie = 0#1)
    (hcurAPT : cur.permissions.ap_table = 0#2)
    (hIdx : Sail.BitVec.extractLsb d 4 2 = 0#3 ∨ Sail.BitVec.extractLsb d 4 2 = 1#3)
    (hAP : Sail.BitVec.extractLsb d 7 6 = 1#2)
    (hCont : Sail.BitVec.access d 52 = 0#1)
    (h : LeafValue .Regime_EL20 cur m wp d next R) :
    next.memattrs.memtype = .MemType_Normal ∧
    next.memattrs.inner.attrs = MemAttr_WB ∧ next.memattrs.outer.attrs = MemAttr_WB ∧
    BitVec.setWidth 2 (Sail.BitVec.extractLsb next.permissions.ap 2 1) = 1#2 ∧
    next.permissions.ap_table = 0#2 ∧
    next.level = 2 ∧ next.contiguous = 0#1 ∧
    next.baseaddress = {paspace := .PAS_NonSecure, address := blockBase d} ∧
    next.memattrs.tags = (if wp.mtx = 1#1 then .MemTag_CanonicallyTagged else .MemTag_Untagged) := by
  obtain ⟨s0, s1, -, hrun⟩ := h
  have hL : 1 ≤ cur.level ∧ cur.level ≤ 3 := by omega
  obtain ⟨a, t, ha, -, hP⟩ :=
    MemM1.LeafFactsGW.post cur m wp d hd128 hds hTG haie hMAIR hpie hpas hL hIdx hAP s0
  rw [hrun] at ha
  injection ha with hn hs
  subst hn
  obtain ⟨⟨-, hlev, hbase, hpasp, hcont, -, -⟩, hmt, hin, hout, htag, hapt, hap⟩ := hP
  refine ⟨hmt, hin, hout, hap, hapt.trans hcurAPT, hlev.trans hcur, ?_, ?_, htag⟩
  · rw [hcont, contig0 d hCont]; split <;> rfl
  · rw [hcur, base_eq2] at hbase
    rw [← hbase, ← hpasp]

/-- Code block (DBM = 0), Normal WB, execute-side fields. -/
theorem leafL2C (cur : TTWState) (m : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (next : TTWState) (R : Regs)
    (hcur : cur.level = 2) (hpas : cur.baseaddress.paspace = .PAS_NonSecure)
    (hMAIR : wp.mair = 0x000000040044ffff#64) (hd128 : wp.d128 = 0#1)
    (hTG : wp.tgx = .TGx_4KB) (hpie : wp.pie = 0#1)
    (hds : wp.ds = 0#1) (haie : wp.aie = 0#1)
    (hcurUXT : cur.permissions.uxn_table = 0#1)
    (hIdx : Sail.BitVec.extractLsb d 4 2 = 0#3 ∨ Sail.BitVec.extractLsb d 4 2 = 1#3)
    (hDBM : Sail.BitVec.access d 51 = 0#1)
    (hCont : Sail.BitVec.access d 52 = 0#1)
    (h : LeafValue .Regime_EL20 cur m wp d next R) :
    next.memattrs.memtype = .MemType_Normal ∧
    next.memattrs.inner.attrs = MemAttr_WB ∧ next.memattrs.outer.attrs = MemAttr_WB ∧
    next.permissions.uxn = Sail.BitVec.access d 54 ∧
    next.permissions.uxn_table = 0#1 ∧
    next.guardedpage = Sail.BitVec.access d 50 ∧
    next.level = 2 ∧ next.contiguous = 0#1 ∧
    next.baseaddress = {paspace := .PAS_NonSecure, address := blockBase d} := by
  obtain ⟨s0, s1, -, hrun⟩ := h
  have hL : 1 ≤ cur.level ∧ cur.level ≤ 3 := by omega
  obtain ⟨a, t, ha, -, hP⟩ :=
    MemM1.LeafFactsGCW.post cur m wp d hd128 hds hTG haie hMAIR hpie hpas hL hIdx hDBM s0
  rw [hrun] at ha
  injection ha with hn hs
  subst hn
  obtain ⟨⟨-, hlev, hbase, hpasp, hcont, -, hgp⟩, hmt, hin, hout, huxt, huxn⟩ := hP
  refine ⟨hmt, hin, hout, huxn, huxt.trans hcurUXT, hgp.trans (MemM1.LeafFactsGC.bit1 _),
    hlev.trans hcur, ?_, ?_⟩
  · rw [hcont, contig0 d hCont]; split <;> rfl
  · rw [hcur, base_eq2] at hbase
    rw [← hbase, ← hpasp]

/-- Code block corollary in the `WalkOKIF` forms (UXN = 0, GP = 0). -/
theorem leafL2C_x (cur : TTWState) (m : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (next : TTWState) (R : Regs)
    (hcur : cur.level = 2) (hpas : cur.baseaddress.paspace = .PAS_NonSecure)
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
    next.memattrs.memtype = .MemType_Normal ∧
    next.memattrs.inner.attrs = MemAttr_WB ∧ next.memattrs.outer.attrs = MemAttr_WB ∧
    next.level = 2 ∧ next.contiguous = 0#1 ∧
    next.baseaddress = {paspace := .PAS_NonSecure, address := blockBase d} ∧
    next.permissions.uxn = 0#1 ∧ next.permissions.uxn_table = 0#1 ∧ next.guardedpage = 0#1 := by
  obtain ⟨h1, hi, ho, h2, h3, h4, h5, h6, h7⟩ :=
    leafL2C cur m wp d next R hcur hpas hMAIR hd128 hTG hpie hds haie hcurUXT hIdx hDBM hCont h
  exact ⟨h1, hi, ho, h5, h6, h7, h2.trans hUXN, h3, h4.trans hGP⟩

/-- Sanity: a 2 MB block at PA 0x40200000 (bits[1:0] = 01, AttrIndx 0, AP = 01, AF). -/
theorem block_example : blockBase 0x0000000040200441#64 = 0x40200000#56 := by decide

#print axioms blockBase_aligned
#print axioms blockBase_low
#print axioms base_eq2
#print axioms leafL2
#print axioms leafL2C
#print axioms leafL2C_x
#print axioms block_example
end MemM1.LeafFactsL2
