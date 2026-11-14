import ArmCertWalk.PageTransfer
import ArmCertWalk.WalkSlots
import ArmCertWalk.LeafOutputData

open Sail ArmFull
open ArmCert.Translate.Model ArmCertWalk S1LogicalReference
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace TranslateSpan

theorem observed_unique (rows : List LogicalRow) (hn : (rows.map (·.logical)).Nodup)
    {slot : Nat} {p q : FullAddress} {v w : S1DescriptorPIE.View 64}
    (hp : logicalObserve rows slot p v) (hq : logicalObserve rows slot q w) : p = q ∧ v = w := by
  obtain ⟨a, ha, ka, pa, va⟩ := hp
  obtain ⟨b, hb, kb, pb, vb⟩ := hq
  have fa := find_logical_of_nodup rows hn a ha slot ka.symm
  have fb := find_logical_of_nodup rows hn b hb slot kb.symm
  have ab : a = b := Option.some.inj (fa.symm.trans fb)
  subst b
  exact ⟨pa.trans pb.symm, va.trans vb.symm⟩

/-- Current realized topology determines each slot's view, even with duplicate logical rows. -/
theorem observed_unique_of_image {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (state : ArmCertWalk.State) (image : TopologyImageAt spec state)
    {slot : Nat} {p q : FullAddress} {v w : S1DescriptorPIE.View 64}
    (hp : logicalObserve spec.logicalRows slot p v) (hq : logicalObserve spec.logicalRows slot q w) :
    p = q ∧ v = w := by
  obtain ⟨ip, sp⟩ := spec.identity slot p v hp
  obtain ⟨iq, sq⟩ := spec.identity slot q w hq
  have addr : p.address = q.address := BitVec.eq_of_toNat_eq (ip.symm.trans iq)
  have physical : p = q := by cases p; cases q; simp_all
  subst q
  obtain ⟨dp, bp, vp⟩ := topology_realizes spec state image slot p v hp
  obtain ⟨dq, bq, vq⟩ := topology_realizes spec state image slot p w hq
  have eq : dp = dq := S1ByteMemory.descriptor_unique state.mem p.address.toNat dp dq
    (by intro i hi; simpa [S1LogicalReference.byte] using bp i hi)
    (by intro i hi; simpa [S1LogicalReference.byte] using bq i hi)
  exact ⟨rfl, vp.symm.trans (by rw [eq]; exact vq)⟩

theorem path_unique {observe : Observation}
    (unique : ∀ slot p q v w, observe slot p v → observe slot q w → p = q ∧ v = w)
    {paBits : Nat} {va : BitVec 64} {level bits : Nat} {base : BitVec 48} {e f : PathEnd}
    (p : Path observe paBits va level bits base e) (q : Path observe paBits va level bits base f) : e = f := by
  induction p generalizing f with
  | invalid level bits base physical view hl aligned present kind =>
    cases q <;> have same := unique _ _ _ _ _ present (by assumption)
    all_goals obtain ⟨rfl, rfl⟩ := same; simp_all
    all_goals first | omega | exact ih (by assumption)
  | leaf level bits base physical view hl aligned present kind =>
    cases q <;> have same := unique _ _ _ _ _ present (by assumption)
    all_goals obtain ⟨rfl, rfl⟩ := same; simp_all
    all_goals first | omega | exact ih (by assumption)
  | range level bits base physical view hl aligned present kind outOfRange =>
    cases q <;> have same := unique _ _ _ _ _ present (by assumption)
    all_goals obtain ⟨rfl, rfl⟩ := same; simp_all
    all_goals first | omega | exact ih (by assumption)
  | table level bits base physical view result hl aligned present kind inRange next ih =>
    cases q <;> have same := unique _ _ _ _ _ present (by assumption)
    all_goals obtain ⟨rfl, rfl⟩ := same; simp_all
    all_goals first | omega | exact ih (by assumption)

abbrev Leaf := Nat × FullAddress × Bool

def leafSize (l : Leaf) : Nat := S1LogicalReference.leafBits l.1 + if l.2.2 then 4 else 0

def leafPA (va : BitVec 64) (l : Leaf) : Nat := (S1LogicalReference.outputAddress va l.1 l.2.1 l.2.2).address.toNat

theorem leafSize_ge (l : Leaf) : 12 ≤ leafSize l := by
  unfold leafSize S1LogicalReference.leafBits; split <;> omega

theorem leafSize_le (l : Leaf) : leafSize l ≤ 43 := by
  unfold leafSize S1LogicalReference.leafBits; split <;> omega

/-- The leaf output address, unwrapped: the 2^bits-aligned block of the base plus the in-block offset. -/
theorem leafPA_eq (va : BitVec 64) (l : Leaf) :
    leafPA va l = l.2.1.address.toNat / 2 ^ leafSize l * 2 ^ leafSize l + va.toNat % 2 ^ leafSize l := by
  unfold leafPA S1LogicalReference.outputAddress
  simp only [BitVec.toNat_ofNat]
  have hs := leafSize_le l
  have hb : l.2.1.address.toNat < 2 ^ 56 := l.2.1.address.isLt
  have pos : 0 < 2 ^ leafSize l := Nat.two_pow_pos _
  -- 2^56 is a multiple of 2^bits, so the aligned block ends at or below 2^56
  obtain ⟨k, hk⟩ : 2 ^ leafSize l ∣ 2 ^ 56 := Nat.pow_dvd_pow 2 (by omega)
  have blk : l.2.1.address.toNat / 2 ^ leafSize l < k := by
    rw [Nat.div_lt_iff_lt_mul pos, Nat.mul_comm, ← hk]; exact hb
  have lt : l.2.1.address.toNat / 2 ^ leafSize l * 2 ^ leafSize l + va.toNat % 2 ^ leafSize l < 2 ^ 56 := by
    have hm := Nat.mod_lt va.toNat pos
    have : (l.2.1.address.toNat / 2 ^ leafSize l + 1) * 2 ^ leafSize l ≤ k * 2 ^ leafSize l :=
      Nat.mul_le_mul_right _ blk
    rw [Nat.succ_mul, Nat.mul_comm k, ← hk] at this
    omega
  exact Nat.mod_eq_of_lt (by unfold leafSize at lt; exact lt)

/-- Splitting the in-block offset at 4 KiB. -/
theorem mod_split (a s : Nat) (hs : 12 ≤ s) : a % 2 ^ s = a % 4096 + 4096 * (a / 4096 % 2 ^ (s - 12)) := by
  have e : 2 ^ s = 4096 * 2 ^ (s - 12) := by
    rw [show (4096 : Nat) = 2 ^ 12 from rfl, ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mod_mul]


theorem access_leaf_unique {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {a b : AccessQuery}
    {state : ArmCertWalk.State} (image : TopologyImageAt spec state) (same : SamePage a.va b.va)
    (da : S1AccessData spec config rows a) (db : S1AccessData spec config rows b) :
    da.leafLevel = db.leafLevel ∧ da.view = db.view := by
  have ea := path_page same da.path
  have e := path_unique (observe := logicalObserve spec.logicalRows)
    (fun slot p q v w hp hq => observed_unique_of_image spec state image (slot := slot) hp hq) ea db.path
  exact ⟨(PathEnd.leaf.inj e).1, (PathEnd.leaf.inj e).2.2.2⟩

theorem leafPA_mod (va : BitVec 64) (l : Leaf) : leafPA va l % 4096 = va.toNat % 4096 := by
  rw [leafPA_eq, mod_split va.toNat _ (leafSize_ge l)]
  obtain ⟨K, hK⟩ : ∃ K, 2 ^ leafSize l = 4096 * K :=
    ⟨2 ^ (leafSize l - 12), by rw [show (4096 : Nat) = 2 ^ 12 from rfl, ← Nat.pow_add]; congr 1; have := leafSize_ge l; omega⟩
  rw [hK]
  have hB : l.2.1.address.toNat / (4096 * K) * (4096 * K) = 4096 * (l.2.1.address.toNat / (4096 * K) * K) := by
    ac_rfl
  rw [hB]
  have := Nat.mod_lt va.toNat (by decide : 0 < 4096)
  omega

/-- One physical access span preserves offsets until the end of its 4KiB page. -/
theorem leafPA_step (va vb : BitVec 64) (l : Leaf) (i : Nat)
    (add : vb.toNat = va.toNat + i) (inside : va.toNat % 4096 + i < 4096) :
    leafPA vb l = leafPA va l + i := by
  have da := Nat.div_add_mod va.toNat 4096
  have db := Nat.div_add_mod vb.toNat 4096
  have ra := Nat.mod_lt va.toNat (by decide : 0 < 4096)
  have rb := Nat.mod_lt vb.toNat (by decide : 0 < 4096)
  have pg : vb.toNat / 4096 = va.toNat / 4096 := by omega
  have off : vb.toNat % 4096 = va.toNat % 4096 + i := by omega
  rw [leafPA_eq, leafPA_eq, mod_split _ _ (leafSize_ge l), mod_split _ _ (leafSize_ge l), pg, off]
  omega

/-- Start-to-start translation consistency, derived from their existing path/map certificates.
    Both VAs here are actual translated access starts; there is no interior-VA mapping premise. -/
theorem access_start_step {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {a b : AccessQuery} {sa sb : ArmCertWalk.State}
    (image : TopologyImageAt spec sa)
    (da : S1AccessData spec config rows a) (db : S1AccessData spec config rows b)
    (ca : CurrentS1AccessAt spec config rows mapping a da sa)
    (cb : CurrentS1AccessAt spec config rows mapping b db sb)
    (i : Nat) (add : b.va.toNat = a.va.toNat + i) (inside : a.va.toNat % 4096 + i < 4096) :
    mapping b.va = (mapping a.va).map (· + i) := by
  have pg : SamePage a.va b.va := by
    unfold SamePage
    have := Nat.div_add_mod a.va.toNat 4096
    have := Nat.div_add_mod b.va.toNat 4096
    have := Nat.mod_lt a.va.toNat (by decide : 0 < 4096)
    have := Nat.mod_lt b.va.toNat (by decide : 0 < 4096)
    omega
  obtain ⟨lev, view⟩ := access_leaf_unique image pg da db
  rw [cb.map.mapped, ca.map.mapped, Option.map_some]
  rw [← lev, ← view]
  congr 1
  exact leafPA_step a.va b.va
    (da.leafLevel, {paspace := .PAS_NonSecure, address := leafBase da.leafLevel da.view.stable}, da.view.stable.getLsbD 52) i add inside

/-- Two actual accesses covering the same virtual byte agree on its physical byte. -/
theorem access_spans_agree {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {a b : AccessQuery} {sa sb : ArmCertWalk.State}
    (image : TopologyImageAt spec sa)
    (da : S1AccessData spec config rows a) (db : S1AccessData spec config rows b)
    (ca : CurrentS1AccessAt spec config rows mapping a da sa)
    (cb : CurrentS1AccessAt spec config rows mapping b db sb)
    (target : BitVec 64) (i j : Nat)
    (adda : target.toNat = a.va.toNat + i) (addb : target.toNat = b.va.toNat + j)
    (ina : a.va.toNat % 4096 + i < 4096) (inb : b.va.toNat % 4096 + j < 4096) :
    (mapping a.va).map (· + i) = (mapping b.va).map (· + j) := by
  have pg : SamePage a.va b.va := by
    unfold SamePage
    have := Nat.div_add_mod a.va.toNat 4096
    have := Nat.div_add_mod b.va.toNat 4096
    have := Nat.mod_lt a.va.toNat (by decide : 0 < 4096)
    have := Nat.mod_lt b.va.toNat (by decide : 0 < 4096)
    omega
  obtain ⟨lev, view⟩ := access_leaf_unique image pg da db
  rw [ca.map.mapped, cb.map.mapped, Option.map_some, Option.map_some, ← lev, ← view]
  let l : Leaf := (da.leafLevel,
    {paspace := .PAS_NonSecure, address := leafBase da.leafLevel da.view.stable}, da.view.stable.getLsbD 52)
  have ha := leafPA_step a.va target l i adda ina
  have hb := leafPA_step b.va target l j addb inb
  exact congrArg some (ha.symm.trans hb)

/-- A physical byte view constructed from actual translated anchors and physical offsets. -/
def anchoredView {α : Type} (mapping : BitVec 64 → Option Nat) (anchor : α → BitVec 64)
    (offset : α → Nat) (a : α) : Option Nat := (mapping (anchor a)).map (· + offset a)

/-- Physical injectivity from translated anchors only. No mapping of an interior VA is used. -/
theorem anchored_injective {α : Type} (tracked : List α) (mapping : BitVec 64 → Option Nat)
    (va anchor : α → BitVec 64) (offset : α → Nat)
    (virtual : ∀ a ∈ tracked, ∀ b ∈ tracked, a ≠ b → va a ≠ va b)
    (walk : ∀ a ∈ tracked, ∃ l : Leaf, mapping (anchor a) = some (leafPA (anchor a) l))
    (add : ∀ a ∈ tracked, (va a).toNat = (anchor a).toNat + offset a)
    (inside : ∀ a ∈ tracked, (anchor a).toNat % 4096 + offset a < 4096)
    (noDouble : ∀ a ∈ tracked, ∀ b ∈ tracked, ∀ pa pb,
      mapping (anchor a) = some pa → mapping (anchor b) = some pb → pa / 4096 = pb / 4096 →
      (anchor a).toNat / 4096 = (anchor b).toNat / 4096) :
    ∀ a ∈ tracked, ∀ b ∈ tracked, a ≠ b → ∀ pa,
      anchoredView mapping anchor offset a = some pa → anchoredView mapping anchor offset b ≠ some pa := by
  intro a ha b hb ne pa hpa hpb
  obtain ⟨la, ma⟩ := walk a ha
  obtain ⟨lb, mb⟩ := walk b hb
  have oa := leafPA_mod (anchor a) la
  have ob := leafPA_mod (anchor b) lb
  have ia := inside a ha
  have ib := inside b hb
  have aa := add a ha
  have ab := add b hb
  simp only [anchoredView, ma, mb, Option.map_some, Option.some.injEq] at hpa hpb
  have da := Nat.div_add_mod (leafPA (anchor a) la) 4096
  have db := Nat.div_add_mod (leafPA (anchor b) lb) 4096
  have sameFrame : leafPA (anchor a) la / 4096 = leafPA (anchor b) lb / 4096 := by omega
  have samePage := noDouble a ha b hb _ _ ma mb sameFrame
  have vaa := Nat.div_add_mod (anchor a).toNat 4096
  have vab := Nat.div_add_mod (anchor b).toNat 4096
  apply virtual a ha b hb ne
  apply BitVec.eq_of_toNat_eq
  omega

#print axioms access_spans_agree
#print axioms anchored_injective
#print axioms leafPA_step
#print axioms access_start_step
#print axioms access_leaf_unique
#print axioms observed_unique_of_image
#print axioms observed_unique
#print axioms path_unique
end TranslateSpan
