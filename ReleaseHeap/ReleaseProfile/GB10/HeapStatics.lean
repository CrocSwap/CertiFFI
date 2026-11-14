import ArmCertTranslateModel.C9TranslateBinding
import RtShim2.ShimMem
import HeapV2StepCerts.CodeScope
import HeapV2StepCerts.C3Core
import RtShim2.SlotPrem
import MemReloc.Placement
import ArmCertWalk.MemPair
import HeapV2StepCerts.Residue.Core
import ArmCertTranslateModel.C9Checks

set_option autoImplicit false

/-!
# Generic static-atom checkers for the Heap positive C2

Program/memory-data facts only (code offsets vs physical byte sets); no register, feature or
configuration value appears. Each lemma turns a finite Bool check into the card's static atom, so on a
concrete world payload the atom closes by `decide`. Re-homed generically from the ControlRows witness proofs
(HeapV2Witness.sep_union / bodyAvoids), which were specific to synthetic data.
-/

namespace ReleaseProfile.GB10.HeapStatics

open ArmCert.Translate.Model

/-- Separation over a union of two code scopes from separation over each. -/
theorem sep_union {s1 s2 : Nat → Prop} {base : MemReloc.Word} {mapping : MemReloc.Mapping}
    {table : Nat → Prop} (h1 : ImageTableSeparated s1 base mapping table)
    (h2 : ImageTableSeparated s2 base mapping table) :
    ImageTableSeparated (fun o => s1 o ∨ s2 o) base mapping table := by
  intro o pa hsc hm ht
  rcases hsc with h | h
  · exact h1 o pa h hm ht
  · exact h2 o pa h hm ht

/-- Every listed code offset maps outside the physical interval [lo, lo + len). -/
def offsetsAvoid (offs : List Nat) (base : MemReloc.Word) (mapping : MemReloc.Mapping)
    (lo len : Nat) : Bool :=
  offs.all fun o => match mapping (MemReloc.imageAddress base o) with
    | none => true
    | some pa => decide (pa < lo ∨ lo + len ≤ pa)

theorem offsetsAvoid_sound {offs : List Nat} {base : MemReloc.Word} {mapping : MemReloc.Mapping}
    {lo len : Nat} (h : offsetsAvoid offs base mapping lo len = true) :
    ∀ o pa, o ∈ offs → mapping (MemReloc.imageAddress base o) = some pa → pa < lo ∨ lo + len ≤ pa := by
  intro o pa ho hm
  have := List.all_eq_true.1 h o ho
  simp only [hm, decide_eq_true_eq] at this
  exact this

/-- Code bytes at the listed offsets are separated from the 16-byte shim slot, given where the slot maps. -/
theorem sep_slot_of_avoid {offs : List Nat} {base : MemReloc.Word} {mapping : MemReloc.Mapping}
    {pins : HeapV2E17.Pins} {n : Nat} (hsp : mapping (BitVec.ofNat 64 pins.sp) = some n)
    (chk : offsetsAvoid offs base mapping n 16 = true) :
    ImageTableSeparated (· ∈ offs) base mapping (RtShim2.ShimMem.slotBytes pins mapping) := by
  intro o pa ho hm slot
  obtain ⟨m, hm2, lo, hi⟩ := slot
  rw [hsp] at hm2
  cases hm2
  rcases offsetsAvoid_sound chk o pa ho hm with h | h <;> omega

/-- The body code scope is list membership, so `offsetsAvoid HeapV2StepCerts.codeOffsets` covers it. -/
theorem codeScope_iff (o : Nat) : HeapV2StepCerts.codeScope o ↔ o ∈ HeapV2StepCerts.codeOffsets := Iff.rfl

/-! ## Memory presence from a byte plan (payload memory built from an (address, byte) list) -/

/-- The state's memory realizes every entry of a byte plan. -/
def Realizes (plan : List (Nat × BitVec 8)) (s : ArmBridge.Draft.NativeState) : Prop :=
  ∀ a b, (a, b) ∈ plan → s.mem[a]? = some b

/-- The plan holds some byte at address `a`. -/
def planHas (plan : List (Nat × BitVec 8)) (a : Nat) : Bool := plan.any fun x => x.1 == a

theorem present_of_planHas {plan : List (Nat × BitVec 8)} {s : ArmBridge.Draft.NativeState}
    (real : Realizes plan s) {a : Nat} (h : planHas plan a = true) : (s.mem[a]?).isSome := by
  obtain ⟨⟨a', b⟩, mem, eq⟩ := List.any_eq_true.1 h
  have : a' = a := by simpa using eq
  subst this
  rw [real _ _ mem]; rfl

/-- Shim slot presence check: the 16 slot bytes are planned (vacuous if the slot VA is unmapped). -/
def checkSlotPresent (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat)
    (plan : List (Nat × BitVec 8)) : Bool :=
  match mapping (BitVec.ofNat 64 pins.sp) with
  | none => true
  | some n => (List.range 16).all fun i => planHas plan (n + i)

theorem slotPresent_of_check {pins : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat}
    {plan : List (Nat × BitVec 8)} {s : ArmBridge.Draft.NativeState} (real : Realizes plan s)
    (chk : checkSlotPresent pins mapping plan = true) : RtShim.SlotPrem.ShimSlotPresent pins mapping s := by
  intro n hn i hi
  unfold checkSlotPresent at chk
  rw [hn] at chk
  exact present_of_planHas real (List.all_eq_true.1 chk i (List.mem_range.2 hi))

/-- Data presence check over the plan's symbolic accesses. -/
def checkDataPresent (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat)
    (plan : List (Nat × BitVec 8)) : Bool :=
  HeapV2Plan.symbolicAccesses.all fun e =>
    match mapping (HeapV2E17.dataVA pins e) with
    | none => true
    | some n => (List.range e.2.2.2.1).all fun i => planHas plan (n + i)

theorem dataPresent_of_check {pins : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat}
    {plan : List (Nat × BitVec 8)} {s : ArmBridge.Draft.NativeState} (real : Realizes plan s)
    (chk : checkDataPresent pins mapping plan = true) : HeapV2StepCerts.C3.DataPresent pins mapping s := by
  intro e he n hn i hi
  have h := List.all_eq_true.1 chk e he
  simp only [hn] at h
  exact present_of_planHas real (List.all_eq_true.1 h i (List.mem_range.2 hi))

/-- Image placement check over a list-membership scope. -/
def checkImageOn (offs : List Nat) (image : MemReloc.Image) (base : MemReloc.Word)
    (mapping : MemReloc.Mapping) (plan : List (Nat × BitVec 8)) : Bool :=
  offs.all fun o => match image o, mapping (MemReloc.imageAddress base o) with
    | some byte, some pa => plan.contains (pa, byte)
    | _, _ => false

theorem imageOn_of_check {offs : List Nat} {image : MemReloc.Image} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {plan : List (Nat × BitVec 8)} {s : ArmBridge.Draft.NativeState}
    (real : Realizes plan s) (chk : checkImageOn offs image base mapping plan = true) :
    MemReloc.ImageOn (· ∈ offs) image s base mapping := by
  intro o ho
  have h := List.all_eq_true.1 chk o ho
  cases hi : image o with
  | none => simp [hi] at h
  | some byte =>
    cases hm : mapping (MemReloc.imageAddress base o) with
    | none => simp [hi, hm] at h
    | some pa =>
      simp only [hi, hm] at h
      exact ⟨byte, pa, rfl, rfl, real _ _ (by simpa using h)⟩

/-! ## Union scopes (shim code ∪ body code), as the Heap world's scope -/

theorem imageOn_union {s1 s2 : Nat → Prop} {image : MemReloc.Image} {st : ArmBridge.Draft.NativeState}
    {base : MemReloc.Word} {mapping : MemReloc.Mapping}
    (h1 : MemReloc.ImageOn s1 image st base mapping) (h2 : MemReloc.ImageOn s2 image st base mapping) :
    MemReloc.ImageOn (fun o => s1 o ∨ s2 o) image st base mapping := by
  intro o ho
  rcases ho with h | h
  · exact h1 o h
  · exact h2 o h

/-- Atom shape `codeSlot` (normal input 20) for a scope given as two offset lists. -/
theorem codeSlot_of_checks {shimOffs bodyOffs : List Nat} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {pins : HeapV2E17.Pins} {n : Nat}
    (hsp : mapping (BitVec.ofNat 64 pins.sp) = some n)
    (c1 : offsetsAvoid shimOffs base mapping n 16 = true) (c2 : offsetsAvoid bodyOffs base mapping n 16 = true) :
    ImageTableSeparated (fun o => o ∈ shimOffs ∨ o ∈ bodyOffs) base mapping (RtShim2.ShimMem.slotBytes pins mapping) :=
  sep_union (sep_slot_of_avoid hsp c1) (sep_slot_of_avoid hsp c2)

/-- Atom shape `inv0_placed` (normal input 123) for a two-list scope. -/
theorem placed_of_checks {shimOffs bodyOffs : List Nat} {image : MemReloc.Image} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {plan : List (Nat × BitVec 8)} {st : ArmBridge.Draft.NativeState}
    (real : Realizes plan st) (c1 : checkImageOn shimOffs image base mapping plan = true)
    (c2 : checkImageOn bodyOffs image base mapping plan = true) :
    MemReloc.ImageOn (fun o => o ∈ shimOffs ∨ o ∈ bodyOffs) image st base mapping :=
  imageOn_union (imageOn_of_check real c1) (imageOn_of_check real c2)

/-! ## Plan segments -/

theorem Realizes.mono {sub plan : List (Nat × BitVec 8)} {s : ArmBridge.Draft.NativeState}
    (h : Realizes plan s) (incl : ∀ x ∈ sub, x ∈ plan) : Realizes sub s :=
  fun a b m => h a b (incl _ m)

theorem Realizes.left {l r : List (Nat × BitVec 8)} {s : ArmBridge.Draft.NativeState}
    (h : Realizes (l ++ r) s) : Realizes l s := h.mono fun _ m => List.mem_append_left _ m

theorem Realizes.right {l r : List (Nat × BitVec 8)} {s : ArmBridge.Draft.NativeState}
    (h : Realizes (l ++ r) s) : Realizes r s := h.mono fun _ m => List.mem_append_right _ m

/-- Image placement by construction: a plan segment built from the image over the offset list. -/
def imagePlanOf (offs : List Nat) (image : MemReloc.Image) (base : MemReloc.Word)
    (mapping : MemReloc.Mapping) : List (Nat × BitVec 8) :=
  offs.filterMap fun o => match image o, mapping (MemReloc.imageAddress base o) with
    | some b, some pa => some (pa, b)
    | _, _ => none

/-- Placement holds when every scoped offset has an image byte and a mapping (a cheap check: no plan scan). -/
def checkImageDefined (offs : List Nat) (image : MemReloc.Image) (base : MemReloc.Word)
    (mapping : MemReloc.Mapping) : Bool :=
  offs.all fun o => (image o).isSome && (mapping (MemReloc.imageAddress base o)).isSome

theorem imageOn_of_imagePlan {offs : List Nat} {image : MemReloc.Image} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {s : ArmBridge.Draft.NativeState}
    (real : Realizes (imagePlanOf offs image base mapping) s)
    (chk : checkImageDefined offs image base mapping = true) :
    MemReloc.ImageOn (· ∈ offs) image s base mapping := by
  intro o ho
  have h := List.all_eq_true.1 chk o ho
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨b, hb⟩, ⟨pa, hpa⟩⟩ := h
  refine ⟨b, pa, hb, hpa, real _ _ ?_⟩
  unfold imagePlanOf
  exact List.mem_filterMap.2 ⟨o, ho, by simp [hb, hpa]⟩

/-! ## Store intervals, store/slot separation, slot statics (re-homed generically from TranslateShim.Deploy,
whose versions are fixed to the synthetic shim offsets) -/

/-- PA intervals of the body's write accesses, exactly as `RtSaved.accPA` counts them. -/
def storeIntervals (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins) : List (Nat × Nat) :=
  (HeapV2Plan.symbolicAccesses.filter (·.2.2.2.2)).flatMap fun e =>
    ((mapping (HeapV2E17.dataVA pins e)).map fun n => (n, e.2.2.2.1)).toList ++
      (if e.2.2.2.1 = 16 then ((mapping (ArmCertWalk.plus8 (HeapV2E17.dataVA pins e))).map fun n => (n, 8)).toList
       else [])

theorem storeBytes_interval {mapping : BitVec 64 → Option Nat} {pins : HeapV2E17.Pins} {y : Nat}
    (h : HeapV2StepCerts.Residue.StoreBytes pins mapping y) :
    ∃ iv ∈ storeIntervals mapping pins, iv.1 ≤ y ∧ y < iv.1 + iv.2 := by
  obtain ⟨e, member, hw, acc⟩ := h
  have mf : e ∈ HeapV2Plan.symbolicAccesses.filter (·.2.2.2.2) := List.mem_filter.2 ⟨member, by simp [hw]⟩
  rcases acc with ⟨n, hm, lo, hi⟩ | ⟨h16, n, hm, lo, hi⟩
  · exact ⟨(n, e.2.2.2.1), List.mem_flatMap.2 ⟨e, mf, List.mem_append_left _ (by simp [hm])⟩, lo, hi⟩
  · exact ⟨(n, 8), List.mem_flatMap.2 ⟨e, mf, List.mem_append_right _ (by simp [hm, h16])⟩, lo, hi⟩

/-- Code bytes at the listed offsets avoid every body store interval. -/
def checkCodeStore (offs : List Nat) (base : MemReloc.Word) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) : Bool :=
  (storeIntervals mapping pins).all fun iv => offsetsAvoid offs base mapping iv.1 iv.2

theorem codeStore_of_check {offs : List Nat} {base : MemReloc.Word} {mapping : BitVec 64 → Option Nat}
    {pins : HeapV2E17.Pins} (h : checkCodeStore offs base mapping pins = true) :
    ImageTableSeparated (· ∈ offs) base mapping (HeapV2StepCerts.Residue.StoreBytes pins mapping) := by
  intro o pa inside mapped store
  obtain ⟨iv, member, lo, hi⟩ := storeBytes_interval store
  rcases offsetsAvoid_sound (List.all_eq_true.1 h iv member) o pa inside mapped with h | h <;> omega

/-- The 16-byte shim slot is disjoint from every body store interval. -/
def checkSlotStoreSep (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins) : Bool :=
  match mapping (BitVec.ofNat 64 pins.sp) with
  | none => true
  | some n => (storeIntervals mapping pins).all fun iv => decide (n + 16 ≤ iv.1 ∨ iv.1 + iv.2 ≤ n)

theorem slotStoreSep_of_check {mapping : BitVec 64 → Option Nat} {pins : HeapV2E17.Pins}
    (h : checkSlotStoreSep mapping pins = true) :
    ∀ a, RtShim2.ShimMem.slotBytes pins mapping a → ¬ HeapV2StepCerts.Residue.StoreBytes pins mapping a := by
  intro a slot store
  obtain ⟨n, hn, lo, hi⟩ := slot
  simp only [checkSlotStoreSep, hn] at h
  obtain ⟨iv, member, lo', hi'⟩ := storeBytes_interval store
  have := List.all_eq_true.1 h iv member
  simp only [decide_eq_true_eq] at this
  omega

/-- Shim slot statics: mapped below 2^56, not MMIO, outside the table footprint, upper half mapped. -/
def checkSlotStatic (fp : ArmCert.Translate.Footprint) (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins) : Bool :=
  match mapping (BitVec.ofNat 64 pins.sp) with
  | none => false
  | some n => decide (n + 16 < 2 ^ 56) && checkMappedNotMMIO mapping (BitVec.ofNat 64 pins.sp) &&
      (List.range 16).all (fun i => fp.slots.all fun s => decide (n + i < s ∨ s + fp.width ≤ n + i)) &&
      decide (mapping (ArmCertWalk.plus8 (BitVec.ofNat 64 pins.sp)) = some (n + 8)) &&
      checkMappedNotMMIO mapping (ArmCertWalk.plus8 (BitVec.ofNat 64 pins.sp))

theorem slotStatic_of_check {fp : ArmCert.Translate.Footprint} {mapping : BitVec 64 → Option Nat}
    {pins : HeapV2E17.Pins} (h : checkSlotStatic fp mapping pins = true) :
    RtShim.SlotPrem.ShimSlotStatic pins mapping fp := by
  unfold checkSlotStatic at h
  split at h
  · cases h
  · next n hn =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨bound, mmio⟩, outside⟩, upper⟩, mmio8⟩ := h
    have hnat : (BitVec.ofNat 56 n).toNat = n := by simp [BitVec.toNat_ofNat]; omega
    have hm : mapping (BitVec.ofNat 64 pins.sp) = some (BitVec.ofNat 56 n).toNat := by rw [hnat]; exact hn
    have hu : mapping (ArmCertWalk.plus8 (BitVec.ofNat 64 pins.sp)) = some ((BitVec.ofNat 56 n).toNat + 8) := by
      rw [hnat]; exact upper
    have hb : (BitVec.ofNat 56 n).toNat + 16 < 2 ^ 56 := by rw [hnat]; exact bound
    refine ⟨BitVec.ofNat 56 n, ⟨hb, hm, checkMappedNotMMIO_sound mmio _ hm, ?_,
      fun _ => ⟨hu, checkMappedNotMMIO_sound mmio8⟩⟩⟩
    intro i small inFp
    rw [hnat] at inFp
    obtain ⟨s, member, lo, hi⟩ := inFp
    have := List.all_eq_true.1 (List.all_eq_true.1 outside i (List.mem_range.2 small)) s member
    simp only [decide_eq_true_eq] at this
    omega

end ReleaseProfile.GB10.HeapStatics

#print axioms ReleaseProfile.GB10.HeapStatics.sep_union
#print axioms ReleaseProfile.GB10.HeapStatics.offsetsAvoid_sound
#print axioms ReleaseProfile.GB10.HeapStatics.sep_slot_of_avoid
#print axioms ReleaseProfile.GB10.HeapStatics.slotPresent_of_check
#print axioms ReleaseProfile.GB10.HeapStatics.dataPresent_of_check
#print axioms ReleaseProfile.GB10.HeapStatics.imageOn_of_check
#print axioms ReleaseProfile.GB10.HeapStatics.codeSlot_of_checks
#print axioms ReleaseProfile.GB10.HeapStatics.placed_of_checks
#print axioms ReleaseProfile.GB10.HeapStatics.imageOn_of_imagePlan
#print axioms ReleaseProfile.GB10.HeapStatics.codeStore_of_check
#print axioms ReleaseProfile.GB10.HeapStatics.slotStoreSep_of_check
#print axioms ReleaseProfile.GB10.HeapStatics.slotStatic_of_check
