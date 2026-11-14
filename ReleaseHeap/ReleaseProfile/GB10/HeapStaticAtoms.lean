import ReleaseProfile.GB10.HeapC2World
import ReleaseProfile.GB10.HeapStatics
import ArmCertTranslateModel.C9Checks
import TranslateShim.ShimFetch
import HeapV2StepCerts.Carry
import HeapV2StepCerts.CodeData
import NativeBodyDeploy.Assemble
import RtSaved.SlotCore
import TranslateMem.WalkE17

set_option autoImplicit false
set_option maxHeartbeats 400000

/-!
# Heap normal positive C2: static atoms at a world

Each lemma proves one static atom of `NormalResidual` for any `HeapWorld` from finite checks on the
world's program/memory data, a scope description (shim offsets ∪ body code offsets) and plan inclusion
(the world plan contains the checked sub-plan; provides it structurally from the plan definition).
On the concrete world every check closes by `decide`. No register or configuration value is involved.
Atoms 259/268/269/272/273/274 use existing generic lemmas directly (slot_static, TranslateShim.Deploy,
DataBytesLinear decide, TranslateMem walk lemmas) and need no wrapper here.
-/

namespace ReleaseProfile.GB10.Heap.Statics

open ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.HeapStatics ArmCert.Translate.Model

/-- The world scope is exactly the shim offsets and the body code offsets. -/
def ScopeIs (w : HeapWorld) (shimOffs : List Nat) : Prop :=
  ∀ o, w.scope o ↔ (o ∈ shimOffs ∨ o ∈ HeapV2StepCerts.codeOffsets)

theorem realizes_world (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (w : HeapWorld) (pcount : BitVec 88) : Realizes w.plan (worldEntry sem rho caller w pcount) :=
  fun a b m => world_realizes sem rho caller w pcount (a, b) m

theorem sep_mono {s t : Nat → Prop} {base : MemReloc.Word} {mapping : MemReloc.Mapping}
    {table : Nat → Prop} (h : ∀ o, s o → t o) (sep : ImageTableSeparated t base mapping table) :
    ImageTableSeparated s base mapping table :=
  fun o pa ho hm ht => sep o pa (h o ho) hm ht

theorem imageOn_mono {s t : Nat → Prop} {image : MemReloc.Image} {st : ArmBridge.Draft.NativeState}
    {base : MemReloc.Word} {mapping : MemReloc.Mapping} (h : ∀ o, s o → t o)
    (on : MemReloc.ImageOn t image st base mapping) : MemReloc.ImageOn s image st base mapping :=
  fun o ho => on o (h o ho)

/-- Atom 20 (`codeSlot`). -/
theorem atom20 (w : HeapWorld) {shimOffs : List Nat} (hsc : ScopeIs w shimOffs) {n : Nat}
    (hsp : w.mapping (BitVec.ofNat 64 w.pins.sp) = some n)
    (c1 : offsetsAvoid shimOffs w.loadBase w.mapping n 16 = true)
    (c2 : offsetsAvoid HeapV2StepCerts.codeOffsets w.loadBase w.mapping n 16 = true) :
    ImageTableSeparated w.scope w.loadBase w.mapping (RtShim2.ShimMem.slotBytes w.pins w.mapping) :=
  sep_mono (fun o h => (hsc o).1 h) (codeSlot_of_checks hsp c1 c2)

/-- Atom 263 (`hscope`). -/
theorem atom263 (w : HeapWorld) {shimOffs : List Nat} (hsc : ScopeIs w shimOffs) :
    ∀ o, HeapV2StepCerts.codeScope o → w.scope o :=
  fun o h => (hsc o).2 (Or.inr h)

/-- Atom 123 (`inv0_placed`): image placement at the world entry. -/
theorem atom123 (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (w : HeapWorld) (pcount : BitVec 88) {shimOffs : List Nat} (hsc : ScopeIs w shimOffs)
    (himg : w.imagePlan = imagePlanOf (shimOffs ++ HeapV2StepCerts.codeOffsets) w.image w.loadBase w.mapping)
    (chk : checkImageDefined (shimOffs ++ HeapV2StepCerts.codeOffsets) w.image w.loadBase w.mapping = true) :
    MemReloc.ImageOn w.scope w.image (worldEntry sem rho caller w pcount) w.loadBase w.mapping :=
  imageOn_mono (fun o h => List.mem_append.2 ((hsc o).1 h))
    (imageOn_of_imagePlan (himg ▸ fun a b m => world_realizes_image sem rho caller w pcount (a, b) m) chk)

/-- Atom 257 (`slotE`): the shim slot bytes are present at the world entry. -/
theorem atom257 (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (w : HeapWorld) (pcount : BitVec 88) (chk : checkSlotPresent w.pins w.mapping w.slotPlan = true) :
    RtShim.SlotPrem.ShimSlotPresent w.pins w.mapping (worldEntry sem rho caller w pcount) :=
  slotPresent_of_check (fun a b m => world_realizes_slot sem rho caller w pcount (a, b) m) chk

/-- Atom 264 (`presentE`): plan data bytes are present at the world entry. -/
theorem atom264 (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (w : HeapWorld) (pcount : BitVec 88) (chk : checkDataPresent w.pins w.mapping w.dataPlan = true) :
    HeapV2StepCerts.C3.DataPresent w.pins w.mapping (worldEntry sem rho caller w pcount) :=
  dataPresent_of_check (fun a b m => world_realizes_data sem rho caller w pcount (a, b) m) chk

/-- Shim code words lie in the shim offsets. -/
def checkShimInside (shimOffs : List Nat) : Bool :=
  HeapV2ShimPlan.codeWords.all fun c => (List.range 4).all fun i => decide (HeapV2ShimPlan.shimOffset + c.1 + i ∈ shimOffs)

/-- Atom 245 (`shimStatic`). -/
theorem atom245 (w : HeapWorld) {shimOffs : List Nat} (hsc : ScopeIs w shimOffs) (fp : ArmCert.Translate.Footprint)
    (csep : checkImageTableSeparated w.base w.mapping (shimOffs ++ HeapV2StepCerts.codeOffsets) fp = true)
    (cin : checkShimInside shimOffs = true)
    (ccont : HeapV2ShimPlan.codeWords.all (fun c => checkImageWordContiguous w.mapping w.base (HeapV2ShimPlan.shimOffset + c.1)) = true)
    (cmmio : HeapV2ShimPlan.codeWords.all (fun c => checkMappedNotMMIO w.mapping
      (MemReloc.imageAddress w.base (HeapV2ShimPlan.shimOffset + c.1))) = true) :
    RtDit.ShimFetch.ShimCodeStatic w.mapping w.base w.scope fp.byte where
  separated := sep_mono (fun o h => List.mem_append.2 ((hsc o).1 h)) (checkImageTableSeparated_sound csep)
  inside := fun c m i hi => (hsc _).2 (Or.inl (of_decide_eq_true
    (List.all_eq_true.1 (List.all_eq_true.1 cin c m) i (List.mem_range.2 hi))))
  contiguous := fun c m => checkImageWordContiguous_sound (List.all_eq_true.1 ccont c m)
  notMMIO := fun c m => checkMappedNotMMIO_sound (List.all_eq_true.1 cmmio c m)

/-- Atom 261 (`E_S`, BodyStatic) from the generic checkers; `agrees` is consumer-map lemma. -/
theorem atom261 {domain : QueryDomain} (spec : TopologyImageSpec domain) (w : HeapWorld)
    (csep : checkImageTableSeparated w.base w.mapping HeapV2StepCerts.codeOffsets (rowsFootprint spec.imageRows) = true)
    (ccont : HeapV2StepCerts.checkCodeContiguous w.mapping w.base = true)
    (cmmio : HeapV2StepCerts.checkCodeNotMMIO w.mapping w.base = true)
    (cdata : HeapV2StepCerts.C3.DataStatic w.pins w.mapping (rowsFootprint spec.imageRows))
    (calign : ∀ i, HeapV2E17.pin w.pins i % 16 = 0)
    (ccode : HeapV2StepCerts.MemNext.checkCodeDataDisjoint w.pins w.mapping w.base = true)
    (cslot : RtSaved.slotSepCheck w.pins w.mapping = true)
    (cmapped : ∃ n, w.mapping (RtSaved.slotVA w.pins) = some n)
    (cpage : w.base.toNat % 4096 = 0) (clow : w.base.toNat < 2 ^ 54)
    (agrees : ConsumerMapAgrees spec w.mapping (HeapV2StepCerts.E17General.cmap spec w.mapping w.base w.pins))
    (cnodup : (spec.logicalRows.map (·.logical)).Nodup) :
    NativeBodyDeploy.BodyStatic spec w.mapping w.base w.pins where
  static := HeapV2StepCerts.codeStatic_of_checks w.mapping w.base _ csep ccont cmmio
  dataStatic := cdata
  pinAligned := calign
  codeD := HeapV2StepCerts.MemNext.codeD_of_check ccode
  sep := RtSaved.slotSep_of_check cslot
  mapped := cmapped
  page := cpage
  low := clow
  agrees := agrees
  nodup := cnodup

/-- Atom 268 (`codeStore`): scoped code bytes avoid the body store bytes. -/
theorem atom268 (w : HeapWorld) {shimOffs : List Nat} (hsc : ScopeIs w shimOffs)
    (c1 : checkCodeStore shimOffs w.base w.mapping w.pins = true)
    (c2 : checkCodeStore HeapV2StepCerts.codeOffsets w.base w.mapping w.pins = true) :
    ImageTableSeparated w.scope w.base w.mapping (HeapV2StepCerts.Residue.StoreBytes w.pins w.mapping) :=
  sep_mono (fun o h => (hsc o).1 h) (sep_union (codeStore_of_check c1) (codeStore_of_check c2))

/-- Atom 269 (`slotStore`). -/
theorem atom269 (w : HeapWorld) (chk : checkSlotStoreSep w.mapping w.pins = true) :
    ∀ a, RtShim2.ShimMem.slotBytes w.pins w.mapping a → ¬ HeapV2StepCerts.Residue.StoreBytes w.pins w.mapping a :=
  slotStoreSep_of_check chk

/-- Atom 259 (`static`). -/
theorem atom259 {domain : QueryDomain} (spec : TopologyImageSpec domain) (w : HeapWorld)
    (chk : checkSlotStatic (rowsFootprint spec.imageRows) w.mapping w.pins = true) :
    RtShim.SlotPrem.ShimSlotStatic w.pins w.mapping (rowsFootprint spec.imageRows) :=
  slotStatic_of_check chk

/-! ## Atoms 273/274: functional region injectivity and input/slot separation via the page walk -/

/-- No two tracked bytes on different VA pages share a physical page (finite check). -/
def checkNoDoubleMapPA (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : Bool :=
  ArmCertValue.HeapV2Mem.heapv2Bytes.all fun a => ArmCertValue.HeapV2Mem.heapv2Bytes.all fun b =>
    match mapping (ArmCertValue.HeapV2Mem.byteVA pins a.1 a.2), mapping (ArmCertValue.HeapV2Mem.byteVA pins b.1 b.2) with
    | some n, some m => !(n / 4096 == m / 4096) ||
        (TranslateMem.pageOf (ArmCertValue.HeapV2Mem.byteVA pins a.1 a.2) == TranslateMem.pageOf (ArmCertValue.HeapV2Mem.byteVA pins b.1 b.2))
    | _, _ => true

theorem noDoubleMapPA_of_check {pins : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat}
    (chk : checkNoDoubleMapPA pins mapping = true) : TranslateMem.NoDoubleMapPA pins mapping := by
  intro a ha b hb n m h1 h2 h3
  have := List.all_eq_true.1 (List.all_eq_true.1 chk a ha) b hb
  simp only [h1, h2, h3, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  exact this

/-- No input-buffer byte shares a physical page with the slot unless on the slot's VA page (finite check). -/
def checkNoDoubleMapSlot (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : Bool :=
  (List.range 32).all fun j => match mapping (BitVec.ofNat 64 (pins.x1 + j)), mapping (BitVec.ofNat 64 pins.sp) with
    | some q, some n => !(q / 4096 == n / 4096) || ((pins.x1 + j) / 4096 == pins.sp / 4096)
    | _, _ => true

theorem noDoubleMapSlot_of_check {pins : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat}
    (chk : checkNoDoubleMapSlot pins mapping = true) : TranslateMem.NoDoubleMapSlot pins mapping := by
  intro j hj q n h1 h2 h3
  have := List.all_eq_true.1 chk j (List.mem_range.2 hj)
  simp only [h1, h2, h3, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  exact this

/-- Every plan data access is leaf-mapped, from closed membership over the shim consumer map. -/
theorem accessLeaf_of_closed {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : ArmCertWalk.AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {base : BitVec 64} {pins : HeapV2E17.Pins} {e : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping
      (ArmBridge.CruxGenGuarded.Release.shimMap spec mapping base pins) e) :
    TranslateMem.AccessLeaf pins mapping := by
  intro access member
  exact TranslateMem.leaf_of_closed closed (acc := TranslateMem.dataAcc access.2.2.2.2)
    (aligned := true) (size := (access.2.2.2.1 : Int))
    (Or.inl (Or.inl ⟨access, member, trivial, rfl, rfl, TranslateMem.dataAcc_shape _⟩))

theorem slotLeaf_of_closed' {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : ArmCertWalk.AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {base : BitVec 64} {pins : HeapV2E17.Pins} {e : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping
      (ArmBridge.CruxGenGuarded.Release.shimMap spec mapping base pins) e) :
    TranslateMem.SlotLeaf pins mapping :=
  TranslateMem.slotLeaf_of_closed pins closed (acc := TranslateMem.dataAcc false)
    (aligned := true) (size := 16) (Or.inr (Or.inr ⟨false, rfl, rfl, TranslateMem.dataAcc_shape _⟩))

/-- Atom 273 (`inj`). -/
theorem atom273 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : ArmCertWalk.AttributeConfig} (w : HeapWorld) {e : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config w.rows w.mapping
      (ArmBridge.CruxGenGuarded.Release.shimMap spec w.mapping w.base w.pins) e)
    (hd : TranslateMem.RegionsDisjoint w.pins)
    (aligned : w.pins.sp % 16 = 0 ∧ w.pins.x0 % 16 = 0 ∧ w.pins.x1 % 16 = 0)
    (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear w.pins w.mapping)
    (cnd : checkNoDoubleMapPA w.pins w.mapping = true) :
    ArmCertValue.HeapV2Mem.RegionsInjective w.pins w.mapping :=
  TranslateMem.regionsInjective_of_walk w.pins w.mapping hd aligned (accessLeaf_of_closed closed) dbl
    (noDoubleMapPA_of_check cnd)

/-- Atom 274 (`inputNoSlot`). -/
theorem atom274 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : ArmCertWalk.AttributeConfig} (w : HeapWorld) {e : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config w.rows w.mapping
      (ArmBridge.CruxGenGuarded.Release.shimMap spec w.mapping w.base w.pins) e)
    (hd : TranslateMem.RegionsDisjoint w.pins)
    (aligned : w.pins.sp % 16 = 0 ∧ w.pins.x0 % 16 = 0 ∧ w.pins.x1 % 16 = 0)
    (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear w.pins w.mapping)
    (cnd : checkNoDoubleMapSlot w.pins w.mapping = true)
    (slotDisj : w.pins.x1 + 32 ≤ w.pins.sp ∨ w.pins.sp + 16 ≤ w.pins.x1) (spHi : w.pins.sp + 16 ≤ 2 ^ 64) :
    ∀ i, i < 32 → ∀ n, w.mapping (BitVec.ofNat 64 (w.pins.x1 + i)) = some n →
      ¬ RtShim2.ShimMem.slotBytes w.pins w.mapping n :=
  TranslateMem.slotSep_of_walk w.pins w.mapping hd aligned (accessLeaf_of_closed closed) dbl
    (slotLeaf_of_closed' closed) (noDoubleMapSlot_of_check cnd) slotDisj spHi

end ReleaseProfile.GB10.Heap.Statics

#print axioms ReleaseProfile.GB10.Heap.Statics.atom20
#print axioms ReleaseProfile.GB10.Heap.Statics.atom123
#print axioms ReleaseProfile.GB10.Heap.Statics.atom245
#print axioms ReleaseProfile.GB10.Heap.Statics.atom257
#print axioms ReleaseProfile.GB10.Heap.Statics.atom261
#print axioms ReleaseProfile.GB10.Heap.Statics.atom263
#print axioms ReleaseProfile.GB10.Heap.Statics.atom264
#print axioms ReleaseProfile.GB10.Heap.Statics.atom268
#print axioms ReleaseProfile.GB10.Heap.Statics.atom269
#print axioms ReleaseProfile.GB10.Heap.Statics.atom259
#print axioms ReleaseProfile.GB10.Heap.Statics.atom273
#print axioms ReleaseProfile.GB10.Heap.Statics.atom274
