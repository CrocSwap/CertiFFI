import DitShim243.DataFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open TranslateSpan TranslateSpan.SecpRawDeployment ArmCertValue ArmCertPipe HeapV2StepCerts NativeMteTagCheck ReleaseProfile
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace DitShim243.DataTransport
open DataFrame

structure Args (p : Plan) (mapping : BitVec 64 → Option Nat) (before after : NativeState) : Prop where
  gp : ∀ r ∈ sources p ++ (sources p).map p.normalize, entryGPR after r.pin = entryGPR before r.pin
  access : ∀ a ∈ p.accesses, entryGPR after a.pin = entryGPR before a.pin
  features : after.regs.FeatureImpl = before.regs.FeatureImpl
  present : ∀ a : Nat, (before.mem[a]?).isSome = true → (after.mem[a]?).isSome = true

theorem of_pre (real : Type) [Sail.SailReal real] (L : Nat)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (start : Nat)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase base : BitVec 64)
    (offS : Nat → BitVec 64) (budget : Nat) (catalogue : ControlCatalogue) (capacity : Nat) (e : NativeState)
    (pre : Pre.ShimPreMG real L spec config rows mapping pins m start scope image loadBase base offS budget catalogue capacity e)
    (p : Plan) (checked : checkPins p = true) : Args p mapping e (stateAt real e 7) := by
  simp only [checkPins,Bool.and_eq_true] at checked
  refine ⟨?_,?_,Profiles.features pre.control7,?_⟩
  · intro r member
    obtain ⟨small,n9,n30⟩ := of_decide_eq_true (List.all_eq_true.mp checked.1 r member)
    exact DataFrame.gpr real L spec config rows mapping pins m start scope image loadBase base offS budget catalogue capacity e pre r.pin small n9 n30
  · intro a member
    obtain ⟨small,n9,n30⟩ := of_decide_eq_true (List.all_eq_true.mp checked.2 a member)
    exact DataFrame.gpr real L spec config rows mapping pins m start scope image loadBase base offS budget catalogue capacity e pre a.pin small n9 n30
  · exact DataFrame.present real L spec config rows mapping pins m start scope image loadBase base offS budget catalogue capacity e pre

theorem span_view (viewA viewB : Physical.BytePA) (r : Region) (word : Nat)
    (mapping : BitVec 64 → Option Nat) (start : BitVec 64)
    (same : ∀ j, viewB r j = viewA r j) (old : SelectedBinding.At viewA r word mapping start) :
    SelectedBinding.At viewB r word mapping start := by
  cases selected : NativeAccess.PairGeometry.selected start with
  | one16 =>
    simp only [SelectedBinding.At,selected] at old ⊢
    intro pa mapped i hi
    rw [same]; exact old pa mapped i hi
  | two8 =>
    simp only [SelectedBinding.At,selected] at old ⊢
    intro j pa mapped i hi
    rw [same]; exact old j pa mapped i hi
  | bytes =>
    simp only [SelectedBinding.At,selected] at old ⊢
    intro j pa mapped
    rw [same]; exact old j pa mapped

section Args
variable {p : Plan} {mapping : BitVec 64 → Option Nat} {before after : NativeState}
    (agree : Args p mapping before after)
include agree

theorem region_used (r : Region) (member : r ∈ sources p ++ (sources p).map p.normalize) (j : Nat) :
    regionVA after r j = regionVA before r j := by
  unfold regionVA
  rw [agree.gp r member]

theorem region (r : Region) (member : r ∈ sources p) (j : Nat) : regionVA after r j = regionVA before r j :=
  region_used agree r (List.mem_append_left _ member) j

theorem view (r : Region) (member : r ∈ sources p) (j : Nat) :
    SecpRawDeployment.view p mapping after r j = SecpRawDeployment.view p mapping before r j := by
  unfold SecpRawDeployment.view
  rw [region_used agree (p.normalize r) (List.mem_append_right _ (List.mem_map.mpr ⟨r,member,rfl⟩)) j]

theorem sites : SecpRawDeployment.sites p after = SecpRawDeployment.sites p before := by
  unfold SecpRawDeployment.sites
  apply List.map_congr_left
  intro a member
  rw [agree.access a member]

theorem consumer (raw : CheckedTopology.Raw) (base : BitVec 64) :
    SecpRawDeployment.consumer p raw mapping base after = SecpRawDeployment.consumer p raw mapping base before := by
  unfold SecpRawDeployment.consumer
  rw [sites agree]

theorem selectedQueries (base : BitVec 64) :
    SecpRawDeployment.selectedQueries p base after = SecpRawDeployment.selectedQueries p base before := by
  unfold SecpRawDeployment.selectedQueries
  rw [sites agree]

omit agree in
private theorem flat_map_congr {α β : Type} (xs : List α) (f g : α → List β)
    (same : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons,List.flatMap_cons,same x (List.mem_cons_self ..)]
    exact congrArg (g x ++ ·) (ih (fun y hy => same y (List.mem_cons_of_mem _ hy)))

theorem bufferQueries : SecpRawDeployment.bufferQueries p after = SecpRawDeployment.bufferQueries p before := by
  unfold SecpRawDeployment.bufferQueries
  apply flat_map_congr
  intro row member
  obtain ⟨r,n⟩ := row
  apply List.map_congr_left
  intro j _
  rw [region agree r (buffer_member p r n member) j]

theorem queries (base : BitVec 64) : SecpRawDeployment.queries p base after = SecpRawDeployment.queries p base before := by
  unfold SecpRawDeployment.queries
  rw [selectedQueries agree base,bufferQueries agree]

theorem addresses (base : BitVec 64) : SecpRawDeployment.addresses p base after = SecpRawDeployment.addresses p base before := by
  unfold SecpRawDeployment.addresses
  rw [queries agree base]

omit agree in
private theorem fold_cost : ∀ (xs : List PairAccess),
    (∀ a ∈ xs, entryGPR after a.pin = entryGPR before a.pin) → ∀ total,
      xs.foldl (fun n a => n + DefaultBudget.cost (BitVec.addInt (entryGPR after a.pin) a.offset)) total =
      xs.foldl (fun n a => n + DefaultBudget.cost (BitVec.addInt (entryGPR before a.pin) a.offset)) total
  | [],_,_ => rfl
  | a::xs,same,total => by
    simp only [List.foldl_cons,same a (List.mem_cons_self ..)]
    exact fold_cost xs (fun b hb => same b (List.mem_cons_of_mem _ hb)) _

theorem budget (k : Nat) : DefaultBudget.before p after k = DefaultBudget.before p before k := by
  unfold DefaultBudget.before
  apply fold_cost
  intro a member
  exact agree.access a (List.mem_filter.mp member).1

theorem profile : SecpRawDeployment.profile after = SecpRawDeployment.profile before := by
  unfold SecpRawDeployment.profile
  rw [agree.features]

theorem outputBytes : SecpRawDeployment.outputBytes p mapping after = SecpRawDeployment.outputBytes p mapping before := by
  unfold SecpRawDeployment.outputBytes
  apply flat_map_congr
  intro row member
  obtain ⟨r,n⟩ := row
  have same : SecpRawDeployment.view p mapping after r = SecpRawDeployment.view p mapping before r :=
    funext (view agree r (output_member p r n member))
  simp only [StaticLayout.outputPAs,same]

omit agree in
private theorem tracked_region {regions : List Region} {a : Region × Nat} (member : a ∈ Physical.trackedBytes regions) : a.1 ∈ regions := by
  obtain ⟨r,hr,rest⟩ := List.mem_flatMap.mp member
  obtain ⟨j,hj,pair⟩ := List.mem_map.mp rest
  rw [← pair]
  exact hr

omit agree in
private theorem tracked_source {a : Region × Nat} (member : a ∈ Physical.trackedBytes (p.regions.map Prod.fst)) : a.1 ∈ sources p := by
  obtain ⟨⟨r,n⟩,hr,eq⟩ := List.mem_map.mp (tracked_region member)
  simp only at eq
  rw [← eq]
  exact region_member p r n hr

theorem layout (raw : CheckedTopology.Raw) (base : BitVec 64) (layout : LayoutFacts p raw mapping base before) :
    LayoutFacts p raw mapping base after := by
  refine ⟨?_,?_,layout.codeRange,?_,?_,?_,layout.codeWords⟩
  · intro r n member
    rw [agree.gp r (List.mem_append_left _ (buffer_member p r n member))]
    exact layout.bounds r n member
  · intro r n member
    rw [region agree r (buffer_member p r n member) 0,
      region_used agree (p.normalize r) (List.mem_append_right _ (List.mem_map.mpr ⟨r,buffer_member p r n member,rfl⟩)) 0]
    exact layout.aliases r n member
  · intro a ha b hb ne pa hpa hpb
    rw [view agree a.1 (tracked_source ha) a.2] at hpa
    rw [view agree b.1 (tracked_source hb) b.2] at hpb
    exact layout.injective a ha b hb ne pa hpa hpb
  · rw [outputBytes agree]
    exact layout.separated
  · intro r n member j bound pa mapped
    rw [view agree r (output_member p r n member) j] at mapped
    exact layout.outputTable r n member j bound pa mapped

theorem present : ∀ g j i k, memBL p.regions 0 g j = some (i,k) →
    (Physical.regionByte (SecpRawDeployment.view p mapping before) before g j).isSome = true →
    (Physical.regionByte (SecpRawDeployment.view p mapping after) after g j).isSome = true := by
  intro g j i k member old
  obtain ⟨n,hm,_⟩ := memBL_member p.regions 0 g j i k member
  have same := view agree g (region_member p g n hm) j
  unfold Physical.regionByte at old ⊢
  rw [same]
  cases mapped : SecpRawDeployment.view p mapping before g j with
  | none => simp [mapped] at old
  | some pa =>
    simp only [mapped,Option.bind_some] at old ⊢
    exact agree.present pa old

theorem spans
    (old : ∀ (r : Region) (n word : Nat), (r,n) ∈ p.buffers → p.normalize r = r → 8*word+16 ≤ n →
      SelectedBinding.At (SecpRawDeployment.view p mapping before) r word mapping (regionVA before r (8*word))) :
    ∀ (r : Region) (n word : Nat), (r,n) ∈ p.buffers → p.normalize r = r → 8*word+16 ≤ n →
      SelectedBinding.At (SecpRawDeployment.view p mapping after) r word mapping (regionVA after r (8*word)) := by
  intro r n word member fixed fits
  rw [region agree r (buffer_member p r n member) (8*word)]
  exact span_view _ _ r word mapping _ (view agree r (buffer_member p r n member)) (old r n word member fixed fits)

theorem domain_initial (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow) (base : BitVec 64)
    (topology : CheckedTopology.check raw (SecpRawDeployment.addresses p base before) 4 = true)
    (closed : ClosedMembershipAt (CheckedTopology.spec raw (SecpRawDeployment.addresses p base before) 4 topology)
      config rows mapping (SecpRawDeployment.consumer p raw mapping base before) (beforeFetchState before))
    (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int)
    (permitted : (SecpRawDeployment.consumer p raw mapping base after).permitted va acc aligned size) :
    va ∈ SecpRawDeployment.addresses p base after := by
  rw [consumer agree raw base] at permitted
  obtain ⟨q,hva,_,_,_,member,_⟩ := closed va acc aligned size permitted
  rw [addresses agree base,← hva]
  exact member

end Args

#print axioms of_pre
#print axioms addresses
#print axioms budget
#print axioms layout
#print axioms present
end DitShim243.DataTransport
