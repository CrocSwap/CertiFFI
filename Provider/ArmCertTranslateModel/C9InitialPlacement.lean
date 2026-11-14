import ArmCertTranslateModel.C9FetchBinding
import NativeSourceInit.PhysicalPlan

open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Physical byte rows for a finite certified image scope: each scoped offset
    that is mapped and present contributes (mapped PA, image byte). -/
def imagePlan (image : MemReloc.Image) (base : MemReloc.Word)
    (mapping : MemReloc.Mapping) (offsets : List Nat) : NativeSourceInit.Plan :=
  offsets.filterMap fun offset =>
    (mapping (MemReloc.imageAddress base offset)).bind fun pa =>
      (image offset).map fun byte => (pa, byte)

theorem mem_imagePlan {image : MemReloc.Image} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {offsets : List Nat} {row : NativeSourceInit.PhysicalByte} :
    row ∈ imagePlan image base mapping offsets ↔
      ∃ offset ∈ offsets, mapping (MemReloc.imageAddress base offset) = some row.1 ∧
        image offset = some row.2 := by
  obtain ⟨pa, byte⟩ := row
  simp only [imagePlan, List.mem_filterMap]
  constructor
  · rintro ⟨offset, member, found⟩
    cases mapped : mapping (MemReloc.imageAddress base offset) with
    | none => simp [mapped] at found
    | some pa' =>
      cases value : image offset with
      | none => simp [mapped, value] at found
      | some byte' =>
        simp only [mapped, value, Option.bind_some, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at found
        obtain ⟨samePA, sameByte⟩ := found
        subst samePA
        subst sameByte
        exact ⟨offset, member, mapped, value⟩
  · rintro ⟨offset, member, mapped, value⟩
    refine ⟨offset, member, ?_⟩
    simp only [mapped, value, Option.bind_some, Option.map_some]

/-- Checkable alias compatibility on the scope: two scoped offsets with the same
    mapped PA carry the same image byte (e.g. an injective scope mapping). -/
def ImageAliasCompatible (image : MemReloc.Image) (base : MemReloc.Word)
    (mapping : MemReloc.Mapping) (offsets : List Nat) : Prop :=
  ∀ first ∈ offsets, ∀ second ∈ offsets, ∀ pa,
    mapping (MemReloc.imageAddress base first) = some pa →
    mapping (MemReloc.imageAddress base second) = some pa → image first = image second

theorem imagePlan_consistent {image : MemReloc.Image} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {offsets : List Nat}
    (compatible : ImageAliasCompatible image base mapping offsets) :
    NativeSourceInit.Consistent (imagePlan image base mapping offsets) := by
  intro left leftMember right rightMember samePA
  obtain ⟨first, firstMember, firstMapped, firstValue⟩ := mem_imagePlan.1 leftMember
  obtain ⟨second, secondMember, secondMapped, secondValue⟩ := mem_imagePlan.1 rightMember
  rw [← samePA] at secondMapped
  have equal := compatible first firstMember second secondMember left.1 firstMapped secondMapped
  rw [firstValue, secondValue] at equal
  exact Option.some.inj equal

/-- C9 placement on Native-1's ACTUAL initial RAM constructor: materializing the
    image plan into any native state places every scoped image byte at its mapped
    PA. Registers and every non-RAM field are unchanged (Native-1 `initState_frame`);
    bytes outside the plan keep their exact original Option value. -/
theorem initState_image_on (image : MemReloc.Image) (base : MemReloc.Word)
    (mapping : MemReloc.Mapping) (offsets : List Nat) (state : NativeSourceInit.NativeState)
    (compatible : ImageAliasCompatible image base mapping offsets)
    (mapped : ∀ offset ∈ offsets, ∃ pa, mapping (MemReloc.imageAddress base offset) = some pa)
    (present : ∀ offset ∈ offsets, ∃ byte, image offset = some byte) :
    MemReloc.ImageOn (· ∈ offsets) image
      (NativeSourceInit.initState (imagePlan image base mapping offsets) state) base mapping := by
  intro offset member
  obtain ⟨pa, hm⟩ := mapped offset member
  obtain ⟨byte, hi⟩ := present offset member
  refine ⟨byte, pa, hi, hm, ?_⟩
  exact NativeSourceInit.initState_satisfies _ state (imagePlan_consistent compatible) (pa, byte)
    (mem_imagePlan.2 ⟨offset, member, hm, hi⟩)

/-- The C9 startup postcondition for the normalized relocated image, on the
    materialized initial state. Raw ELF -> segments/patches stays Core's checker. -/
theorem initState_c9 (file : MemReloc.Image) (segments : List MemReloc.LoadSegment)
    (patches : List MemReloc.RelativePatch) (base : MemReloc.Word)
    (mapping : MemReloc.Mapping) (offsets : List Nat) (state : NativeSourceInit.NativeState)
    (compatible : ImageAliasCompatible (MemReloc.relocatedImage file segments patches base)
      base mapping offsets)
    (mapped : ∀ offset ∈ offsets, ∃ pa, mapping (MemReloc.imageAddress base offset) = some pa)
    (present : ∀ offset ∈ offsets,
      ∃ byte, MemReloc.relocatedImage file segments patches base offset = some byte) :
    MemReloc.C9 (· ∈ offsets) file segments patches base
      (NativeSourceInit.initState
        (imagePlan (MemReloc.relocatedImage file segments patches base) base mapping offsets)
        state) mapping :=
  initState_image_on _ base mapping offsets state compatible mapped present

/-- Checkable separation of a declared VA region's mapped PAs from a table footprint. -/
def RegionTableSeparated (region : BitVec 64 → Prop) (mapping : MemReloc.Mapping)
    (table : Nat → Prop) : Prop :=
  ∀ va pa, region va → mapping va = some pa → ¬ table pa

/-- Program writes whose PAs are mapped from a separated region never touch the
    table footprint. The write PA set comes from the step's actual store rows. -/
theorem separated_of_region {region : BitVec 64 → Prop} {mapping : MemReloc.Mapping}
    {table writes : Nat → Prop} (separated : RegionTableSeparated region mapping table)
    (cover : ∀ pa, writes pa → ∃ va, region va ∧ mapping va = some pa) :
    Separated table writes := by
  intro pa inTable written
  obtain ⟨va, inRegion, mappedVA⟩ := cover pa written
  exact separated va pa inRegion mappedVA inTable

/-- The image instance of region separation. -/
theorem image_table_separated_of_region {scope : Nat → Prop} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {table : Nat → Prop}
    (separated : RegionTableSeparated
      (fun va => ∃ offset, scope offset ∧ va = MemReloc.imageAddress base offset) mapping table) :
    ImageTableSeparated scope base mapping table :=
  fun offset pa inside mappedPA => separated _ pa ⟨offset, inside, rfl⟩ mappedPA

#print axioms imagePlan_consistent
#print axioms initState_image_on
#print axioms initState_c9
#print axioms separated_of_region
#print axioms image_table_separated_of_region
end ArmCert.Translate.Model
