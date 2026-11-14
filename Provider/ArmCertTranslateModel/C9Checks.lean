import ArmCertTranslateModel.C9InitialPlacement

open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- ImageOn survives any physical write frame whose written bytes avoid the
    scoped image PAs (e.g. program stores outside code/rodata). The write set is
    the step's actual store footprint; no unrelated memory equality is used. -/
theorem image_on_across_writes {scope : Nat → Prop} {image : MemReloc.Image}
    {base : MemReloc.Word} {mapping : MemReloc.Mapping} {writes : Nat → Prop}
    {left right : State} (placed : MemReloc.ImageOn scope image left base mapping)
    (avoid : ImageTableSeparated scope base mapping writes)
    (frame : WritesOnly writes (fun a => left.mem[a]?) (fun a => right.mem[a]?)) :
    MemReloc.ImageOn scope image right base mapping :=
  MemReloc.imageOn_frame placed (scope_memory_eq_of_writes_only avoid frame)

/-- Executable check: no scoped mapped image PA lies in the descriptor footprint. -/
def checkImageTableSeparated (base : MemReloc.Word) (mapping : MemReloc.Mapping)
    (offsets : List Nat) (footprint : Footprint) : Bool :=
  offsets.all fun offset =>
    match mapping (MemReloc.imageAddress base offset) with
    | none => true
    | some pa => !(footprint.slots.any fun slot =>
        decide (slot ≤ pa) && decide (pa < slot + footprint.width))

theorem checkImageTableSeparated_sound {base : MemReloc.Word} {mapping : MemReloc.Mapping}
    {offsets : List Nat} {footprint : Footprint}
    (checked : checkImageTableSeparated base mapping offsets footprint = true) :
    ImageTableSeparated (· ∈ offsets) base mapping footprint.byte := by
  intro offset pa inside mapped inTable
  have entry := List.all_eq_true.1 checked offset inside
  simp only [mapped] at entry
  obtain ⟨slot, slotMember, low, high⟩ := inTable
  have hit : (footprint.slots.any fun slot =>
      decide (slot ≤ pa) && decide (pa < slot + footprint.width)) = true :=
    List.any_eq_true.2 ⟨slot, slotMember, by simp [low, high]⟩
  rw [hit] at entry
  exact absurd entry (by decide)

/-- Executable check of `ImageWordContiguous` at one image offset. -/
def checkImageWordContiguous (mapping : MemReloc.Mapping) (base : MemReloc.Word)
    (offset : Nat) : Bool :=
  match mapping (MemReloc.imageAddress base offset) with
  | none => true
  | some pa => (List.range 4).all fun i =>
      mapping (MemReloc.imageAddress base (offset + i)) == some (pa + i)

theorem checkImageWordContiguous_sound {mapping : MemReloc.Mapping}
    {base : MemReloc.Word} {offset : Nat}
    (checked : checkImageWordContiguous mapping base offset = true) :
    ImageWordContiguous mapping base offset := by
  intro i small pa mapped
  simp only [checkImageWordContiguous, mapped] at checked
  have entry := List.all_eq_true.1 checked i (List.mem_range.2 small)
  exact beq_iff_eq.1 entry

/-- Executable check of `ImageAliasCompatible` on a finite scope. -/
def checkImageAliasCompatible (image : MemReloc.Image) (base : MemReloc.Word)
    (mapping : MemReloc.Mapping) (offsets : List Nat) : Bool :=
  offsets.all fun first => offsets.all fun second =>
    match mapping (MemReloc.imageAddress base first),
        mapping (MemReloc.imageAddress base second) with
    | some left, some right => left != right || image first == image second
    | _, _ => true

theorem checkImageAliasCompatible_sound {image : MemReloc.Image} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {offsets : List Nat}
    (checked : checkImageAliasCompatible image base mapping offsets = true) :
    ImageAliasCompatible image base mapping offsets := by
  intro first firstMember second secondMember pa firstMapped secondMapped
  have entry := List.all_eq_true.1 (List.all_eq_true.1 checked first firstMember) second secondMember
  simp only [firstMapped, secondMapped, bne_self_eq_false, Bool.false_or] at entry
  exact beq_iff_eq.1 entry

/-- Executable check of Memory's `MappedNotMMIO` at one VA: the mapped PA is
    outside the model's two special 64KiB pages (PA[55:16] = 0x2C00 / 0x3C00). -/
def checkMappedNotMMIO (mapping : MemReloc.Mapping) (va : BitVec 64) : Bool :=
  match mapping va with
  | none => true
  | some pa => decide (pa / 65536 ≠ 0x2C00) && decide (pa / 65536 ≠ 0x3C00)

theorem checkMappedNotMMIO_sound {mapping : MemReloc.Mapping} {va : BitVec 64}
    (checked : checkMappedNotMMIO mapping va = true) :
    ArmCertWalk.MappedNotMMIO mapping va := by
  intro pa mapped
  simp only [checkMappedNotMMIO, mapped, Bool.and_eq_true, decide_eq_true_eq] at checked
  have bound : pa.toNat < 72057594037927936 := pa.isLt
  have field : (Sail.BitVec.extractLsb pa 55 16).toNat = pa.toNat / 65536 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow]
    omega
  refine ⟨fun equal => checked.1 ?_, fun equal => checked.2 ?_⟩
  · have value := congrArg BitVec.toNat equal
    rw [field] at value
    simpa using value
  · have value := congrArg BitVec.toNat equal
    rw [field] at value
    simpa using value

#print axioms checkMappedNotMMIO_sound
#print axioms image_on_across_writes
#print axioms checkImageTableSeparated_sound
#print axioms checkImageWordContiguous_sound
#print axioms checkImageAliasCompatible_sound
end ArmCert.Translate.Model
