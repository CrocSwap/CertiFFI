import ArmCertTranslateModel.C9Checks
import ArmCertTranslateModel.HeapV2Image

open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model.HeapV2

/-- The normalized heap-v2 startup image at load base `base` (ELF-ordered PT_LOADs,
    BSS tails as explicit zero bytes, no RELATIVE patches). -/
def image (base : MemReloc.Word) : MemReloc.Image :=
  MemReloc.relocatedImage file segments patches base

/-- One physical byte plan for the entry RAM: the mapped scoped image bytes, then
    the page-table rows supplied for this run (the real ones are the kernel's). -/
def entryPlan (base : MemReloc.Word) (mapping : MemReloc.Mapping) (offsets : List Nat)
    (tableRows : NativeSourceInit.Plan) : NativeSourceInit.Plan :=
  imagePlan (image base) base mapping offsets ++ tableRows

/-- The entry state: Native-1's actual RAM initializer applied to the plan over any
    starting native state `start`; registers and every non-RAM field are `start`'s. -/
def entryState (base : MemReloc.Word) (mapping : MemReloc.Mapping) (offsets : List Nat)
    (tableRows : NativeSourceInit.Plan) (start : NativeSourceInit.NativeState) :
    NativeSourceInit.NativeState :=
  NativeSourceInit.initState (entryPlan base mapping offsets tableRows) start

theorem entryState_regs (base : MemReloc.Word) (mapping : MemReloc.Mapping)
    (offsets : List Nat) (tableRows : NativeSourceInit.Plan) (start : NativeSourceInit.NativeState) :
    (entryState base mapping offsets tableRows start).regs = start.regs := rfl

/-- E17 obligation 1, parametric part (A). For any load base, mapping, finite image
    scope, table rows and starting state whose plan is consistent and whose scoped
    image offsets are mapped and present: C9 placement of the heap-v2 image holds on
    the entry state, every supplied table row is present there, and registers are
    the starting ones (so register premises transfer unchanged). The current
    invariant itself comes from the evaluated `checkCurrentS1` on this state. -/
theorem heapv2_entry (base : MemReloc.Word) (mapping : MemReloc.Mapping)
    (offsets : List Nat) (tableRows : NativeSourceInit.Plan) (start : NativeSourceInit.NativeState)
    (consistent : NativeSourceInit.Consistent (entryPlan base mapping offsets tableRows))
    (mapped : ∀ offset ∈ offsets, ∃ pa, mapping (MemReloc.imageAddress base offset) = some pa)
    (present : ∀ offset ∈ offsets, ∃ byte, image base offset = some byte) :
    MemReloc.C9 (· ∈ offsets) file segments patches base
        (entryState base mapping offsets tableRows start) mapping ∧
      (∀ row ∈ tableRows, (entryState base mapping offsets tableRows start).mem[row.1]? = some row.2) ∧
      (entryState base mapping offsets tableRows start).regs = start.regs := by
  have satisfied := NativeSourceInit.initState_satisfies _ start consistent
  refine ⟨?_, fun row member => satisfied row (List.mem_append_right _ member), rfl⟩
  intro offset member
  obtain ⟨pa, hm⟩ := mapped offset member
  obtain ⟨byte, hi⟩ := present offset member
  exact ⟨byte, pa, hi, hm, satisfied (pa, byte)
    (List.mem_append_left _ (mem_imagePlan.2 ⟨offset, member, hm, hi⟩))⟩

/-- The semantic entry PC is inside the code scope when the base places it. -/
theorem entry_pc (base : MemReloc.Word) :
    MemReloc.imageAddress base entryOffset = base + BitVec.ofNat 64 0x10278 := rfl

#print axioms heapv2_entry
end ArmCert.Translate.Model.HeapV2
