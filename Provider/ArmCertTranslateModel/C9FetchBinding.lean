import ArmCertTranslateModel.C9TranslateBinding
import ArmCertWalk.NativeFetchPreserving

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
open ArmCert.Eval.M1a.Fetch2
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Pure property of the declared mapping on four consecutive image bytes:
    they map to four consecutive physical bytes. Checkable from the mapping
    alone; it concerns no state and no future execution. -/
def ImageWordContiguous (mapping : MemReloc.Mapping) (base : MemReloc.Word)
    (offset : Nat) : Prop :=
  ∀ i < 4, ∀ pa, mapping (MemReloc.imageAddress base offset) = some pa →
    mapping (MemReloc.imageAddress base (offset + i)) = some (pa + i)

/-- C9 placement supplies Memory's `MappedBytesPresent` at an image PC. -/
theorem mapped_bytes_present_of_image_on {scope : Nat → Prop} {image : MemReloc.Image}
    {base : MemReloc.Word} {mapping : MemReloc.Mapping} {s : State} {offset : Nat}
    (placed : MemReloc.ImageOn scope image s base mapping)
    (pcAt : s.regs._PC = MemReloc.imageAddress base offset)
    (inside : ∀ i < 4, scope (offset + i)) (contiguous : ImageWordContiguous mapping base offset) :
    MappedBytesPresent mapping s.regs._PC s.mem := by
  intro pa mappedPC i small
  rw [pcAt] at mappedPC
  obtain ⟨byte, pa', _value, mapped', bytePresent⟩ := placed (offset + i) (inside i small)
  rw [contiguous i small pa mappedPC] at mapped'
  rw [← Option.some.inj mapped'] at bytePresent
  exact ⟨byte, bytePresent⟩

/-- Memory's actual fetch on the current invariant (`native_fetch_current_preserving`)
    at the ACTUAL before-fetch state `s`, with `MappedBytesPresent` derived from C9
    placement instead of supplied. All of its conclusions are kept. In addition the
    C9 placement holds on the SAME actual final state, and each fetched instruction
    byte equals the placed (relocated) image byte. The fetched word is read from
    the actual post-walk memory; separation of the image from the descriptor
    footprint is what makes it equal the placed image. `MappedNotMMIO` stays
    explicit (RX PT_LOAD PA ranges vs the model's special pages). -/
theorem c9_fetch_current {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (step : StepFacts s.regs) (el : s.regs.PSTATE.EL = 0#2)
    (pcLow : Sail.BitVec.extractLsb s.regs._PC 1 0 = 0#2) (il : s.regs.PSTATE.IL = 0#1)
    (current : CurrentS1At spec config rows s)
    (mode : HostEL0ModeAt s.regs) (aa64 : s.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt s.regs) (spe : s.regs.bank_Bool .SPESampleInFlight = false)
    (queryOf : AccessDescriptor → AccessQuery)
    (rawOf : ∀ acc, (queryOf acc).request.raw = acc)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    (mmio : MappedNotMMIO mapping s.regs._PC)
    (perAcc : ∀ acc, ActualIFetchAcc s acc → domain (queryOf acc) ∧
      ∃ data : S1AccessData spec config rows (queryOf acc),
        CurrentS1AccessAt spec config rows mapping (queryOf acc) data s)
    {scope : Nat → Prop} {image : MemReloc.Image} {base : MemReloc.Word} {offset : Nat}
    (placed : MemReloc.ImageOn scope image s base mapping)
    (separated : ImageTableSeparated scope base mapping (rowsFootprint spec.imageRows).byte)
    (pcAt : s.regs._PC = MemReloc.imageAddress base offset)
    (inside : ∀ i < 4, scope (offset + i)) (contiguous : ImageWordContiguous mapping base offset) :
    ∃ acc word final address faultOut translated,
      ∃ data : S1AccessData spec config rows (queryOf acc),
      ActualIFetchAcc s acc ∧
      __FetchInstr s.regs._PC s = .ok (__InstrEnc.__A64, word) final ∧
      CleanTranslateResultFields spec config rows mapping (queryOf acc) data.leafLevel data.view
        (fetchPre s) (faultOut, address) translated ∧
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? =
        some (word.extractLsb' (8 * i) 8)) ∧
      final.regs = translated.regs ∧ final.mem = translated.mem ∧
      final.events = translated.events.push
        (.memRead address.paddress.address.toNat 4 (some s.regs._PC.toNat) (AK_ifetch ()) false) ∧
      CurrentS1At spec config rows final ∧
      CurrentS1AccessAt spec config rows mapping (queryOf acc) data final ∧
      MemReloc.ImageOn scope image final base mapping ∧
      (∀ i < 4, image (offset + i) = some (word.extractLsb' (8 * i) 8)) := by
  have present := mapped_bytes_present_of_image_on placed pcAt inside contiguous
  obtain ⟨acc, word, final, address, faultOut, translated, data, actual, call, fields, bytes,
    fRegs, fMem, fEvents, post, postAccess⟩ :=
    native_fetch_current_preserving spec config rows mapping s step el pcLow il current mode aa64
      debug spe queryOf rawOf vaOf mmio present perAcc
  have frames := clean_translate_image_frame (clean_translate_fields_to_clean fields)
  have writes : WritesOnly (rowsFootprint spec.imageRows).byte (fun a => s.mem[a]?)
      (fun a => final.mem[a]?) := by
    intro a outside
    rw [fMem]
    exact frames.2.2.1 a outside
  have after : MemReloc.ImageOn scope image final base mapping :=
    MemReloc.imageOn_frame placed (scope_memory_eq_of_writes_only separated writes)
  refine ⟨acc, word, final, address, faultOut, translated, data, actual, call, fields, bytes,
    fRegs, fMem, fEvents, post, postAccess, after, ?_⟩
  intro i small
  obtain ⟨_params, _out, _operations, _active, _format, _faultEq, _faultNone, mappedQuery, _rest⟩ :=
    fields
  have mappedBase : mapping (MemReloc.imageAddress base offset) =
      some address.paddress.address.toNat := by
    rw [← pcAt, ← vaOf acc]; exact mappedQuery
  obtain ⟨byte, pa', value, mapped', placedByte⟩ := after (offset + i) (inside i small)
  rw [contiguous i small _ mappedBase] at mapped'
  rw [← Option.some.inj mapped', fMem, bytes i small] at placedByte
  rw [value]
  exact placedByte.symm

/-- Two 32-bit words with the same four little-endian bytes are equal. -/
theorem word32_eq_of_bytes {w v : BitVec 32}
    (same : ∀ i < 4, w.extractLsb' (8 * i) 8 = v.extractLsb' (8 * i) 8) : w = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j small
  have bit := congrArg (fun x : BitVec 8 => x.getLsbD (j % 8)) (same (j / 8) (by omega))
  have low : j % 8 < 8 := Nat.mod_lt _ (by decide)
  have split : 8 * (j / 8) + j % 8 = j := by omega
  simpa only [BitVec.getLsbD_extractLsb', low, decide_true, Bool.true_and, split] using bit

/-- Core's fetched-code input, in its exact shape, at any actual before-fetch
    state `s`: for EVERY actual descriptor and EVERY clean translation from
    `fetchPre s`, four post-translation bytes at the translated PA forming `w`
    force `w = v`, where `v` is any word whose bytes are the placed image bytes at
    the PC offset. Derived from C9 placement at `s`, image/descriptor-footprint
    separation and the translation's own table-only write frame. -/
theorem c9_fetch_code {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (s : State) (queryOf : AccessDescriptor → AccessQuery)
    (vaOf : ∀ acc, (queryOf acc).va = s.regs._PC)
    {scope : Nat → Prop} {image : MemReloc.Image} {base : MemReloc.Word} {offset : Nat}
    (placed : MemReloc.ImageOn scope image s base mapping)
    (separated : ImageTableSeparated scope base mapping (rowsFootprint spec.imageRows).byte)
    (pcAt : s.regs._PC = MemReloc.imageAddress base offset)
    (inside : ∀ i < 4, scope (offset + i)) (contiguous : ImageWordContiguous mapping base offset)
    (v : BitVec 32) (imageWord : ∀ i < 4, image (offset + i) = some (v.extractLsb' (8 * i) 8)) :
    ∀ (acc : AccessDescriptor) (leafLevel : Nat) (view : S1DescriptorPIE.View 64)
      (faultOut : FaultRecord) (address : AddressDescriptor) (translated : State) (w : BitVec 32),
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view (fetchPre s)
        (faultOut, address) translated →
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? = some (w.extractLsb' (8 * i) 8)) →
      w = v := by
  intro acc leafLevel view faultOut address translated w fields bytes
  have frames := clean_translate_image_frame (clean_translate_fields_to_clean fields)
  have writes : WritesOnly (rowsFootprint spec.imageRows).byte (fun a => s.mem[a]?)
      (fun a => translated.mem[a]?) := fun a outside => frames.2.2.1 a outside
  have after : MemReloc.ImageOn scope image translated base mapping :=
    MemReloc.imageOn_frame placed (scope_memory_eq_of_writes_only separated writes)
  obtain ⟨_params, _out, _operations, _active, _format, _faultEq, _faultNone, mappedQuery, _rest⟩ :=
    fields
  have mappedBase : mapping (MemReloc.imageAddress base offset) =
      some address.paddress.address.toNat := by
    rw [← pcAt, ← vaOf acc]; exact mappedQuery
  apply word32_eq_of_bytes
  intro i small
  obtain ⟨byte, pa', value, mapped', placedByte⟩ := after (offset + i) (inside i small)
  rw [contiguous i small _ mappedBase] at mapped'
  rw [← Option.some.inj mapped', bytes i small] at placedByte
  exact Option.some.inj (placedByte.trans (value.symm.trans (imageWord i small)))

#print axioms mapped_bytes_present_of_image_on
#print axioms c9_fetch_current
#print axioms word32_eq_of_bytes
#print axioms c9_fetch_code
end ArmCert.Translate.Model
