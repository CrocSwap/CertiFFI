import ArmCertTranslateModel.HeapV2E17Table
import ArmCertTranslateModel.C9FetchBinding

/-! E17 obligation (1b) for heap-v2, component-wise (Core assembles its
`FetchObligations` structure): at a before-fetch state `pre` whose PC is the plan
code word `c` placed at load base `base`, the mapped bytes are present, every actual
fetched word equals the plan word, and every actual IFETCH descriptor's query is in the
domain with current access data — from C9 placement, image/table separation and closed
membership for the plan's consumer map. -/

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ArmCert.Translate.Model.HeapV2E17

/-- Inside the RX segment [0x10278, 0x10574) of the relink (body + decision-179 shim) the
    relocated image (any load base; no patches) is the ELF byte. -/
theorem image_code (base : MemReloc.Word) (offset : Nat) (low : 0x10278 ≤ offset)
    (high : offset < 0x10574) : HeapV2.image base offset = HeapV2.file (offset - 0x10000) := by
  have outside : ¬ (0x20578 ≤ offset ∧ offset < 0x20578 + 0xa88) := by omega
  have inside : 0x10278 ≤ offset ∧ offset < 0x10278 + 0x2fc := by omega
  have early : offset - 0x10278 < 0x2fc := by omega
  simp only [HeapV2.image, MemReloc.relocatedImage, HeapV2.patches, List.foldl_nil,
    MemReloc.loadSegments, HeapV2.segments, List.foldl_cons, MemReloc.loadSegment, outside,
    inside, early, and_self, ite_true, ite_false]
  exact congrArg HeapV2.file (by omega)

/-- The four relocated image bytes at a plan code word are that word's little-endian bytes. -/
theorem fetch_code_image (base : MemReloc.Word) {code : Nat × Nat} (member : code ∈ HeapV2Plan.codeWords) :
    ∀ i < 4, HeapV2.image base (HeapV2.entryOffset + code.1 + i) =
      some ((BitVec.ofNat 32 code.2).extractLsb' (8 * i) 8) := by
  intro i small
  have bound := (HeapV2Plan.codeWords_bound code member).1
  rw [image_code base _ (by simp only [HeapV2.entryOffset]; omega) (by simp only [HeapV2.entryOffset]; omega)]
  have bytes := HeapV2Plan.codeWords_bytes code member i small
  have shift : HeapV2.entryOffset + code.1 + i - 0x10000 = 0x278 + code.1 + i := by
    simp only [HeapV2.entryOffset]; omega
  rw [shift]
  exact bytes

/-- `MappedBytesPresent` at the before-fetch state from C9 placement of the code word. -/
theorem fetch_present {scope : Nat → Prop} {base : MemReloc.Word} {mapping : MemReloc.Mapping}
    {pre : State} {code : Nat × Nat}
    (placed : MemReloc.ImageOn scope (HeapV2.image base) pre base mapping)
    (pcAt : pre.regs._PC = MemReloc.imageAddress base (HeapV2.entryOffset + code.1))
    (inside : ∀ i < 4, scope (HeapV2.entryOffset + code.1 + i))
    (contiguous : ImageWordContiguous mapping base (HeapV2.entryOffset + code.1)) :
    MappedBytesPresent mapping pre.regs._PC pre.mem :=
  mapped_bytes_present_of_image_on placed pcAt inside contiguous

/-- Core's `code` field: every clean translation from `fetchPre pre` whose post-translation
    bytes at the translated PA form `w` has `w` = the plan word. -/
theorem fetch_code {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    {scope : Nat → Prop} {base : MemReloc.Word} {pre : State} {code : Nat × Nat}
    (member : code ∈ HeapV2Plan.codeWords) (queryOf : AccessDescriptor → AccessQuery)
    (vaOf : ∀ acc, (queryOf acc).va = pre.regs._PC)
    (placed : MemReloc.ImageOn scope (HeapV2.image base) pre base mapping)
    (separated : ImageTableSeparated scope base mapping (rowsFootprint spec.imageRows).byte)
    (pcAt : pre.regs._PC = MemReloc.imageAddress base (HeapV2.entryOffset + code.1))
    (inside : ∀ i < 4, scope (HeapV2.entryOffset + code.1 + i))
    (contiguous : ImageWordContiguous mapping base (HeapV2.entryOffset + code.1)) :
    ∀ (acc : AccessDescriptor) (leafLevel : Nat) (view : S1DescriptorPIE.View 64)
      (faultOut : FaultRecord) (address : AddressDescriptor) (translated : State) (w : BitVec 32),
      CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view (fetchPre pre)
        (faultOut, address) translated →
      (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? = some (w.extractLsb' (8 * i) 8)) →
      w = BitVec.ofNat 32 code.2 :=
  c9_fetch_code spec config rows mapping pre queryOf vaOf placed separated pcAt inside contiguous
    (BitVec.ofNat 32 code.2) (fetch_code_image base member)

/-- Core's `perAcc` field: every actual IFETCH descriptor's query at the PC is in the
    domain with current access data, from closed membership for the plan's consumer map. -/
theorem fetch_per_acc {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (p : Pins) (base : Nat) (table : Nat → Prop) {pre : State} {code : Nat × Nat}
    (member : code ∈ HeapV2Plan.codeWords) (pcAt : pre.regs._PC = codeVA base code.1)
    (closed : ClosedMembershipAt spec config rows mapping (consumerMap p base mapping table) pre)
    (shape : ∀ acc, ActualIFetchAcc pre acc → acc.el = EL0 ∧ acc.ss = .SS_NonSecure) :
    ∀ acc, ActualIFetchAcc pre acc →
      domain ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩ ∧
      ∃ data : S1AccessData spec config rows ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩,
        CurrentS1AccessAt spec config rows mapping ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩ data pre := by
  intro acc actual
  obtain ⟨acctype, read, write, tagaccess, transactional, nonfault, contiguous, firstfault, first, ls64⟩ :=
    actual_ifetch_flags actual
  obtain ⟨el, ss⟩ := shape acc actual
  have permitted : Permitted p base pre.regs._PC acc 4 :=
    Or.inr ⟨code, member, pcAt, rfl, ⟨acctype, el, ss, read, write, tagaccess, transactional, nonfault,
      contiguous, firstfault, first, ls64⟩⟩
  obtain ⟨⟨va, ⟨raw, aligned⟩, size⟩, hva, hraw, haligned, hsize, inDomain, data, current⟩ :=
    closed pre.regs._PC acc true 4 permitted
  simp only at hva hraw haligned hsize
  subst hva hraw haligned hsize
  exact ⟨inDomain, data, current⟩

#print axioms image_code
#print axioms fetch_code_image
#print axioms fetch_code
#print axioms fetch_per_acc
end ArmCert.Translate.Model.HeapV2E17
