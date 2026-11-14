-- Memory part A: CodeHyps static facts from executable
-- checks (A1) and the carry lemmas ChainInv v2's plan_step needs for the two new per-state
-- fields `placed` (ImageOn) and `closed` (ClosedMembershipAt at beforeFetchState) (A2).
import HeapV2StepCerts.Straight
import HeapV2StepCerts.CodeScope
import ArmCertTranslateModel.C9Checks
import ArmCertTranslateModel.StoreHistory
import Bridge.CruxGenGuarded.ClosedChain
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace HeapV2StepCerts
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.HeapV2Compose
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts

/-! ### A1: static facts from executable checks -/

theorem codeScope_inside : ∀ code ∈ HeapV2Plan.codeWords, ∀ i < 4, codeScope (HeapV2.entryOffset + code.1 + i) :=
  fun code member i small =>
    List.mem_flatMap.2 ⟨code, member, List.mem_map.2 ⟨i, List.mem_range.2 small, rfl⟩⟩

/-- Contiguity check over every code word. -/
def checkCodeContiguous (mapping : MemReloc.Mapping) (base : MemReloc.Word) : Bool :=
  HeapV2Plan.codeWords.all fun c => checkImageWordContiguous mapping base (HeapV2.entryOffset + c.1)

/-- Not-MMIO check over every code word. -/
def checkCodeNotMMIO (mapping : MemReloc.Mapping) (base : MemReloc.Word) : Bool :=
  HeapV2Plan.codeWords.all fun c =>
    checkMappedNotMMIO mapping (MemReloc.imageAddress base (HeapV2.entryOffset + c.1))

/-- The four static CodeHyps facts, for the code scope, from three Boolean check results. -/
structure CodeStatic (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (table : Nat → Prop) : Prop where
  separated : ImageTableSeparated codeScope base mapping table
  inside : ∀ code ∈ HeapV2Plan.codeWords, ∀ i < 4, codeScope (HeapV2.entryOffset + code.1 + i)
  contiguous : ∀ code ∈ HeapV2Plan.codeWords, ImageWordContiguous mapping base (HeapV2.entryOffset + code.1)
  notMMIO : ∀ code ∈ HeapV2Plan.codeWords,
    MappedNotMMIO mapping (MemReloc.imageAddress base (HeapV2.entryOffset + code.1))

theorem codeStatic_of_checks (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (footprint : Footprint)
    (separatedChk : checkImageTableSeparated base mapping codeOffsets footprint = true)
    (contiguousChk : checkCodeContiguous mapping base = true)
    (mmioChk : checkCodeNotMMIO mapping base = true) :
    CodeStatic mapping base footprint.byte where
  separated := checkImageTableSeparated_sound separatedChk
  inside := codeScope_inside
  contiguous := fun code member =>
    checkImageWordContiguous_sound (List.all_eq_true.1 contiguousChk code member)
  notMMIO := fun code member => checkMappedNotMMIO_sound (List.all_eq_true.1 mmioChk code member)

/-- CodeHyps from the static checks plus the two ChainInv v2 per-state fields. -/
def CodeHyps.ofChecks {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {base : BitVec 64} {budget : Nat} (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (placed : ∀ k x, ChainInv spec config rows base offsetOf budget k x →
      MemReloc.ImageOn codeScope (HeapV2.image base) x base mapping)
    (closed : ∀ k x, ChainInv spec config rows base offsetOf budget k x →
      ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
        (ArmBridge.CruxGenGuarded.beforeFetchState x)) :
    CodeHyps spec config rows mapping base budget :=
  ⟨codeScope, pins, table, static.separated, static.inside, static.contiguous, static.notMMIO, placed, closed⟩

/-! ### A2: carry lemmas for `placed` and `closed` -/

/-- ImageOn reads only memory: it moves freely between x, beforeFetchState x and fetchPre. -/
theorem placed_before_fetch {scope : Nat → Prop} {image : MemReloc.Image} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {x : NativeState}
    (placed : MemReloc.ImageOn scope image x base mapping) :
    MemReloc.ImageOn scope image (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState x)) base mapping :=
  placed

theorem placed_of_mem_eq {scope : Nat → Prop} {image : MemReloc.Image} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {x y : NativeState} (mem : y.mem = x.mem)
    (placed : MemReloc.ImageOn scope image x base mapping) :
    MemReloc.ImageOn scope image y base mapping := by
  intro offset inside
  obtain ⟨byte, pa, hi, hm, hp⟩ := placed offset inside
  exact ⟨byte, pa, hi, hm, by rw [mem]; exact hp⟩

/-- A clean actual translation (any route, incl. AF/dirty updates) writes only table
bytes, so ImageOn survives it when the scope is separated from the table footprint. -/
theorem placed_translate {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {leafLevel : Nat} {view : S1DescriptorPIE.View 64}
    {initial other : ArmCertWalk.State} {result : FaultRecord × AddressDescriptor}
    {scope : Nat → Prop} {image : MemReloc.Image} {base : MemReloc.Word}
    (placed : MemReloc.ImageOn scope image initial base mapping)
    (separated : ImageTableSeparated scope base mapping (rowsFootprint spec.imageRows).byte)
    (clean : CleanTranslateResultFields spec config rows mapping query leafLevel view initial result other) :
    MemReloc.ImageOn scope image other base mapping := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, history, _⟩ := clean
  exact image_on_across_writes placed separated (history.frame rfl)

/-- `placed_fetch`: from ImageOn at x to ImageOn at the actual fetched state (`final` of
native_fetch_current_preserving: final.mem = translated.mem, clean from fetchPre(beforeFetchState x)). -/
theorem placed_fetch {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {leafLevel : Nat} {view : S1DescriptorPIE.View 64}
    {x : NativeState} {translated final : ArmCertWalk.State} {result : FaultRecord × AddressDescriptor}
    {scope : Nat → Prop} {image : MemReloc.Image} {base : MemReloc.Word}
    (placed : MemReloc.ImageOn scope image x base mapping)
    (separated : ImageTableSeparated scope base mapping (rowsFootprint spec.imageRows).byte)
    (clean : CleanTranslateResultFields spec config rows mapping query leafLevel view
      (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState x)) result translated)
    (finalMem : final.mem = translated.mem) :
    MemReloc.ImageOn scope image final base mapping :=
  placed_of_mem_eq finalMem (placed_translate (placed_before_fetch placed) separated clean)

/-- `placed_class` for fixed (non-memory) class tails: ClassTail exports fin.mem = fetched.mem. -/
theorem placed_class {scope : Nat → Prop} {image : MemReloc.Image} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {fetched fin : NativeState} (mem : fin.mem = fetched.mem)
    (placed : MemReloc.ImageOn scope image fetched base mapping) :
    MemReloc.ImageOn scope image fin base mapping :=
  placed_of_mem_eq mem placed

/-- `placed_class` for memory classes: the step writes only `written`, disjoint from the code scope. -/
theorem placed_class_writes {scope : Nat → Prop} {image : MemReloc.Image} {base : MemReloc.Word}
    {mapping : MemReloc.Mapping} {written : Nat → Prop} {fetched fin : NativeState}
    (frame : WritesOnly written (fun a => fetched.mem[a]?) (fun a => fin.mem[a]?))
    (avoid : ImageTableSeparated scope base mapping written)
    (placed : MemReloc.ImageOn scope image fetched base mapping) :
    MemReloc.ImageOn scope image fin base mapping :=
  image_on_across_writes placed avoid frame

/-- `closed_step` for ANY class tail (incl. memory classes): ClosedMembershipAt is a
register-only property (closed_of_fields), so the class-tail exports SysEq2 / Frame / NPE
bkHeap with the fetch's E20 frame carry it; no table/memory fact is needed. -/
theorem closed_step {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    (writes : NativeEntry.Effects.Writes) (word : BitVec 32) (K : Int)
    (fetched sp a fin : NativeState) (closed : ClosedMembershipAt spec config rows mapping m fetched)
    (e20 : E20Frame fetched.regs sp.regs)
    (frame : NativeEntryContract.Frame writes (ArmBridge.CruxGenGuarded.actionState word sp K) a)
    (sys : SysEq2 a.regs fin.regs)
    (np : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap a.regs fin.regs) :
    ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState fin) :=
  ArmBridge.CruxGenGuarded.ClosedChain.closed_before_fetch fin
    (ArmBridge.CruxGenGuarded.ClosedChain.closed_tail writes word K fetched sp a fin closed e20 frame sys np)

#print axioms codeStatic_of_checks
#print axioms placed_translate
#print axioms placed_fetch
#print axioms placed_class
#print axioms placed_class_writes
#print axioms closed_step
end HeapV2StepCerts
