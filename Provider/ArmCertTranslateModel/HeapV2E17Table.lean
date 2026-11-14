import ArmCertTranslateModel.ClosedTable
import ArmCertTranslateModel.HeapV2Plan

/-! E17 obligation (1a) for heap-v2, PARAMETRIC in the caller's entry pins (SP, x0, x1)
and the load base: the consumer map whose permitted accesses are exactly the plan's
declared data accesses (entry pin + constant offset, with their sizes and read/write
descriptor shape) and the instruction fetches at the plan's code words; its
agreement with the walk mapping; and closed query membership at a state from one
evaluated representative per declared access. -/

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model.HeapV2E17

/-- Caller-supplied entry pointers (symbolic in the claim; concrete in the synthetic instance). -/
structure Pins where
  sp : Nat
  x0 : Nat
  x1 : Nat

def pin (p : Pins) : Nat → Nat
  | 0 => p.sp
  | 1 => p.x0
  | _ => p.x1

/-- VA of a symbolic data access: entry pin + signed constant offset. -/
def dataVA (p : Pins) (access : Nat × Nat × Int × Nat × Bool) : BitVec 64 :=
  BitVec.ofInt 64 ((pin p access.2.1 : Int) + access.2.2.1)

/-- VA of the code word at entry offset `offset` for load base `base`. -/
def codeVA (base : Nat) (offset : Nat) : BitVec 64 := BitVec.ofNat 64 (base + HeapV2.entryOffset + offset)

/-- Permitted accesses of the heap-v2 plan. -/
def Permitted (p : Pins) (base : Nat) (va : BitVec 64) (acc : AccessDescriptor) (size : Int) : Prop :=
  (∃ access ∈ HeapV2Plan.symbolicAccesses, va = dataVA p access ∧ size = (access.2.2.2.1 : Int) ∧
      DataShape access.2.2.2.2 acc) ∨
    (∃ code ∈ HeapV2Plan.codeWords, va = codeVA base code.1 ∧ size = 4 ∧ FetchShape acc)

/-- The plan's consumer map: PA read off the walk mapping, table bytes = descriptor footprint. -/
def consumerMap (p : Pins) (base : Nat) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) :
    ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  ⟨fun va => BitVec.ofNat 56 ((mapping va).getD 0), fun va acc _ size => Permitted p base va acc size, table⟩

/-- Static agreement, from every permitted VA being mapped below 2^56 and the
    descriptor footprint being the table bytes. -/
theorem consumer_agrees {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (p : Pins) (base : Nat) (mapping : BitVec 64 → Option Nat)
    (mapped : ∀ va acc size, Permitted p base va acc size → ∃ pa, mapping va = some pa ∧ pa < 2 ^ 56) :
    ConsumerMapAgrees spec mapping (consumerMap p base mapping (rowsFootprint spec.imageRows).byte) := by
  refine ⟨?_, fun _ inside => inside⟩
  intro va acc aligned size permitted
  obtain ⟨pa, hm, bound⟩ := mapped va acc size permitted
  simp only [consumerMap, hm, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

/-- (1a) Closed membership at `state` from one evaluated representative per declared
    access (same VA, a descriptor of the same shape, current access data at `state`),
    with the spec's domain admitting every request at a declared VA. -/
theorem heapv2_closed {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (p : Pins) (base : Nat) (table : Nat → Prop) (state : State)
    (domainVA : ∀ va acc size, Permitted p base va acc size →
      ∀ r : S1LogicalReference.Request, domain ⟨va, r, size⟩)
    (dataReps : ∀ access ∈ HeapV2Plan.symbolicAccesses,
      ∃ (r : S1LogicalReference.Request)
        (data : S1AccessData spec config rows ⟨dataVA p access, r, (access.2.2.2.1 : Int)⟩),
        DataShape access.2.2.2.2 r.raw ∧
        CurrentS1AccessAt spec config rows mapping ⟨dataVA p access, r, (access.2.2.2.1 : Int)⟩ data state)
    (codeReps : ∀ code ∈ HeapV2Plan.codeWords,
      ∃ (r : S1LogicalReference.Request) (data : S1AccessData spec config rows ⟨codeVA base code.1, r, 4⟩),
        FetchShape r.raw ∧ CurrentS1AccessAt spec config rows mapping ⟨codeVA base code.1, r, 4⟩ data state) :
    ClosedMembershipAt spec config rows mapping (consumerMap p base mapping table) state := by
  apply closed_of_represented
  intro va acc aligned size permitted
  refine ⟨domainVA va acc size permitted ⟨acc, aligned⟩, ?_⟩
  rcases permitted with ⟨access, member, hva, hsize, shape⟩ | ⟨code, member, hva, hsize, shape⟩
  · obtain ⟨r, data, rshape, current⟩ := dataReps access member
    subst hva; subst hsize
    exact ⟨r, data, rshape.agree shape, current⟩
  · obtain ⟨r, data, rshape, current⟩ := codeReps code member
    subst hva; subst hsize
    exact ⟨r, data, rshape.agree shape, current⟩

#print axioms consumer_agrees
#print axioms heapv2_closed
end ArmCert.Translate.Model.HeapV2E17
