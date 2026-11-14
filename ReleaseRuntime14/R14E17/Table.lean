import ArmCertTranslateModel.ClosedTable
import R14Plan.Plan

/-! runtime14 E17 obligation (1a), generic over a case's plan tables (R14Plan), PARAMETRIC in the
caller's entry pins: entry register values (index 31 = SP) and the VAs of the indirect access forms (e.g.
x0+mem64[x1+8]+24), which are caller-supplied, as the route Inputs carry them. Mirrors HeapV2E17Table: the consumer
map whose permitted accesses are exactly the case's declared data accesses (pin + const, size, read/write shape)
and its instruction fetches; its agreement with the walk mapping; closed query membership from one evaluated
representative per declared access. -/

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
open ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace R14E17

/-- Caller-supplied entry pins. -/
structure Pins where
  regs : Nat → Nat
  indirect : String → Nat

def baseVA (p : Pins) : R14Plan.Base → Int
  | .pin r off => (p.regs r : Int) + off
  | .indirect f => (p.indirect f : Int)

def dataVA (p : Pins) (b : R14Plan.Base) : BitVec 64 := BitVec.ofInt 64 (baseVA p b)

/-- VA of the code word at entry offset `off` for load base `base` (image offsets = link vaddrs). -/
def codeVA (base entry off : Nat) : BitVec 64 := BitVec.ofNat 64 (base + entry + off)

abbrev Access := Nat × R14Plan.Base × Nat × Bool

def Permitted (accs : List Access) (cws : List (Nat × Nat)) (entry : Nat) (p : Pins) (base : Nat)
    (va : BitVec 64) (acc : AccessDescriptor) (size : Int) : Prop :=
  (∃ a ∈ accs, va = dataVA p a.2.1 ∧ size = (a.2.2.1 : Int) ∧ DataShape a.2.2.2 acc) ∨
    (∃ c ∈ cws, va = codeVA base entry c.1 ∧ size = 4 ∧ FetchShape acc)

def consumerMap (accs : List Access) (cws : List (Nat × Nat)) (entry : Nat) (p : Pins) (base : Nat)
    (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) : ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  ⟨fun va => BitVec.ofNat 56 ((mapping va).getD 0), fun va acc _ size => Permitted accs cws entry p base va acc size, table⟩

theorem consumer_agrees {domain : QueryDomain} (spec : TopologyImageSpec domain) (accs : List Access)
    (cws : List (Nat × Nat)) (entry : Nat) (p : Pins) (base : Nat) (mapping : BitVec 64 → Option Nat)
    (mapped : ∀ va acc size, Permitted accs cws entry p base va acc size → ∃ pa, mapping va = some pa ∧ pa < 2 ^ 56) :
    ConsumerMapAgrees spec mapping (consumerMap accs cws entry p base mapping (rowsFootprint spec.imageRows).byte) := by
  refine ⟨?_, fun _ inside => inside⟩
  intro va acc aligned size permitted
  obtain ⟨pa, hm, bound⟩ := mapped va acc size permitted
  simp only [consumerMap, hm, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

theorem closed {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (accs : List Access) (cws : List (Nat × Nat))
    (entry : Nat) (p : Pins) (base : Nat) (table : Nat → Prop) (state : ArmCertWalk.State)
    (domainVA : ∀ va acc size, Permitted accs cws entry p base va acc size →
      ∀ r : S1LogicalReference.Request, domain ⟨va, r, size⟩)
    (dataReps : ∀ a ∈ accs, ∃ (r : S1LogicalReference.Request)
        (data : S1AccessData spec config rows ⟨dataVA p a.2.1, r, (a.2.2.1 : Int)⟩),
        DataShape a.2.2.2 r.raw ∧ CurrentS1AccessAt spec config rows mapping ⟨dataVA p a.2.1, r, (a.2.2.1 : Int)⟩ data state)
    (codeReps : ∀ c ∈ cws, ∃ (r : S1LogicalReference.Request) (data : S1AccessData spec config rows ⟨codeVA base entry c.1, r, 4⟩),
        FetchShape r.raw ∧ CurrentS1AccessAt spec config rows mapping ⟨codeVA base entry c.1, r, 4⟩ data state) :
    ClosedMembershipAt spec config rows mapping (consumerMap accs cws entry p base mapping table) state := by
  apply closed_of_represented
  intro va acc aligned size permitted
  refine ⟨domainVA va acc size permitted ⟨acc, aligned⟩, ?_⟩
  rcases permitted with ⟨a, member, hva, hsize, shape⟩ | ⟨c, member, hva, hsize, shape⟩
  · obtain ⟨r, data, rshape, current⟩ := dataReps a member
    subst hva; subst hsize
    exact ⟨r, data, rshape.agree shape, current⟩
  · obtain ⟨r, data, rshape, current⟩ := codeReps c member
    subst hva; subst hsize
    exact ⟨r, data, rshape.agree shape, current⟩

/-- Per-case instances: case cNN's consumer map. -/
def caseMap (n : Nat) : Option (List Access × List (Nat × Nat) × Nat) :=
  match n with
  | 0 => some (R14Plan.accesses_c00, R14Plan.codeWords_c00, R14Plan.entry_c00)
  | 1 => some (R14Plan.accesses_c01, R14Plan.codeWords_c01, R14Plan.entry_c01)
  | 2 => some (R14Plan.accesses_c02, R14Plan.codeWords_c02, R14Plan.entry_c02)
  | 3 => some (R14Plan.accesses_c03, R14Plan.codeWords_c03, R14Plan.entry_c03)
  | 4 => some (R14Plan.accesses_c04, R14Plan.codeWords_c04, R14Plan.entry_c04)
  | 5 => some (R14Plan.accesses_c05, R14Plan.codeWords_c05, R14Plan.entry_c05)
  | 6 => some (R14Plan.accesses_c06, R14Plan.codeWords_c06, R14Plan.entry_c06)
  | 7 => some (R14Plan.accesses_c07, R14Plan.codeWords_c07, R14Plan.entry_c07)
  | 8 => some (R14Plan.accesses_c08, R14Plan.codeWords_c08, R14Plan.entry_c08)
  | 9 => some (R14Plan.accesses_c09, R14Plan.codeWords_c09, R14Plan.entry_c09)
  | 10 => some (R14Plan.accesses_c10, R14Plan.codeWords_c10, R14Plan.entry_c10)
  | 11 => some (R14Plan.accesses_c11, R14Plan.codeWords_c11, R14Plan.entry_c11)
  | 12 => some (R14Plan.accesses_c12, R14Plan.codeWords_c12, R14Plan.entry_c12)
  | 13 => some (R14Plan.accesses_c13, R14Plan.codeWords_c13, R14Plan.entry_c13)
  | _ => none

#print axioms consumer_agrees
#print axioms closed
end R14E17
