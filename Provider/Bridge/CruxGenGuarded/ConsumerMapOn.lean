import ArmCertTranslateModel.HeapV2E17Table
open Sail ArmFull
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmCert.Translate.Model.HeapV2E17
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

/-! a design decision: the heap-v2 consumer map restricted to a path-indexed set S of plan data
accesses (code fetches stay permitted). The full map is S = everything; trap paths L = 1/2
(trap at the CBZ before any x0/x1 data access) use S = nothing, so their E17 statement and
closed membership quantify only over the accesses the path actually reaches. -/

/-- Permitted accesses restricted to the data accesses in S (every plan code fetch kept). -/
def PermittedOn (S : Nat × Nat × Int × Nat × Bool → Prop) (p : Pins) (base : Nat) (va : BitVec 64)
    (acc : AccessDescriptor) (size : Int) : Prop :=
  (∃ access ∈ HeapV2Plan.symbolicAccesses, S access ∧ va = dataVA p access ∧
      size = (access.2.2.2.1 : Int) ∧ DataShape access.2.2.2.2 acc) ∨
    (∃ code ∈ HeapV2Plan.codeWords, va = codeVA base code.1 ∧ size = 4 ∧ FetchShape acc)

def consumerMapOn (S : Nat × Nat × Int × Nat × Bool → Prop) (p : Pins) (base : Nat)
    (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) : ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  ⟨fun va => BitVec.ofNat 56 ((mapping va).getD 0), fun va acc _ size => PermittedOn S p base va acc size, table⟩

/-- Path set of the trap paths that trap before any data access (L = 1, 2). -/
def noData : Nat × Nat × Int × Nat × Bool → Prop := fun _ => False

theorem permittedOn_all (p : Pins) (base : Nat) (va : BitVec 64) (acc : AccessDescriptor) (size : Int) :
    PermittedOn (fun _ => True) p base va acc size ↔ Permitted p base va acc size := by
  unfold PermittedOn Permitted
  constructor
  · rintro (⟨a, m, _, h⟩ | h)
    · exact Or.inl ⟨a, m, h⟩
    · exact Or.inr h
  · rintro (⟨a, m, h⟩ | h)
    · exact Or.inl ⟨a, m, trivial, h⟩
    · exact Or.inr h

/-- A restricted map's permitted set is a subset of the full map's. -/
theorem permittedOn_sub {S : Nat × Nat × Int × Nat × Bool → Prop} {p : Pins} {base : Nat} {va : BitVec 64}
    {acc : AccessDescriptor} {size : Int} (h : PermittedOn S p base va acc size) : Permitted p base va acc size := by
  rcases h with ⟨a, m, _, h⟩ | h
  · exact Or.inl ⟨a, m, h⟩
  · exact Or.inr h

/-- Code-only maps permit no data access: every permitted VA is a plan code word. -/
theorem noData_code {p : Pins} {base : Nat} {va : BitVec 64} {acc : AccessDescriptor} {size : Int}
    (h : PermittedOn noData p base va acc size) :
    ∃ code ∈ HeapV2Plan.codeWords, va = codeVA base code.1 ∧ size = 4 ∧ FetchShape acc := by
  rcases h with ⟨_, _, f, _⟩ | h
  · exact f.elim
  · exact h

/-- Agreement for a restricted map, from mapping every permitted VA below 2^56. -/
theorem consumerOn_agrees {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (S : Nat × Nat × Int × Nat × Bool → Prop) (p : Pins) (base : Nat) (mapping : BitVec 64 → Option Nat)
    (mapped : ∀ va acc size, PermittedOn S p base va acc size → ∃ pa, mapping va = some pa ∧ pa < 2 ^ 56) :
    ConsumerMapAgrees spec mapping (consumerMapOn S p base mapping (rowsFootprint spec.imageRows).byte) := by
  refine ⟨?_, fun _ inside => inside⟩
  intro va acc aligned size permitted
  obtain ⟨pa, hm, bound⟩ := mapped va acc size permitted
  simp only [consumerMapOn, hm, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

#print axioms permittedOn_all
#print axioms consumerOn_agrees
end ArmCert.Translate.Model.HeapV2E17
