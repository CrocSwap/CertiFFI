import ArmCertTranslateModel.ClosedTable
import ArmCertLoop.Bytes

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
open ArmCert.Translate.Model

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

namespace ArmCertLoop.SpanMap

/-- One symbolic byte range. A list of two spans covers an arbitrary-length
copy without enumerating one access or one SSA input per byte. -/
structure Span where
  base : BitVec 64
  length : Nat
  write : Bool

def byteVA (span : Span) (i : Nat) : BitVec 64 := span.base + BitVec.ofNat 64 i

/-- Explicit C-object geometry; the one-past value is never dereferenced. -/
def NoWrap (span : Span) : Prop := span.base.toNat + span.length ≤ 2 ^ 64

def InUnion (spans : List Span) (va : BitVec 64) : Prop :=
  ∃ span ∈ spans, ∃ i, i < span.length ∧ va = byteVA span i

/-- Injectivity on the accessed union only. Other deployment aliases are free. -/
def UnionInjective (mapping : BitVec 64 → Option Nat) (spans : List Span) : Prop :=
  ∀ a b pa, InUnion spans a → InUnion spans b →
    mapping a = some pa → mapping b = some pa → a = b

theorem byteVA_toNat (span : Span) (nowrap : NoWrap span) (i : Nat) (room : i < span.length) :
    (byteVA span i).toNat = span.base.toNat + i := by
  have inside : i < 2 ^ 64 := by unfold NoWrap at nowrap; omega
  have sumInside : span.base.toNat + i < 2 ^ 64 := by unfold NoWrap at nowrap; omega
  simp only [byteVA, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt inside,
    Nat.mod_eq_of_lt sumInside]

theorem forward_va_ne (src dst : Span) (sourceObject : NoWrap src) (destObject : NoWrap dst)
    (direction : dst.base.toNat ≤ src.base.toNat)
    (i j : Nat) (ir : i < dst.length) (jr : j < src.length) (later : i < j) :
    byteVA src j ≠ byteVA dst i := by
  intro equal
  have e := congrArg BitVec.toNat equal
  rw [byteVA_toNat src sourceObject j jr, byteVA_toNat dst destObject i ir] at e
  exact ArmCertLoop.Bytes.forward_address_ne direction later e

theorem backward_va_ne (src dst : Span) (sourceObject : NoWrap src) (destObject : NoWrap dst)
    (direction : src.base.toNat < dst.base.toNat)
    (i j : Nat) (ir : i < dst.length) (jr : j < src.length) (earlier : j < i) :
    byteVA src j ≠ byteVA dst i := by
  intro equal
  have e := congrArg BitVec.toNat equal
  rw [byteVA_toNat src sourceObject j jr, byteVA_toNat dst destObject i ir] at e
  exact ArmCertLoop.Bytes.backward_address_ne direction earlier e

theorem mapped_different (mapping : BitVec 64 → Option Nat) (spans : List Span)
    (injective : UnionInjective mapping spans) (a b : BitVec 64)
    (ha : InUnion spans a) (hb : InUnion spans b)
    (ma : ∃ pa, mapping a = some pa) (mb : ∃ pa, mapping b = some pa)
    (different : a ≠ b) : (mapping a).getD 0 ≠ (mapping b).getD 0 := by
  intro equal
  obtain ⟨pa, ea⟩ := ma
  obtain ⟨pb, eb⟩ := mb
  have same : pa = pb := by simpa only [ea, eb, Option.getD_some] using equal
  subst pb
  exact different (injective a b pa ha hb ea eb)

def Permitted (spans : List Span) (code : List (BitVec 64))
    (va : BitVec 64) (acc : AccessDescriptor) (size : Int) : Prop :=
  (∃ span ∈ spans, ∃ i, i < span.length ∧ va = byteVA span i ∧ size = 1 ∧ DataShape span.write acc) ∨
  (va ∈ code ∧ size = 4 ∧ FetchShape acc)

def consumerMap (spans : List Span) (code : List (BitVec 64))
    (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) :
    ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  ⟨fun va => BitVec.ofNat 56 ((mapping va).getD 0),
    fun va acc aligned size => aligned = true ∧ Permitted spans code va acc size, table⟩

theorem data_permitted (spans : List Span) (code : List (BitVec 64))
    (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (span : Span) (member : span ∈ spans) (i : Nat) (room : i < span.length)
    (acc : AccessDescriptor) (shape : DataShape span.write acc) :
    (consumerMap spans code mapping table).permitted (byteVA span i) acc true 1 :=
  ⟨rfl, Or.inl ⟨span, member, i, room, rfl, rfl, shape⟩⟩

theorem fetch_permitted (spans : List Span) (code : List (BitVec 64))
    (mapping : BitVec 64 → Option Nat) (table : Nat → Prop)
    (va : BitVec 64) (member : va ∈ code) (acc : AccessDescriptor) (shape : FetchShape acc) :
    (consumerMap spans code mapping table).permitted va acc true 4 :=
  ⟨rfl, Or.inr ⟨member, rfl, shape⟩⟩

/-- Address-only static agreement; no future run or state-universal premise. -/
theorem consumer_agrees {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (spans : List Span) (code : List (BitVec 64)) (mapping : BitVec 64 → Option Nat)
    (mapped : ∀ va acc size, Permitted spans code va acc size →
      ∃ pa, mapping va = some pa ∧ pa < 2 ^ 56) :
    ConsumerMapAgrees spec mapping
      (consumerMap spans code mapping (rowsFootprint spec.imageRows).byte) := by
  refine ⟨?_, fun _ inside => inside⟩
  intro va acc aligned size permitted
  obtain ⟨pa, hm, bound⟩ := mapped va acc size permitted.2
  simp only [consumerMap, hm, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

/-- Construct closed query membership at ONE current state from symbolic
per-byte representatives. Consumers derive representatives/preservation
internally after entry; this is a conditional helper, not a public card. -/
theorem closed {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (spans : List Span) (code : List (BitVec 64)) (table : Nat → Prop) (state : ArmCertWalk.State)
    (domainActual : ∀ va acc aligned size,
      (consumerMap spans code mapping table).permitted va acc aligned size →
      domain ⟨va, ⟨acc, aligned⟩, size⟩)
    (dataReps : ∀ span ∈ spans, ∀ i, i < span.length →
      ∃ (r : S1LogicalReference.Request)
        (data : S1AccessData spec config rows ⟨byteVA span i, r, 1⟩),
        DataShape span.write r.raw ∧
        CurrentS1AccessAt spec config rows mapping ⟨byteVA span i, r, 1⟩ data state)
    (codeReps : ∀ va ∈ code, ∃ (r : S1LogicalReference.Request)
      (data : S1AccessData spec config rows ⟨va, r, 4⟩),
      FetchShape r.raw ∧ CurrentS1AccessAt spec config rows mapping ⟨va, r, 4⟩ data state) :
    ClosedMembershipAt spec config rows mapping (consumerMap spans code mapping table) state := by
  apply closed_of_represented
  intro va acc aligned size permitted
  refine ⟨domainActual va acc aligned size permitted, ?_⟩
  rcases permitted.2 with ⟨span, member, i, room, hva, hsize, shape⟩ | ⟨member, hsize, shape⟩
  · obtain ⟨r, data, rshape, current⟩ := dataReps span member i room
    subst va; subst size
    exact ⟨r, data, rshape.agree shape, current⟩
  · obtain ⟨r, data, rshape, current⟩ := codeReps va member
    subst size
    exact ⟨r, data, rshape.agree shape, current⟩

#print axioms data_permitted
#print axioms byteVA_toNat
#print axioms forward_va_ne
#print axioms backward_va_ne
#print axioms mapped_different
#print axioms fetch_permitted
#print axioms consumer_agrees
#print axioms closed

end ArmCertLoop.SpanMap
