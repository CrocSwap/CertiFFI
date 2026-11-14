-- One fixed consumer map, containing only the native selector's chosen pair plan.
import NativeAccess.PairGeometry
import TranslateSpan.SelectedCurrent
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.SelectedMap

structure Site where
  address : BitVec 64
  write : Bool

def pairPermitted (site : Site) (va : BitVec 64) (acc : AccessDescriptor)
    (aligned : Bool) (size : Int) : Prop :=
  DataShape site.write acc ∧
  match NativeAccess.PairGeometry.selected site.address with
  | .one16 => va = site.address ∧ aligned = NativeAccess.Logical.accessAligned site.address 16 true ∧ size = 16
  | .two8 => ∃ j : Fin 2, va = NativeAccess.PairSplit.halfAddress site.address j ∧ aligned = true ∧ size = 8
  | .bytes => ∃ j : Fin 16, va = site.address + BitVec.ofNat 64 j.val ∧ size = 1

/-- Byte flags form the VA-keyed domain envelope used by the actual DEVPAGE2
producer. Actual trace flags remain unchanged; no unused widths are included. -/
def permitted (sites : List Site) (code : List (BitVec 64)) (va : BitVec 64)
    (acc : AccessDescriptor) (aligned : Bool) (size : Int) : Prop :=
  (va ∈ code ∧ FetchShape acc ∧ aligned = true ∧ size = 4) ∨
  ∃ site ∈ sites, pairPermitted site va acc aligned size

def consumerMap (sites : List Site) (code : List (BitVec 64))
    (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) :
    ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  ⟨fun va => BitVec.ofNat 56 ((mapping va).getD 0), permitted sites code, table⟩

theorem fetch_member (sites : List Site) (code : List (BitVec 64))
    (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (va : BitVec 64)
    (acc : AccessDescriptor) (member : va ∈ code) (shape : FetchShape acc) :
    (consumerMap sites code mapping table).permitted va acc true 4 :=
  Or.inl ⟨member,shape,rfl,rfl⟩

theorem one_member (sites : List Site) (code : List (BitVec 64))
    (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (site : Site)
    (member : site ∈ sites) (chosen : NativeAccess.PairGeometry.selected site.address = .one16)
    (acc : AccessDescriptor) (shape : DataShape site.write acc) :
    (consumerMap sites code mapping table).permitted site.address acc
      (NativeAccess.Logical.accessAligned site.address 16 true) 16 := by
  refine Or.inr ⟨site,member,shape,?_⟩
  rw [chosen]
  exact ⟨rfl,rfl,rfl⟩

theorem half_member (sites : List Site) (code : List (BitVec 64))
    (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (site : Site)
    (member : site ∈ sites) (chosen : NativeAccess.PairGeometry.selected site.address = .two8)
    (j : Fin 2) (acc : AccessDescriptor) (shape : DataShape site.write acc) :
    (consumerMap sites code mapping table).permitted
      (NativeAccess.PairSplit.halfAddress site.address j) acc true 8 := by
  refine Or.inr ⟨site,member,shape,?_⟩
  rw [chosen]
  exact ⟨j,rfl,rfl,rfl⟩

theorem byte_member (sites : List Site) (code : List (BitVec 64))
    (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (site : Site)
    (member : site ∈ sites) (chosen : NativeAccess.PairGeometry.selected site.address = .bytes)
    (j : Fin 16) (acc : AccessDescriptor) (shape : DataShape site.write acc) (aligned : Bool) :
    (consumerMap sites code mapping table).permitted
      (site.address + BitVec.ofNat 64 j.val) acc aligned 1 := by
  refine Or.inr ⟨site,member,shape,?_⟩
  rw [chosen]
  exact ⟨j,rfl,rfl⟩

theorem agrees {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (sites : List Site) (code : List (BitVec 64)) (mapping : BitVec 64 → Option Nat)
    (mapped : ∀ va acc aligned size, permitted sites code va acc aligned size →
      ∃ pa, mapping va = some pa ∧ pa < 2 ^ 56) :
    ConsumerMapAgrees spec mapping (consumerMap sites code mapping (rowsFootprint spec.imageRows).byte) := by
  refine ⟨?_,fun _ member => member⟩
  intro va acc aligned size member
  obtain ⟨pa,map,bound⟩ := mapped va acc aligned size member
  simpa only [consumerMap,map,Option.getD_some,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] using map

#print axioms pairPermitted
#print axioms permitted
#print axioms consumerMap
#print axioms fetch_member
#print axioms one_member
#print axioms half_member
#print axioms byte_member
#print axioms agrees
end TranslateSpan.SelectedMap
