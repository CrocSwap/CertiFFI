-- Extract only the queries of the selected actual native plan from the current invariant.
import ArmCertTranslateModel.ClosedTable
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.SelectedCurrent

theorem point {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping consumer state)
    (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int)
    (permitted : consumer.permitted va acc aligned size) :
    ∃ data : S1AccessData spec config rows ⟨va,⟨acc,aligned⟩,size⟩,
      domain ⟨va,⟨acc,aligned⟩,size⟩ ∧
      CurrentS1AccessAt spec config rows mapping ⟨va,⟨acc,aligned⟩,size⟩ data state := by
  obtain ⟨query,hva,hraw,haligned,hsize,member,data,current⟩ := closed va acc aligned size permitted
  rcases query with ⟨v,⟨raw,a⟩,sz⟩
  change v = va at hva
  change raw = acc at hraw
  change a = aligned at haligned
  change sz = size at hsize
  subst v
  subst raw
  subst a
  subst sz
  exact ⟨data,member,current⟩

/-- Static permissions describe only one chosen plan's indices. Instantiating
with Fin 16, Fin 2 or Unit gives the byte, half-pair or single-pair families.
The invariant is at this one state; concrete entry and run preservation remain
separate proof duties, never future-success callbacks in a caller contract. -/
theorem family {ι : Type} {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {state : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping consumer state)
    (addresses : ι → BitVec 64) (aligned : ι → Bool) (sizes : ι → Int) (write : Bool)
    (members : ∀ i acc, DataShape write acc → consumer.permitted (addresses i) acc (aligned i) (sizes i)) :
    ∃ data : ∀ i acc, DataShape write acc →
        S1AccessData spec config rows ⟨addresses i,⟨acc,aligned i⟩,sizes i⟩,
      ∀ i acc shape, domain ⟨addresses i,⟨acc,aligned i⟩,sizes i⟩ ∧
        CurrentS1AccessAt spec config rows mapping
          ⟨addresses i,⟨acc,aligned i⟩,sizes i⟩ (data i acc shape) state := by
  have each := fun i acc shape => point closed (addresses i) acc (aligned i) (sizes i) (members i acc shape)
  refine ⟨fun i acc shape => (each i acc shape).choose, ?_⟩
  intro i acc shape
  exact (each i acc shape).choose_spec

#print axioms point
#print axioms family
end TranslateSpan.SelectedCurrent
