import TranslateSpan.CheckedTopology
import TranslateSpan.DefaultContext
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace DitShim243.TopologyTransport
open TranslateSpan.CheckedTopology

/-- Query envelopes change only the certificate's proof fields. The logical
rows, image, hardware controls and native current-state facts remain identical. -/
theorem current (raw : Raw) (a b : List (BitVec 64)) (fuel : Nat)
    (ha : check raw a fuel = true) (hb : check raw b fuel = true)
    (config : AttributeConfig) (rows : List PermissionRow) (s : ArmCertWalk.State)
    (c : CurrentS1At (spec raw a fuel ha) config rows s) :
    CurrentS1At (spec raw b fuel hb) config rows s :=
  ⟨⟨c.images.covered, c.images.topology, c.images.attributes, c.images.writeback, c.images.permissions⟩,
    c.host, c.core, c.geometry, c.guards, c.rawFault, c.enabled, c.cache⟩

def accessData (raw : Raw) (a b : List (BitVec 64)) (fuel : Nat)
    (ha : check raw a fuel = true) (hb : check raw b fuel = true)
    (config : AttributeConfig) (rows : List PermissionRow) (q : AccessQuery)
    (d : S1AccessData (spec raw a fuel ha) config rows q) :
    S1AccessData (spec raw b fuel hb) config rows q :=
  ⟨d.leafLevel,d.logical,d.physical,d.view,d.path,⟨d.permissions.row,d.permissions.member,d.permissions.slot,d.permissions.words,
    d.permissions.annotation,d.permissions.used,d.permissions.rowView,d.permissions.attributes,
    d.permissions.kind,d.permissions.read,d.permissions.write,d.permissions.tagaccess⟩,d.lower,d.accessEL,d.nonsecure⟩

theorem access (raw : Raw) (a b : List (BitVec 64)) (fuel : Nat)
    (ha : check raw a fuel = true) (hb : check raw b fuel = true)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (q : AccessQuery) (d : S1AccessData (spec raw a fuel ha) config rows q) (s : ArmCertWalk.State)
    (c : CurrentS1AccessAt (spec raw a fuel ha) config rows mapping q d s) :
    CurrentS1AccessAt (spec raw b fuel hb) config rows mapping q
      (accessData raw a b fuel ha hb config rows q d) s :=
  ⟨c.layout,c.checks,c.epd,c.map,c.outputPolicy⟩

theorem closed (raw : Raw) (a b : List (BitVec 64)) (fuel : Nat)
    (ha : check raw a fuel = true) (hb : check raw b fuel = true)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (outer inner : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (s : ArmCertWalk.State)
    (subset : ∀ va acc aligned size, inner.permitted va acc aligned size → outer.permitted va acc aligned size)
    (domain : ∀ va acc aligned size, inner.permitted va acc aligned size → va ∈ b)
    (c : ClosedMembershipAt (spec raw a fuel ha) config rows mapping outer s) :
    ClosedMembershipAt (spec raw b fuel hb) config rows mapping inner s := by
  intro va acc aligned size permitted
  obtain ⟨q,hva,hacc,hal,hsize,_,d,currentAccess⟩ := c va acc aligned size (subset va acc aligned size permitted)
  refine ⟨q,hva,hacc,hal,hsize,?_,accessData raw a b fuel ha hb config rows q d,?_⟩
  · change q.va ∈ b
    rw [hva]; exact domain va acc aligned size permitted
  · exact access raw a b fuel ha hb config rows mapping q d s currentAccess

#print axioms current
#print axioms access
#print axioms closed
end DitShim243.TopologyTransport
