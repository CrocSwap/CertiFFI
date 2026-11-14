-- heap-v2 premise D, the closed-membership transfer from the shim consumer map
-- (Release.shimMap: PermittedShim with the data filter True = every plan data access, every body code word, plus the shim
-- code words and the 16-byte slot) to the body's plan map (E17General.cmap). Closed membership quantifies over the
-- permitted accesses only, and the body map's permitted set is contained in the shim map's, so it transfers unchanged.
import Bridge.CruxGenGuarded.ReleaseHeadline
import HeapV2StepCerts.E17General.Base
import RtShim2.ShimInv
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
set_option autoImplicit false
namespace TranslateShim

/-- Closed membership for the shim map gives closed membership for the body's plan map, at any state. -/
theorem closed_cmap_of_shimMap {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {base : BitVec 64} {pins : HeapV2E17.Pins}
    {s : ArmCertWalk.State}
    (h : ClosedMembershipAt spec config rows mapping (ArmBridge.CruxGenGuarded.Release.shimMap spec mapping base pins) s) :
    ClosedMembershipAt spec config rows mapping (HeapV2StepCerts.E17General.cmap spec mapping base pins) s := by
  intro va acc aligned size perm
  apply h va acc aligned size
  rcases perm with ⟨a, m, hva, hs, sh⟩ | ⟨c, m, hva, hs, sh⟩
  · exact Or.inl (Or.inl ⟨a, m, trivial, hva, hs, sh⟩)
  · exact Or.inl (Or.inr ⟨c, m, hva, hs, sh⟩)

/-- form: from the shim invariant at step 7 (body entry), closed membership for cmap at the body's
    before-fetch state. -/
theorem closed_cmap_of_shim {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {base : BitVec 64} {pins : HeapV2E17.Pins}
    {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word} {offS : Nat → BitVec 64}
    {budget : Nat} (x : NativeState)
    (i7 : RtShim2.ShimInv spec config rows mapping (ArmBridge.CruxGenGuarded.Release.shimMap spec mapping base pins)
      scope image loadBase base offS budget 7 x) :
    ClosedMembershipAt spec config rows mapping (HeapV2StepCerts.E17General.cmap spec mapping base pins)
      (ArmBridge.CruxGenGuarded.beforeFetchState x) :=
  closed_cmap_of_shimMap i7.v2.closed

#print axioms closed_cmap_of_shimMap
#print axioms closed_cmap_of_shim
end TranslateShim
