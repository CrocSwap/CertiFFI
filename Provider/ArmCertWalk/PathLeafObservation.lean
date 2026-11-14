import ArmCertWalk.PathEndpointBounds

open Sail ArmFull
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem path_leaf_observed {observe : S1LogicalReference.Observation} {paBits : Nat} {va : BitVec 64}
    {level bits : Nat} {base : BitVec 48} {endpoint : S1LogicalReference.PathEnd}
    (path : S1LogicalReference.Path observe paBits va level bits base endpoint)
    (leafLevel leafLogical : Nat) (leafPhysical : FullAddress) (leafView : S1DescriptorPIE.View 64)
    (successful : endpoint = .leaf leafLevel leafLogical leafPhysical leafView) :
    observe leafLogical leafPhysical leafView := by
  induction path generalizing leafLevel leafLogical leafPhysical leafView with
  | invalid => cases successful
  | range => cases successful
  | leaf level bits base physical view valid aligned present kind =>
    cases successful
    exact present
  | table level bits base physical view endpoint valid aligned present kind inRange tail ih =>
    exact ih leafLevel leafLogical leafPhysical leafView successful

#print axioms path_leaf_observed
end ArmCertWalk
