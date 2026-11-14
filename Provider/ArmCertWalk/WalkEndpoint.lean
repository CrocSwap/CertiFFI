import ArmCertWalk.WalkCalleeInputs

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk
abbrev WalkVars := S1OuterBody.Vars

def walkCurrent : WalkVars → TTWState | (_, _, _, _, _, _, _, _, _, current) => current
def walkDescriptor : WalkVars → BitVec 64 | (_, _, descriptor, _, _, _, _, _, _, _) => descriptor
def walkSlot : WalkVars → FullAddress | (_, slot, _, _, _, _, _, _, _, _) => slot
def walkFault : WalkVars → FaultRecord | (_, _, _, _, fault, _, _, _, _, _) => fault
def walkStop : WalkVars → Bool | (_, _, _, kind, _, _, _, _, _, _) => kind == .DescriptorType_Leaf

/-- Data extracted from the actual source endpoint. The inherited permission
prior is tied to the existing Path annotation by the execution theorem. -/
def WalkLeafEndpoint (params : S1TTWParams) (config : AttributeConfig)
    (controls : S1LogicalReference.Controls) (overlay : Bool) (level : Nat)
    (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (prior : S1LogicalReference.TablePermissions) (out : WalkVars) (state : State) : Prop :=
  ∃ leafCurrent descriptor,
    leafCurrent.level = (level : Int) ∧ leafCurrent.disch = 0#1 ∧
    nativeTablePermissionProjection leafCurrent.permissions = prior ∧
    S1DescriptorPIE.view (params.pie == 1#1) (params.ha == 1#1) (params.hd == 1#1) descriptor = view ∧
    S1ByteMemory.DescAt state.mem physical.address.toNat descriptor ∧
    walkDescriptor out = descriptor ∧ walkSlot out = physical ∧ walkStop out = true ∧
    (walkFault out).statuscode = .Fault_None ∧
    LeafMeaning config controls params overlay leafCurrent level descriptor (walkCurrent out)

#print axioms WalkLeafEndpoint
end ArmCertWalk
