import Walk.S1WalkInvalid
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1WalkLeaf
abbrev State := S1WalkInvalid.State
abbrev Return := S1WalkInvalid.Return
abbrev Vars := S1WalkInvalid.Vars

def action (wp : S1TTWParams) (regime : Regime) (acc : AccessDescriptor)
    (s2fs1mro aligned : Bool) (descaddr : FullAddress) (d : BitVec 64)
    (fault : FaultRecord) (a64 : Bool) (s2fault : FaultRecord)
    (skl : BitVec 2) (current : TTWState) : SailME Return Vars := do
  let next ← AArch64_S1NextWalkStateLeaf current s2fs1mro regime acc.ss wp d
  pure (aligned, descaddr, d, .DescriptorType_Leaf, fault, d, a64, s2fault, skl, next)

/- Structural equation only: next-leaf source call is explicit, not a totality premise. -/
theorem equation (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (walkaddr : AddressDescriptor) (ti : TranslationInfo)
    (s2fs1mro aligned : Bool) (descaddr : FullAddress) (d : BitVec 64)
    (oldType : DescriptorType) (fault : FaultRecord) (oldNew : BitVec 64)
    (a64 : Bool) (s2fault : FaultRecord) (skl : BitVec 2) (current : TTWState)
    (s : State) (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1)
    (hTG : wp.tgx = .TGx_4KB)
    (hLeaf : S1DecodeFacts.classify d current.level = .DescriptorType_Leaf) :
    S1WalkSource.named.body1 wp va regime acc 64 walkaddr ti s2fs1mro
      (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s =
      action wp regime acc s2fs1mro aligned descaddr d fault a64 s2fault skl current s := by
  have hdec : AArch64_DecodeDescriptorType d 0#1 0#1 .TGx_4KB current.level =
      (pure .DescriptorType_Leaf : SailM DescriptorType) := by
    funext t
    rw [S1DecodeFacts.model_eq, hLeaf]
    rfl
  simp only [S1WalkSource.named.body1, hD128, hDS, hTG, hdec]
  simp [action, Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.mk, ExceptT.lift, EStateM.bind, EStateM.map, EStateM.pure,
    liftM, MonadLiftT.monadLift, MonadLift.monadLift, ArmFull.assert, PreSail.assert]
  cases hr : AArch64_S1NextWalkStateLeaf current s2fs1mro regime acc.ss wp d s <;>
    simp [hr, EStateM.bind, EStateM.pure, ExceptT.bindCont]
#print axioms equation
end S1WalkLeaf
