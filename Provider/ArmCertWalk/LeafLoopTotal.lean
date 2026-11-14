import ArmCertWalk.LeafNextTotal
import Walk.S1WalkLeaf
import Walk.S1LeafShape

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem leaf_source_loop_total (config : AttributeConfig) (controls : S1LogicalReference.Controls)
    (params : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2 aligned : Bool)
    (descaddr : FullAddress) (descriptor : BitVec 64) (oldType : DescriptorType)
    (fault : FaultRecord) (oldNew : BitVec 64) (a64 : Bool) (s2fault : FaultRecord)
    (skl : BitVec 2) (current : TTWState) (level : Nat) (state : State)
    (d128 : params.d128 = 0#1) (ds : params.ds = 0#1) (tg : params.tgx = .TGx_4KB)
    (aie : params.aie = 0#1) (pnch : params.pnch = 0#1)
    (nonsecure : current.baseaddress.paspace = .PAS_NonSecure)
    (ss : acc.ss = .SS_NonSecure) (currentLevel : current.level = (level : Int))
    (leaf : S1DecodeFacts.classify descriptor current.level = .DescriptorType_Leaf)
    (activeAttrs : ActiveAttributesAt config params state)
    (admissible : AttributeAdmissible config (selectedAttribute config descriptor))
    (binding : LeafPermissionControls params (outputOverlayEnabled state.regs) controls) :
    ∃ next other,
      S1WalkSource.named.loop1 params va .Regime_EL20 acc 64 descaddr oldType skl current
        walkaddr ti aligned descriptor fault a64 s2fault s2 oldNew state =
        .ok (.ok (aligned, descaddr, descriptor, .DescriptorType_Leaf, fault, descriptor,
          a64, s2fault, skl, next)) other ∧
      LeafMeaning config controls params (outputOverlayEnabled state.regs) current level descriptor next ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  have levels := S1LeafShape.leaf_levels descriptor current.level leaf
  obtain ⟨next, other, nextCall, meaning, registers, memory, events⟩ :=
    leaf_next_canonical_total config controls current level s2 params descriptor state nonsecure
      currentLevel (by omega) (by omega) aie d128 ds pnch tg activeAttrs admissible binding
  have body : S1WalkSource.named.body1 params va .Regime_EL20 acc 64 walkaddr ti s2
      (aligned, descaddr, descriptor, oldType, fault, oldNew, a64, s2fault, skl, current) state =
      .ok (.ok (aligned, descaddr, descriptor, .DescriptorType_Leaf, fault, descriptor,
        a64, s2fault, skl, next)) other := by
    rw [S1WalkLeaf.equation params va .Regime_EL20 acc walkaddr ti s2 aligned descaddr descriptor
      oldType fault oldNew a64 s2fault skl current state d128 ds tg leaf]
    simp [S1WalkLeaf.action, ss, Bind.bind, Pure.pure, ExceptT.bind,
      ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift, EStateM.bind,
      EStateM.pure, Functor.map, EStateM.map, liftM, MonadLiftT.monadLift, MonadLift.monadLift, nextCall]
  have trace : S2Loop.Trace S1WalkInvalid.stop
      (S1WalkSource.named.body1 params va .Regime_EL20 acc 64 walkaddr ti s2)
      1 (aligned, descaddr, descriptor, oldType, fault, oldNew, a64, s2fault, skl, current) state
      (.ok (aligned, descaddr, descriptor, .DescriptorType_Leaf, fault, descriptor,
        a64, s2fault, skl, next)) other := .done body (by simp [S1WalkInvalid.stop])
  refine ⟨next, other, ?_, meaning, registers, memory, events⟩
  simpa only [S1WalkSource.named.loop1, S1WalkInvalid.stop] using
    S2Loop.execute trace 1048576 (by decide)

#print axioms leaf_source_loop_total
end ArmCertWalk
