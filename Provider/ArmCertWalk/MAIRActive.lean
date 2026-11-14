import ArmCertWalk.MAIRSelect

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

/-- Ordinary AIE=0 selection needs no binding for the inactive MAIR2 word. -/
structure ActiveAttributesAt (config : AttributeConfig) (params : S1TTWParams)
    (state : State) : Prop where
  mair : params.mair = config.mair
  xs : state.regs.FeatureImpl[166] = config.xs
  mte2 : state.regs.FeatureImpl[134] = config.mte2

theorem ActiveAttributesAt.of_regs {config : AttributeConfig} {params : S1TTWParams}
    {state other : State} (current : ActiveAttributesAt config params state)
    (registers : other.regs = state.regs) : ActiveAttributesAt config params other := by
  exact ⟨current.mair, by rw [registers]; exact current.xs,
    by rw [registers]; exact current.mte2⟩

theorem selectedAttribute_active_eq (config : AttributeConfig) (params : S1TTWParams)
    (state : State) (current : ActiveAttributesAt config params state) (descriptor : BitVec 64) :
    AArch64_MAIRAttr (S1MAIRKernel.index descriptor) params.mair2 params.mair state =
      .ok (selectedAttribute config descriptor) state := by
  rw [descriptorIndex_source, current.mair]
  exact mairAttr_eq (descriptorIndex descriptor) config.mair params.mair2 state

theorem reservedAttribute_active_eq (config : AttributeConfig) (params : S1TTWParams)
    (state : State) (current : ActiveAttributesAt config params state) (attr : BitVec 8) :
    S1ConstrainUnpredictableRESMAIR attr true state =
      .ok (reservedAttribute config.xs config.mte2 attr) state := by
  let actual : AttributeConfig := {config with mair2 := params.mair2}
  have full : AttributesAt actual params state :=
    ⟨current.mair, rfl, current.xs, current.mte2⟩
  exact reservedAttribute_eq actual params state full attr

#print axioms ActiveAttributesAt.of_regs
#print axioms selectedAttribute_active_eq
#print axioms reservedAttribute_active_eq

end ArmCertWalk
