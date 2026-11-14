import ArmCertWalk.AttributeStages
import ArmCertWalk.CacheFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

def BodyInterprets (attr : BitVec 8) (actual : MemoryAttributes) : Prop :=
  (attributeProjection actual).kind = (decodedAttributeBody attr 0#1).kind ∧
    actual.xs = (decodedAttributeBody attr 0#1).xs

theorem xs_current_eq (config : AttributeConfig) (params : S1TTWParams) (state : State)
    (current : ActiveAttributesAt config params state) :
    HaveFeatXS () state = .ok config.xs state := by
  change EStateM.Result.ok state.regs.FeatureImpl[166] state = _
  rw [current.xs]

theorem mte2_current_eq (config : AttributeConfig) (params : S1TTWParams) (state : State)
    (current : ActiveAttributesAt config params state) :
    HaveMTE2Ext () state = .ok config.mte2 state := by
  change EStateM.Result.ok state.regs.FeatureImpl[134] state = _
  rw [current.mte2]

theorem admissible_64_xs (config : AttributeConfig)
    (admissible : AttributeAdmissible config 64#8) : config.xs = true := by
  simpa [AttributeAdmissible, reservedAttribute, attributeHigh, attributeLow2,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.castWidth] using admissible

theorem admissible_160_xs (config : AttributeConfig)
    (admissible : AttributeAdmissible config 160#8) : config.xs = true := by
  simpa [AttributeAdmissible, reservedAttribute, attributeHigh, attributeLow2,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.castWidth] using admissible

theorem admissible_240_mte2 (config : AttributeConfig)
    (admissible : AttributeAdmissible config 240#8) : config.mte2 = true := by
  simpa [AttributeAdmissible, reservedAttribute, attributeHigh, attributeLow2,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.castWidth] using admissible

#print axioms xs_current_eq
#print axioms mte2_current_eq
#print axioms admissible_64_xs
#print axioms admissible_160_xs
#print axioms admissible_240_mte2

end ArmCertWalk
