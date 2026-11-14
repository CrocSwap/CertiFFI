import ArmCertWalk.Profile

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

structure AttributeConfig where
  mair : BitVec 64
  mair2 : BitVec 64
  xs : Bool
  mte2 : Bool
  deriving DecidableEq, Repr

/-- Current walk-parameter data and source feature binding. Obtaining these
parameters from the actual register getter is a separate execution theorem. -/
structure AttributesAt (config : AttributeConfig) (params : S1TTWParams) (state : State) : Prop where
  mair : params.mair = config.mair
  mair2 : params.mair2 = config.mair2
  xs : state.regs.FeatureImpl[166] = config.xs
  mte2 : state.regs.FeatureImpl[134] = config.mte2

def descriptorIndex (descriptor : BitVec 64) : Fin 8 :=
  ⟨(descriptor.extractLsb' 2 3).toNat, (descriptor.extractLsb' 2 3).isLt⟩

def mairByte (mair : BitVec 64) (index : Fin 8) : BitVec 8 :=
  mair.extractLsb' (8 * index.val) 8

/-- Selected ordinary (AIE=0) slot only; unused slots are unconstrained. -/
def selectedAttribute (config : AttributeConfig) (descriptor : BitVec 64) : BitVec 8 :=
  mairByte config.mair (descriptorIndex descriptor)

def attributeHigh (attr : BitVec 8) : BitVec 4 :=
  Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb attr 7 4)

def attributeLow2 (attr : BitVec 8) : BitVec 2 :=
  Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb attr 1 0)

def attributeLow4 (attr : BitVec 8) : BitVec 4 :=
  Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb attr 3 0)

/-- Pure source reserved-encoding test, including conditional XS/MTE encodings.
It is not a proposition that a future native decoder succeeds. -/
def reservedAttribute (xs mte2 : Bool) (attr : BitVec 8) : Bool :=
  if (attributeHigh attr == 0#4) && (attributeLow2 attr == 1#2) then !xs
  else if attributeHigh attr == 0#4 then attributeLow2 attr != 0#2
  else if attr = 64#8 then !xs
  else if attr = 160#8 then !xs
  else if attr = 240#8 then !mte2
  else attributeLow4 attr == 0#4

def AttributeAdmissible (config : AttributeConfig) (attr : BitVec 8) : Prop :=
  reservedAttribute config.xs config.mte2 attr = false

theorem AttributesAt.of_regs {config : AttributeConfig} {params : S1TTWParams}
    {state other : State} (current : AttributesAt config params state)
    (registers : other.regs = state.regs) : AttributesAt config params other := by
  exact ⟨current.mair, current.mair2, by rw [registers]; exact current.xs,
    by rw [registers]; exact current.mte2⟩

theorem xs_feature_index : num_of_Feature .FEAT_XS = 166 := by decide
theorem mte2_feature_index : num_of_Feature .FEAT_MTE2 = 134 := by decide

#print axioms xs_feature_index
#print axioms mte2_feature_index
#print axioms AttributesAt.of_regs

end ArmCertWalk
