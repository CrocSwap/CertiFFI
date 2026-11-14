import ArmCertWalk.AttributeInputs
import Walk.S1MAIRAttr
import Walk.S1RESMAIR
import Walk.S1MAIRKernel

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertWalk

private theorem extractCast_eq {width count : Nat} (value : BitVec width) (high low : Nat)
    (length : high - low + 1 = count) :
    Sail.BitVec.castWidth (m := count) (Sail.BitVec.extractLsb value high low) =
      value.extractLsb' low count := by
  subst count
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb]

theorem mairAttr_eq (index : Fin 8) (mair mair2 : BitVec 64) (state : State) :
    AArch64_MAIRAttr (index.val : Int) mair2 mair state =
      .ok (mairByte mair index) state := by
  have lower : (0 : Int) ≤ index.val := by omega
  have upper : (index.val : Int) < 8 := by have bound := index.isLt; omega
  have endBound : 8 * (index.val : Int) + 7 < 64 := by omega
  have endNonnegative : 0 ≤ 8 * (index.val : Int) + 7 := by omega
  have startNat : (8 * (index.val : Int)).toNat = 8 * index.val := by omega
  have endNat : (8 * (index.val : Int) + 7).toNat = 8 * index.val + 7 := by omega
  rw [S1MAIRAttr.complete]
  delta S1MAIRAttr.native
  simp [mairByte, upper, show ¬ (index.val : Int) > 7 by omega,
    show 0 ≤ 8 * (index.val : Int) by omega,
    show 8 * (index.val : Int) ≤ 8 * (index.val : Int) + 7 by omega,
    endBound, endNonnegative, Sail.Int.toNatChecked]
  rw [extractCast_eq mair _ _ (by omega)]
  rw [startNat]

theorem reservedAttribute_eq (config : AttributeConfig) (params : S1TTWParams)
    (state : State) (current : AttributesAt config params state) (attr : BitVec 8) :
    S1ConstrainUnpredictableRESMAIR attr true state =
      .ok (reservedAttribute config.xs config.mte2 attr) state := by
  rw [S1RESMAIR.complete]
  delta S1RESMAIR.native
  simp [reservedAttribute, attributeHigh, attributeLow2, attributeLow4,
    current.xs, current.mte2]

theorem descriptorIndex_source (descriptor : BitVec 64) :
    S1MAIRKernel.index descriptor = ((descriptorIndex descriptor).val : Int) := by
  change (((0 : Nat) <<< 3 ||| (Sail.BitVec.extractLsb descriptor 4 2).toNat) : Int) =
    ((descriptor.extractLsb' 2 3).toNat : Int)
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb]

theorem selectedAttribute_eq (config : AttributeConfig) (params : S1TTWParams)
    (state : State) (current : AttributesAt config params state) (descriptor : BitVec 64) :
    AArch64_MAIRAttr (S1MAIRKernel.index descriptor) params.mair2 params.mair state =
      .ok (selectedAttribute config descriptor) state := by
  rw [descriptorIndex_source, current.mair, current.mair2]
  exact mairAttr_eq (descriptorIndex descriptor) config.mair config.mair2 state

#print axioms mairAttr_eq
#print axioms reservedAttribute_eq
#print axioms descriptorIndex_source
#print axioms selectedAttribute_eq

end ArmCertWalk
