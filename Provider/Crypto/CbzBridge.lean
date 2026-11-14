import BR8.CBZ
import Crypto.CbzDecode
import Crypto.BranchPins
import Crypto.CbzCore
import Bridge.StepM
import Bridge.Proj
import BridgeV2.BoundaryV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.BoundaryV2 Crypto.CbzDec
open ArmCert.Premises.TranslationAgreesV1
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Crypto.CbzBridgeLNSym.
namespace Crypto.CbzBridge

/-- Driver's BR_CBZ root inventory pins bit 24 (op) to 0: CBZ only (the heap words are CBZ). -/
theorem inv_word (sf : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) :
    (cbzWord sf 0#1 imm19 Rt &&& 2130706432#32) = 872415232#32 := by
  unfold cbzWord
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_append]
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem arg_Rt (sf op : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) :
    BitVec.extractLsb' 0 5 (cbzWord sf op imm19 Rt) = Rt := by unfold cbzWord; bv_field

theorem arg_imm19 (sf op : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) :
    BitVec.extractLsb' 5 19 (cbzWord sf op imm19 Rt) = imm19 := by unfold cbzWord; bv_field

theorem arg_op (sf op : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) :
    BitVec.extractLsb' 24 1 (cbzWord sf op imm19 Rt) = op := by unfold cbzWord; bv_field

theorem arg_sf (sf op : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) :
    BitVec.extractLsb' 31 1 (cbzWord sf op imm19 Rt) = sf := by unfold cbzWord; bv_field

end Crypto.CbzBridge

