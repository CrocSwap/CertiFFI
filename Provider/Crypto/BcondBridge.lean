import BR8.BCond
import Crypto.BcondDecode
import Crypto.BranchPins
import Crypto.BcondCore
import Bridge.StepM
import Bridge.Proj
import BridgeV2.BoundaryV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.BoundaryV2 Crypto.BcondDec
open ArmCert.Premises.TranslationAgreesV1
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Crypto.BcondBridgeLNSym.
namespace Crypto.BcondBridge

theorem inv_word (imm19 : BitVec 19) (cond : BitVec 4) :
    (bcondWord imm19 cond &&& 4278190096#32) = 1409286144#32 := by
  unfold bcondWord
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_append]
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem arg_cond (imm19 : BitVec 19) (cond : BitVec 4) : BitVec.extractLsb' 0 4 (bcondWord imm19 cond) = cond := by
  unfold bcondWord; bv_field

theorem arg_imm19 (imm19 : BitVec 19) (cond : BitVec 4) : BitVec.extractLsb' 5 19 (bcondWord imm19 cond) = imm19 := by
  unfold bcondWord; bv_field

end Crypto.BcondBridge

