import Crypto.CruxCbz
import Crypto.CruxBcond
import Crypto.CruxRet
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeEntryBodyBranch.Decide
open ArmBridge.Draft Crypto.BcondCore
set_option autoImplicit false

/- Spec decision lemmas for Core's branch path step: the canonical
Crypto.CruxCbz/CruxBcond/CruxRet.spec successor PC and BranchTaken as functions of the
decision predicates cbzC / bcondC used by BranchAgreement. `fPC_eq` are stated with any
Decidable instance; `fBT_eq` hold under the pre-state __BranchTaken = false
(Core's EntryPins hbtt0), in decide form. Ret has no low-bit clearing in the spec. -/

theorem cbz_fPC_eq (imm19 : BitVec 19) (Rt : BitVec 5) (s : NativeState)
    [Decidable (Crypto.CruxCbz.cbzC 1#1 Rt s)] :
    (Crypto.CruxCbz.spec 1#1 imm19 Rt).fPC s =
      if Crypto.CruxCbz.cbzC 1#1 Rt s then s.regs._PC + sign_extend (imm19 ++ 0#2) 64 else s.regs._PC := by
  simp only [Crypto.CruxCbz.spec]
  by_cases c : Crypto.CruxCbz.cbzC 1#1 Rt s <;> simp [c]

theorem cbz_fBT_eq (imm19 : BitVec 19) (Rt : BitVec 5) (s : NativeState)
    [Decidable (Crypto.CruxCbz.cbzC 1#1 Rt s)] (hbt : s.regs.__BranchTaken = false) :
    (Crypto.CruxCbz.spec 1#1 imm19 Rt).fBT s = decide (Crypto.CruxCbz.cbzC 1#1 Rt s) := by
  simp only [Crypto.CruxCbz.spec]
  by_cases c : Crypto.CruxCbz.cbzC 1#1 Rt s <;> simp [c, hbt]

theorem bcond_fPC_eq (cond : BitVec 4) (imm19 : BitVec 19) (s : NativeState) [Decidable (bcondC cond s.regs)] :
    (Crypto.CruxBcond.spec cond imm19).fPC s =
      if bcondC cond s.regs then s.regs._PC + sign_extend (imm19 ++ 0#2) 64 else s.regs._PC := by
  simp only [Crypto.CruxBcond.spec]
  by_cases c : bcondC cond s.regs <;> simp [c]

theorem bcond_fBT_eq (cond : BitVec 4) (imm19 : BitVec 19) (s : NativeState) [Decidable (bcondC cond s.regs)]
    (hbt : s.regs.__BranchTaken = false) :
    (Crypto.CruxBcond.spec cond imm19).fBT s = decide (bcondC cond s.regs) := by
  simp only [Crypto.CruxBcond.spec]
  by_cases c : bcondC cond s.regs <;> simp [c, hbt]

theorem ret_fPC_eq (Rn : BitVec 5) (s : NativeState) :
    (Crypto.CruxRet.spec Rn).fPC s = s.regs.gpr[(GPRSummary.key Rn.toNat).val] := rfl

theorem ret_fBT_eq (Rn : BitVec 5) (s : NativeState) : (Crypto.CruxRet.spec Rn).fBT s = true := rfl

#print axioms cbz_fPC_eq
#print axioms cbz_fBT_eq
#print axioms bcond_fPC_eq
#print axioms bcond_fBT_eq
#print axioms ret_fPC_eq
#print axioms ret_fBT_eq
end NativeEntryBodyBranch.Decide
