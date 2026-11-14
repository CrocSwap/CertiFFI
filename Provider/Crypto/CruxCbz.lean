import Crypto.CruxBrObl
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
open ArmBridge.Draft ArmBridge.CruxGenBr Crypto.CruxBrObl Crypto.CbzDec
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Crypto.CruxCbzLNSym.
namespace Crypto.CruxCbz

attribute [local instance 10] Classical.propDecidable

/-- The CBZ condition on the GPR file, exactly as `cbz_link` states it. -/
def cbzC (sf : BitVec 1) (Rt : BitVec 5) (t : NativeState) : Prop :=
  IsZero (if ((Rt.toNat : Nat) : Int) = 31 then (Zeros : BitVec (Sail.Int.toNatChecked (if sf = 1#1 then 64 else 32)))
      else BitVec.castWidth (Sail.BitVec.extractLsb t.regs.gpr[(GPRSummary.key Rt.toNat).val]
        (Sail.Int.toNatChecked (↑(Sail.Int.toNatChecked (if sf = 1#1 then 64 else 32)) - 1)) 0)) = ((0#1 : BitVec 1) == 0#1)

theorem cbzC_congr (sf : BitVec 1) (Rt : BitVec 5) (t1 t2 : NativeState) (h : t1.regs.gpr = t2.regs.gpr) :
    cbzC sf Rt t1 ↔ cbzC sf Rt t2 := by
  unfold cbzC; rw [h]

noncomputable def spec (sf : BitVec 1) (imm19 : BitVec 19) (Rt : BitVec 5) : BrSpec :=
  { fG := fun t => t
    fPC := fun t => if cbzC sf Rt t then t.regs._PC + sign_extend (imm19 ++ 0#2) 64 else t.regs._PC
    fBT := fun t => if cbzC sf Rt t then true else t.regs.__BranchTaken }

end Crypto.CruxCbz

