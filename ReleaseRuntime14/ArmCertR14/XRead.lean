-- Memory (runtime14): W/B register reads for the store classes (restated from CruxMem.UoffCommon.xread32 /
-- CryptoMem.Strb.xread8 so the classes don't import those old-bridge modules).
import CryptoMem.MemCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
namespace ArmCertR14.XRead
open ArmBridge.Draft

theorem xread32 (s : NativeState) (R : BitVec 5) (hR : R.toNat < 31) :
    X_read ((R.toNat : Nat) : Int) 32 s =
      .ok (BitVec.castWidth (Sail.BitVec.extractLsb (s.regs.gpr[(GPRSummary.key R.toNat).val]) 31 0)) s := by
  unfold X_read get_R
  have htn : Sail.Int.toNatChecked ((R.toNat : Nat) : Int) = R.toNat := rfl
  have h1 : ((R.toNat : Int) ≤ 31) := by omega
  have h2 : ¬ ((R.toNat : Int) = 31) := by omega
  simp [PreSail.assert, bind, EStateM.bind, pure, EStateM.pure, GPRSummary.read_complete, htn, h1, h2,
    CryptoMem.MemCore.cw_extract63]
  rfl

theorem xread8 (s : NativeState) (R : BitVec 5) (hR : R.toNat < 31) :
    X_read ((R.toNat : Nat) : Int) 8 s =
      .ok (BitVec.castWidth (Sail.BitVec.extractLsb (s.regs.gpr[(GPRSummary.key R.toNat).val]) 7 0)) s := by
  unfold X_read get_R
  have htn : Sail.Int.toNatChecked ((R.toNat : Nat) : Int) = R.toNat := rfl
  have h1 : ((R.toNat : Int) ≤ 31) := by omega
  have h2 : ¬ ((R.toNat : Int) = 31) := by omega
  simp [PreSail.assert, bind, EStateM.bind, pure, EStateM.pure, GPRSummary.read_complete, htn, h1, h2,
    CryptoMem.MemCore.cw_extract63]
  rfl

#print axioms xread32
#print axioms xread8
end ArmCertR14.XRead
