import MemM1.MemDataV5
import MemM1.AccGPR
import CryptoMem.MemCore
import CryptoMem.Tac
import CryptoMem.Tac2
import Bridge.StepM
import Bridge.Proj
import BridgeV2.AgreesV3
import CryptoMem.LdstPostDecode
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.BoundaryV2 CryptoMem.LdstPost
open ArmCert.Premises.TranslationAgreesV1
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoMem.StrbLNSym.
namespace CryptoMem.Strb

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

end CryptoMem.Strb

