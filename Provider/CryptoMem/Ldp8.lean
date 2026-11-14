import MemM1.MemDataV5
import MemM1.MemPair8V5
import MemM1.AccGPR
import MemM1.MemReadDBE
import CryptoMem.MemCore
import CryptoMem.Tac
import CryptoMem.Tac2
import CryptoMem.PairCore
import CryptoMem.PairNative
import Bridge.StepM
import Bridge.Proj
import BridgeV2.AgreesV3
import CryptoMem.LdstPairDecode
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.BoundaryV2 CryptoMem.LdstPair
open ArmCert.Premises.TranslationAgreesV1
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoMem.Ldp8LNSym.
namespace CryptoMem.Ldp8

theorem add_split8 (x : BitVec 64) (i : Nat) (h1 : 8 ≤ i) (h2 : i < 16) :
    x + BitVec.ofNat 64 i = Sail.BitVec.addInt x ((8 : Nat) : Int) + BitVec.ofNat 64 (i - 8) := by
  unfold Sail.BitVec.addInt
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt, BitVec.toNat_add]
  omega

end CryptoMem.Ldp8

