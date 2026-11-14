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
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to CryptoMem.Stp8LNSym.
namespace CryptoMem.Stp8

theorem sub_split8 (x : BitVec 64) (k : Nat) (hk : k < 8) :
    (Sail.BitVec.addInt x ((8 : Nat) : Int) + BitVec.ofNat 64 k - x).toNat = 8 + k := by
  unfold Sail.BitVec.addInt
  have := x.isLt
  simp [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofInt]
  omega

theorem sub_split0 (x : BitVec 64) (k : Nat) (hk : k < 16) : (x + BitVec.ofNat 64 k - x).toNat = k := by
  have := x.isLt
  simp [BitVec.toNat_add, BitVec.toNat_sub]
  omega

theorem b_split8 (x b : BitVec 64) (h1 : 8 ≤ (b - x).toNat) (h2 : (b - x).toNat < 16) :
    b = Sail.BitVec.addInt x ((8 : Nat) : Int) + BitVec.ofNat 64 ((b - x).toNat - 8) := by
  unfold Sail.BitVec.addInt
  apply BitVec.eq_of_toNat_eq
  have := x.isLt; have := b.isLt
  simp [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofInt] at h1 h2 ⊢
  omega

end CryptoMem.Stp8

