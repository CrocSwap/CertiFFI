import CryptoBridge.AddImmGen
import CryptoBridge.SubsImmGen
import CryptoBridge.OrrLogShiftGen
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace Spike91.ActLib
open ArmBridge.Draft

/-! Class-level lemmas for the generated direct-ArmCert ALU action lemmas. -/

theorem sres0 (x y : BitVec 64) : ArmBridge.Awc.sres x y 0#1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  rw [ArmBridge.Awc.sres_toNat (by decide), BitVec.toNat_add]
  simp

theorem cw64 (x : BitVec 64) :
    (BitVec.castWidth (Sail.BitVec.extractLsb x (Int.toNatChecked (↑(64 : Nat) - 1)) 0) : BitVec 64) = x := by
  have hw : Int.toNatChecked (↑(64 : Nat) - 1) - 0 + 1 = 64 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [ArmBridge.Awc.castWidth_of_eq hw]
  simp [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb, hi]

theorem zx64 (x : BitVec 64) : Sail.BitVec.zeroExtend x 64 = x := by
  simp [Sail.BitVec.zeroExtend]

/-- The 32-bit operand X[Rn] as the native leaf reads it. -/
def X32 (t : NativeState) (Rn : BitVec 5) : BitVec 32 :=
  BitVec.castWidth (Sail.BitVec.extractLsb t.regs.gpr[(GPRSummary.key Rn.toNat).val] (Int.toNatChecked (↑(32 : Nat) - 1)) 0)

/-- Native NZCV of x - y (as AddWithCarry(x, ~y, 1)), verbatim from the ArmFull leaf. -/
def nN (x y : BitVec 32) : BitVec 1 :=
  BitVec.setWidth 1 (BitVec.join1 [BitVec.access (ArmBridge.Awc.sres x (~~~y) 1#1) (Int.toNatChecked (↑(BitVec.length (~~~y)) - 1))])
def nZ (x y : BitVec 32) : BitVec 1 := bif IsZero (ArmBridge.Awc.sres x (~~~y) 1#1) then 1#1 else 0#1
def nC (x y : BitVec 32) : BitVec 1 :=
  bif ((ArmBridge.Awc.sres x (~~~y) 1#1).toNat : Int) == ↑x.toNat + ↑(~~~y).toNat + ↑(1#1 : BitVec 1).toNat then 0#1 else 1#1
def nV (x y : BitVec 32) : BitVec 1 :=
  bif (ArmBridge.Awc.sres x (~~~y) 1#1).toInt == x.toInt + (~~~y).toInt + ↑(1#1 : BitVec 1).toNat then 0#1 else 1#1

/-- N of AddWithCarry(x, y, c), generic in y (folding target, so a match inside y stays a plain argument). -/
def nNg (x y : BitVec 32) (c : BitVec 1) : BitVec 1 :=
  BitVec.setWidth 1 (BitVec.join1 [BitVec.access (ArmBridge.Awc.sres x y c) (Int.toNatChecked (↑(BitVec.length y) - 1))])
theorem nNg_def (x y : BitVec 32) (c : BitVec 1) :
    nNg x y c = BitVec.setWidth 1 (BitVec.join1 [BitVec.access (ArmBridge.Awc.sres x y c) (Int.toNatChecked (↑(BitVec.length y) - 1))]) := rfl

#print axioms sres0
#print axioms cw64
end Spike91.ActLib
