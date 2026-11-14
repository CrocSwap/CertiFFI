import Spike91.HeapActLib
import CryptoBridge.AddSubShiftCore
import CryptoBridge.LogImmCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace Spike91.NativeActLib
open ArmBridge.Draft Spike91.HeapActLib

def xs (t : NativeState) (r : BitVec 5) : BitVec 64 :=
  if r.toNat = 31 then t.regs.SP_EL0 else t.regs.gpr[(GPRSummary.key r.toNat).val]
def lsl (t : NativeState) (r : BitVec 5) (amount : BitVec 6) : BitVec 64 :=
  xz t r <<< amount.toNat
def mz (imm16 : BitVec 16) (hv : BitVec 2) : BitVec 64 :=
  Sail.BitVec.zeroExtend
    (Sail.BitVec.updateSubrange (0#64) (Sail.Int.toNatChecked ((hv +++ 0#4).toNat + 15))
      (hv +++ 0#4).toNat (Sail.BitVec.castWidth imm16)) 64
def nz (v : BitVec 64) : BitVec 1 := bif IsZero v then 1#1 else 0#1
theorem native_read64 (x : BitVec 64) :
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb x
      (Sail.Int.toNatChecked ((Sail.Int.toNatChecked (64 : Int) : Int) - 1)) 0) : BitVec 64) = x :=
  Spike91.ActLib.cw64 x
theorem nat_int31 (r : BitVec 5) : ((r.toNat : Int) = 31) ↔ r.toNat = 31 := by omega
theorem width64 : Sail.Int.toNatChecked (64 : Int) = 64 := rfl
theorem width63 : Sail.Int.toNatChecked (63 : Int) = 63 := rfl
theorem top64 : Sail.Int.toNatChecked ((64 : Nat) - (1 : Int)) = 63 := rfl
theorem read63 (x : BitVec 64) :
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked 63) 0) : BitVec 64) = x :=
  Spike91.ActLib.cw64 x
theorem read63_lit (x : BitVec 64) :
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb x 63 0) : BitVec 64) = x :=
  Spike91.ActLib.cw64 x
theorem raw_read63 (x : BitVec 64) : Sail.BitVec.extractLsb x 63 0 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb, hi]
theorem shl_nat (x : BitVec 64) (n : Nat) :
    @HShiftLeft.hShiftLeft (BitVec 64) Int (BitVec 64)
      (@Sail.instHShiftLeftBitVecInt_sail 64) x (n : Int) = x <<< n := rfl
theorem and7_top (x : BitVec 64) : Sail.BitVec.access (x &&& 7#64) 63 = 0#1 := by
  unfold Sail.BitVec.access
  simp [getElem!_def]
end Spike91.NativeActLib
