import Spike91.ActLib
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace Spike91.HeapActLib
open ArmBridge.Draft

/-! Generic arithmetic vocabulary for generated heap action classes. -/
def xz (s : NativeState) (r : BitVec 5) : BitVec 64 :=
  if (r.toNat : Int) = 31 then 0#64 else
    Sail.BitVec.castWidth (Sail.BitVec.extractLsb s.regs.gpr[(GPRSummary.key r.toNat).val]
      (Sail.Int.toNatChecked 63) 0)

def aN (x y : BitVec 64) (c : BitVec 1) : BitVec 1 :=
  BitVec.access (ArmBridge.Awc.sres x y c) 63
def aZ (x y : BitVec 64) (c : BitVec 1) : BitVec 1 :=
  bif IsZero (ArmBridge.Awc.sres x y c) then 1#1 else 0#1
def aC (x y : BitVec 64) (c : BitVec 1) : BitVec 1 :=
  bif ((ArmBridge.Awc.sres x y c).toNat : Int) == ↑x.toNat + ↑y.toNat + ↑c.toNat then 0#1 else 1#1
def aV (x y : BitVec 64) (c : BitVec 1) : BitVec 1 :=
  bif (ArmBridge.Awc.sres x y c).toInt == x.toInt + y.toInt + ↑c.toNat then 0#1 else 1#1

theorem sres64 (x y : BitVec 64) (c : BitVec 1) :
    ArmBridge.Awc.sres x y c =
      (Sail.BitVec.castWidth (integer_subrange (↑x.toNat + ↑y.toNat + ↑c.toNat) 63 0) : BitVec 64) := rfl

theorem read64_eq (x : BitVec 64) :
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked 63) 0) : BitVec 64) = x := by
  exact Spike91.ActLib.cw64 x

end Spike91.HeapActLib
