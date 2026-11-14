import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 200000
namespace S1Contiguous
abbrev State := SequentialState Regs oracleChoiceSource
def bit (d : BitVec 64) : BitVec 1 :=
  BitVec.setWidth 1 (BitVec.join1 [BitVec.access d 52])
theorem total (d : BitVec 64) (level : Int) (s : State) (hNonZero : level ≠ 0) :
    AArch64_ContiguousBit .TGx_4KB 0#1 level d s = .ok (bit d) s := by
  have h64 : ((.TGx_4KB : TGx) == .TGx_64KB) = false := by decide
  have h16 : ((.TGx_4KB : TGx) == .TGx_16KB) = false := by decide
  have h4 : ((.TGx_4KB : TGx) == .TGx_4KB) = true := by decide
  simp [AArch64_ContiguousBit, h64, h16, h4, hNonZero, bit,
    Bind.bind, Pure.pure, EStateM.pure]
#print axioms total
end S1Contiguous
