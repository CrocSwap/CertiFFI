import NativeEntryBodyDispatch.Cbz

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions

namespace LoopNative.Cbz64.Dispatch
set_option autoImplicit false
set_option maxHeartbeats 100000

abbrev selected (Rt : BitVec 5) (imm19 : BitVec 19) : BitVec 32 :=
  NativeEntryBodyDispatch.Cbz.selected Rt imm19

theorem dispatch_at (real : Type) [Sail.SailReal real] (pc : Int)
    (Rt : BitVec 5) (imm19 : BitVec 19) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 118) :
    (__DecodeA64 (real := real) pc (selected Rt imm19) : SailM Unit) s =
      (do writeReg Register.SEE 118; decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 0#1 1#1 : SailM Unit) s :=
  NativeEntryBodyDispatch.Cbz.dispatch_at real pc Rt imm19 s see

#print axioms dispatch_at
end LoopNative.Cbz64.Dispatch
