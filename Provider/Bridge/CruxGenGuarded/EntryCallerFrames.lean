import NativeEntryCallerTransport.Pins
import Bridge.CruxGenGuarded.EntryTail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
open NativeEntryCallerParts NativeEntryCallerTransport
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/- Actual caller actions preserve SysEq2's 17 fields. This does NOT claim
historical bkHeap NPE: the real SPE path can clear PrevValid. -/

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.bl_action_sys"
  (← IO.getStderr).flush

theorem bl_action_sys (imm26 : BitVec 26) (s : NativeState) :
    SysEq2 s.regs (blActionState imm26 s).regs := by
  constructor
  · exact bl_FeatureImpl imm26 s
  · exact congrArg ProcState.EL (bl_action_PSTATE imm26 s)
  · exact congrArg ProcState.nRW (bl_action_PSTATE imm26 s)
  · exact congrFun (bl_bank_BitVec_64 imm26 s) _
  · exact congrFun (bl_bank_BitVec_64 imm26 s) _
  · exact congrFun (bl_bank_BitVec_64 imm26 s) _
  · exact congrFun (bl_bank_BitVec_64 imm26 s) _
  · exact congrFun (bl_bank_BitVec_64 imm26 s) _
  · exact congrFun (bl_bank_BitVec_64 imm26 s) _
  · exact congrFun (bl_bank_BitVec_64 imm26 s) _
  · exact congrFun (bl_bank_BitVec_64 imm26 s) _
  · exact congrFun (bl_bank_BitVec_128 imm26 s) _
  · exact congrFun (bl_bank_BitVec_128 imm26 s) _
  · rw [bl_bank_BitVec_32]
  · unfold blActionState branchState profileState
    dsimp only []
    split <;>
      simp (disch := decide) only [finish_bbool, spe_regs, address_regs,
        SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] <;> rfl
  · exact bl_sample imm26 s
  · exact congrFun (bl_bank_Int imm26 s) _

theorem bl_action_branch (imm26 : BitVec 26) (s : NativeState) :
    BrSysEq s.regs (blActionState imm26 s).regs := by
  exact ⟨congrFun (bl_bank_Int imm26 s) _,
    congrFun (bl_bank_Int imm26 s) _, congrFun (bl_bank_Int imm26 s) _,
    congrFun (bl_bank_BitVec_64 imm26 s) _⟩

#print axioms bl_action_sys
#print axioms bl_action_branch

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.blr_action_sys"
  (← IO.getStderr).flush

theorem blr_action_sys (Rn : BitVec 5) (s : NativeState) :
    SysEq2 s.regs (blrActionState Rn s).regs := by
  constructor
  · exact blr_FeatureImpl Rn s
  · exact congrArg ProcState.EL (blr_action_PSTATE Rn s)
  · exact congrArg ProcState.nRW (blr_action_PSTATE Rn s)
  · exact congrFun (blr_bank_BitVec_64 Rn s) _
  · exact congrFun (blr_bank_BitVec_64 Rn s) _
  · exact congrFun (blr_bank_BitVec_64 Rn s) _
  · exact congrFun (blr_bank_BitVec_64 Rn s) _
  · exact congrFun (blr_bank_BitVec_64 Rn s) _
  · exact congrFun (blr_bank_BitVec_64 Rn s) _
  · exact congrFun (blr_bank_BitVec_64 Rn s) _
  · exact congrFun (blr_bank_BitVec_64 Rn s) _
  · exact congrFun (blr_bank_BitVec_128 Rn s) _
  · exact congrFun (blr_bank_BitVec_128 Rn s) _
  · rw [blr_bank_BitVec_32]
  · unfold blrActionState branchState profileState
    dsimp only []
    split <;>
      simp (disch := decide) only [finish_bbool, spe_regs, address_regs,
        SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne] <;> rfl
  · exact blr_sample Rn s
  · exact congrFun (blr_bank_Int Rn s) _

theorem blr_action_branch (Rn : BitVec 5) (s : NativeState) :
    BrSysEq s.regs (blrActionState Rn s).regs := by
  exact ⟨congrFun (blr_bank_Int Rn s) _,
    congrFun (blr_bank_Int Rn s) _, congrFun (blr_bank_Int Rn s) _,
    congrFun (blr_bank_BitVec_64 Rn s) _⟩

#print axioms blr_action_sys
#print axioms blr_action_branch

end ArmBridge.CruxGenGuarded
