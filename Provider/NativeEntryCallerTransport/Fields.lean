import NativeEntryCallerParts.BlCall
import NativeEntryCallerParts.BlrCall
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeEntryCallerTransport
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem finish_FeatureImpl (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.FeatureImpl = s.regs.FeatureImpl := rfl

theorem spe_FeatureImpl (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.FeatureImpl = s.regs.FeatureImpl := by
  rw [spe_regs]
  rfl

theorem branch_FeatureImpl (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.FeatureImpl = s.regs.FeatureImpl := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_FeatureImpl, spe_FeatureImpl, address_regs]
    rfl
  · rw [finish_FeatureImpl, address_regs]
    rfl

theorem finish_bank_BitVec_64 (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.bank_BitVec_64 = s.regs.bank_BitVec_64 := rfl

theorem spe_bank_BitVec_64 (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.bank_BitVec_64 = s.regs.bank_BitVec_64 := by
  rw [spe_regs]
  rfl

theorem branch_bank_BitVec_64 (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.bank_BitVec_64 = s.regs.bank_BitVec_64 := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_bank_BitVec_64, spe_bank_BitVec_64, address_regs]
    rfl
  · rw [finish_bank_BitVec_64, address_regs]
    rfl

theorem finish_bank_BitVec_32 (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.bank_BitVec_32 = s.regs.bank_BitVec_32 := rfl

theorem spe_bank_BitVec_32 (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.bank_BitVec_32 = s.regs.bank_BitVec_32 := by
  rw [spe_regs]
  rfl

theorem branch_bank_BitVec_32 (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.bank_BitVec_32 = s.regs.bank_BitVec_32 := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_bank_BitVec_32, spe_bank_BitVec_32, address_regs]
    rfl
  · rw [finish_bank_BitVec_32, address_regs]
    rfl

theorem finish_bank_Int (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.bank_Int = s.regs.bank_Int := rfl

theorem spe_bank_Int (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.bank_Int = s.regs.bank_Int := by
  rw [spe_regs]
  rfl

theorem branch_bank_Int (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.bank_Int = s.regs.bank_Int := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_bank_Int, spe_bank_Int, address_regs]
    rfl
  · rw [finish_bank_Int, address_regs]
    rfl

theorem finish_PhysicalCount (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.PhysicalCount = s.regs.PhysicalCount := rfl

theorem spe_PhysicalCount (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.PhysicalCount = s.regs.PhysicalCount := by
  rw [spe_regs]
  rfl

theorem branch_PhysicalCount (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.PhysicalCount = s.regs.PhysicalCount := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_PhysicalCount, spe_PhysicalCount, address_regs]
    rfl
  · rw [finish_PhysicalCount, address_regs]
    rfl

theorem finish___emulator_termination_opcode (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.__emulator_termination_opcode = s.regs.__emulator_termination_opcode := rfl

theorem spe___emulator_termination_opcode (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.__emulator_termination_opcode = s.regs.__emulator_termination_opcode := by
  rw [spe_regs]
  rfl

theorem branch___emulator_termination_opcode (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.__emulator_termination_opcode = s.regs.__emulator_termination_opcode := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish___emulator_termination_opcode, spe___emulator_termination_opcode, address_regs]
    rfl
  · rw [finish___emulator_termination_opcode, address_regs]
    rfl

theorem finish_ShouldAdvanceIT (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.ShouldAdvanceIT = s.regs.ShouldAdvanceIT := rfl

theorem spe_ShouldAdvanceIT (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.ShouldAdvanceIT = s.regs.ShouldAdvanceIT := by
  rw [spe_regs]
  rfl

theorem branch_ShouldAdvanceIT (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.ShouldAdvanceIT = s.regs.ShouldAdvanceIT := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_ShouldAdvanceIT, spe_ShouldAdvanceIT, address_regs]
    rfl
  · rw [finish_ShouldAdvanceIT, address_regs]
    rfl

theorem finish_ShouldAdvanceSS (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.ShouldAdvanceSS = s.regs.ShouldAdvanceSS := rfl

theorem spe_ShouldAdvanceSS (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.ShouldAdvanceSS = s.regs.ShouldAdvanceSS := by
  rw [spe_regs]
  rfl

theorem branch_ShouldAdvanceSS (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.ShouldAdvanceSS = s.regs.ShouldAdvanceSS := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_ShouldAdvanceSS, spe_ShouldAdvanceSS, address_regs]
    rfl
  · rw [finish_ShouldAdvanceSS, address_regs]
    rfl

theorem finish___ThisInstrEnc (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.__ThisInstrEnc = s.regs.__ThisInstrEnc := rfl

theorem spe___ThisInstrEnc (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.__ThisInstrEnc = s.regs.__ThisInstrEnc := by
  rw [spe_regs]
  rfl

theorem branch___ThisInstrEnc (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.__ThisInstrEnc = s.regs.__ThisInstrEnc := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish___ThisInstrEnc, spe___ThisInstrEnc, address_regs]
    rfl
  · rw [finish___ThisInstrEnc, address_regs]
    rfl

theorem finish_bank_BitVec_128 (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.bank_BitVec_128 = s.regs.bank_BitVec_128 := rfl

theorem spe_bank_BitVec_128 (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.bank_BitVec_128 = s.regs.bank_BitVec_128 := by
  rw [spe_regs]
  rfl

theorem branch_bank_BitVec_128 (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.bank_BitVec_128 = s.regs.bank_BitVec_128 := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_bank_BitVec_128, spe_bank_BitVec_128, address_regs]
    rfl
  · rw [finish_bank_BitVec_128, address_regs]
    rfl

theorem finish_bank_Option_InterruptID (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.bank_Option_InterruptID = s.regs.bank_Option_InterruptID := rfl

theorem spe_bank_Option_InterruptID (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.bank_Option_InterruptID = s.regs.bank_Option_InterruptID := by
  rw [spe_regs]
  rfl

theorem branch_bank_Option_InterruptID (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.bank_Option_InterruptID = s.regs.bank_Option_InterruptID := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_bank_Option_InterruptID, spe_bank_Option_InterruptID, address_regs]
    rfl
  · rw [finish_bank_Option_InterruptID, address_regs]
    rfl

theorem finish_bbool (target : BitVec 64) (s : NativeState) :
    (finishState target s).regs.bank_Bool = s.regs.bank_Bool := rfl

theorem spe_sample (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (speState target branch false s).regs.bank_Bool .SPESampleInFlight =
      s.regs.bank_Bool .SPESampleInFlight := by
  rw [spe_regs]
  simp (disch := decide) only [SPESamplePreviousBranchAddressValid, Regs.ref_Bool, RegMap.set_ne]

theorem branch_sample (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.bank_Bool .SPESampleInFlight =
      s.regs.bank_Bool .SPESampleInFlight := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_bbool, spe_sample, address_regs]
    rfl
  · rw [finish_bbool, address_regs]
    rfl

/- Exact real SPE effect; this key is NOT masked by the historical bkHeap. -/
theorem branch_previous_valid (target : BitVec 64) (branch : BranchType) (s : NativeState) :
    (branchState target branch s).regs.bank_Bool .SPESamplePreviousBranchAddressValid =
      if speFeature (addressState target (hintState branch s)) then false
      else s.regs.bank_Bool .SPESamplePreviousBranchAddressValid := by
  unfold branchState profileState
  dsimp only []
  split
  · rw [finish_bbool, spe_regs]
    rfl
  · rw [finish_bbool, address_regs]
    rfl

theorem bl_FeatureImpl (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.FeatureImpl = s.regs.FeatureImpl := by
  unfold blActionState
  rw [branch_FeatureImpl]
  rfl

theorem bl_bank_BitVec_64 (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.bank_BitVec_64 = s.regs.bank_BitVec_64 := by
  unfold blActionState
  rw [branch_bank_BitVec_64]
  rfl

theorem bl_bank_BitVec_32 (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.bank_BitVec_32 = s.regs.bank_BitVec_32 := by
  unfold blActionState
  rw [branch_bank_BitVec_32]
  rfl

theorem bl_bank_Int (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.bank_Int = s.regs.bank_Int := by
  unfold blActionState
  rw [branch_bank_Int]
  rfl

theorem bl_PhysicalCount (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.PhysicalCount = s.regs.PhysicalCount := by
  unfold blActionState
  rw [branch_PhysicalCount]
  rfl

theorem bl___emulator_termination_opcode (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.__emulator_termination_opcode = s.regs.__emulator_termination_opcode := by
  unfold blActionState
  rw [branch___emulator_termination_opcode]
  rfl

theorem bl_ShouldAdvanceIT (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.ShouldAdvanceIT = s.regs.ShouldAdvanceIT := by
  unfold blActionState
  rw [branch_ShouldAdvanceIT]
  rfl

theorem bl_ShouldAdvanceSS (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.ShouldAdvanceSS = s.regs.ShouldAdvanceSS := by
  unfold blActionState
  rw [branch_ShouldAdvanceSS]
  rfl

theorem bl___ThisInstrEnc (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.__ThisInstrEnc = s.regs.__ThisInstrEnc := by
  unfold blActionState
  rw [branch___ThisInstrEnc]
  rfl

theorem bl_bank_BitVec_128 (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.bank_BitVec_128 = s.regs.bank_BitVec_128 := by
  unfold blActionState
  rw [branch_bank_BitVec_128]
  rfl

theorem bl_bank_Option_InterruptID (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.bank_Option_InterruptID = s.regs.bank_Option_InterruptID := by
  unfold blActionState
  rw [branch_bank_Option_InterruptID]
  rfl

theorem bl_sample (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.bank_Bool .SPESampleInFlight =
      s.regs.bank_Bool .SPESampleInFlight := by
  unfold blActionState
  rw [branch_sample]
  rfl

theorem blr_FeatureImpl (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.FeatureImpl = s.regs.FeatureImpl := by
  unfold blrActionState
  rw [branch_FeatureImpl]
  rfl

theorem blr_bank_BitVec_64 (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.bank_BitVec_64 = s.regs.bank_BitVec_64 := by
  unfold blrActionState
  rw [branch_bank_BitVec_64]
  rfl

theorem blr_bank_BitVec_32 (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.bank_BitVec_32 = s.regs.bank_BitVec_32 := by
  unfold blrActionState
  rw [branch_bank_BitVec_32]
  rfl

theorem blr_bank_Int (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.bank_Int = s.regs.bank_Int := by
  unfold blrActionState
  rw [branch_bank_Int]
  rfl

theorem blr_PhysicalCount (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.PhysicalCount = s.regs.PhysicalCount := by
  unfold blrActionState
  rw [branch_PhysicalCount]
  rfl

theorem blr___emulator_termination_opcode (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.__emulator_termination_opcode = s.regs.__emulator_termination_opcode := by
  unfold blrActionState
  rw [branch___emulator_termination_opcode]
  rfl

theorem blr_ShouldAdvanceIT (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.ShouldAdvanceIT = s.regs.ShouldAdvanceIT := by
  unfold blrActionState
  rw [branch_ShouldAdvanceIT]
  rfl

theorem blr_ShouldAdvanceSS (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.ShouldAdvanceSS = s.regs.ShouldAdvanceSS := by
  unfold blrActionState
  rw [branch_ShouldAdvanceSS]
  rfl

theorem blr___ThisInstrEnc (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.__ThisInstrEnc = s.regs.__ThisInstrEnc := by
  unfold blrActionState
  rw [branch___ThisInstrEnc]
  rfl

theorem blr_bank_BitVec_128 (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.bank_BitVec_128 = s.regs.bank_BitVec_128 := by
  unfold blrActionState
  rw [branch_bank_BitVec_128]
  rfl

theorem blr_bank_Option_InterruptID (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.bank_Option_InterruptID = s.regs.bank_Option_InterruptID := by
  unfold blrActionState
  rw [branch_bank_Option_InterruptID]
  rfl

theorem blr_sample (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.bank_Bool .SPESampleInFlight =
      s.regs.bank_Bool .SPESampleInFlight := by
  unfold blrActionState
  rw [branch_sample]
  rfl

#print axioms finish_FeatureImpl
#print axioms spe_FeatureImpl
#print axioms branch_FeatureImpl
#print axioms finish_bank_BitVec_64
#print axioms spe_bank_BitVec_64
#print axioms branch_bank_BitVec_64
#print axioms finish_bank_BitVec_32
#print axioms spe_bank_BitVec_32
#print axioms branch_bank_BitVec_32
#print axioms finish_bank_Int
#print axioms spe_bank_Int
#print axioms branch_bank_Int
#print axioms finish_PhysicalCount
#print axioms spe_PhysicalCount
#print axioms branch_PhysicalCount
#print axioms finish___emulator_termination_opcode
#print axioms spe___emulator_termination_opcode
#print axioms branch___emulator_termination_opcode
#print axioms finish_ShouldAdvanceIT
#print axioms spe_ShouldAdvanceIT
#print axioms branch_ShouldAdvanceIT
#print axioms finish_ShouldAdvanceSS
#print axioms spe_ShouldAdvanceSS
#print axioms branch_ShouldAdvanceSS
#print axioms finish___ThisInstrEnc
#print axioms spe___ThisInstrEnc
#print axioms branch___ThisInstrEnc
#print axioms finish_bank_BitVec_128
#print axioms spe_bank_BitVec_128
#print axioms branch_bank_BitVec_128
#print axioms finish_bank_Option_InterruptID
#print axioms spe_bank_Option_InterruptID
#print axioms branch_bank_Option_InterruptID
#print axioms finish_bbool
#print axioms spe_sample
#print axioms branch_sample
#print axioms branch_previous_valid
#print axioms bl_FeatureImpl
#print axioms bl_bank_BitVec_64
#print axioms bl_bank_BitVec_32
#print axioms bl_bank_Int
#print axioms bl_PhysicalCount
#print axioms bl___emulator_termination_opcode
#print axioms bl_ShouldAdvanceIT
#print axioms bl_ShouldAdvanceSS
#print axioms bl___ThisInstrEnc
#print axioms bl_bank_BitVec_128
#print axioms bl_bank_Option_InterruptID
#print axioms bl_sample
#print axioms blr_FeatureImpl
#print axioms blr_bank_BitVec_64
#print axioms blr_bank_BitVec_32
#print axioms blr_bank_Int
#print axioms blr_PhysicalCount
#print axioms blr___emulator_termination_opcode
#print axioms blr_ShouldAdvanceIT
#print axioms blr_ShouldAdvanceSS
#print axioms blr___ThisInstrEnc
#print axioms blr_bank_BitVec_128
#print axioms blr_bank_Option_InterruptID
#print axioms blr_sample
end NativeEntryCallerTransport
