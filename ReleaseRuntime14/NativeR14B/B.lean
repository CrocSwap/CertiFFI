import NativeR14B.BPrefix
import NativeEntryCallerParts.BlCall
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeR14B
open ArmBridge.Draft ArmBridge.CruxCore NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-! runtime14 B (unconditional immediate, imm26): exact action and frame. The actual decoder is
exactly BranchTo (PC + sign_extend (imm26 ++ 0#2)) DIR false on the UNCHANGED state (BPrefix,
drive_spec with BranchTo opaque); BranchTo is then the sealed caller-actions branchState. -/

/-- Exact result of the actual B decoder. -/
noncomputable def bActionState (imm26 : BitVec 26) (s : NativeState) : NativeState :=
  branchState (blTarget imm26 s) BranchType.BranchType_DIR s

theorem b_boundary (imm26 : BitVec 26) (s : NativeState) (hp : CallerControls s) :
    (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 0#1 : SailM Unit) s =
      (BranchTo (blTarget imm26 s) BranchType.BranchType_DIR false : SailM Unit) s := by
  simpa only [BPrefix_native, blTarget] using BPrefix_complete imm26 s

theorem b_run (imm26 : BitVec 26) (s : NativeState) (hp : CallerControls s)
    (low : (blTarget imm26 s).toNat < 2^55) :
    (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 0#1 : SailM Unit) s =
      .ok () (bActionState imm26 s) := by
  rw [b_boundary imm26 s hp]
  exact branch_run _ _ _ hp (low_bit55 _ low)

theorem b_action_controls (imm26 : BitVec 26) (s : NativeState) (hp : CallerControls s) :
    CallerControls (bActionState imm26 s) := branch_controls _ _ _ hp
theorem b_action_pc (imm26 : BitVec 26) (s : NativeState) (hp : CallerControls s)
    (low : (blTarget imm26 s).toNat < 2^55) : (bActionState imm26 s).regs._PC = blTarget imm26 s :=
  (branch_pc _ _ _).trans (address_low _ _ (hint_controls _ _ hp) low)
theorem b_action_taken (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).regs.__BranchTaken = true := branch_taken _ _ _
theorem b_action_type (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).regs.Branchtypetaken = BranchType.BranchType_DIR := branch_type _ _ _
theorem b_action_btn (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).regs.BTypeNext = s.regs.BTypeNext := branch_BTypeNext _ _ _
theorem b_action_gpr (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).regs.gpr = s.regs.gpr := branch_gpr _ _ _
theorem b_action_SP_EL0 (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).regs.SP_EL0 = s.regs.SP_EL0 := branch_SP_EL0 _ _ _
theorem b_action_PSTATE (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).regs.PSTATE = s.regs.PSTATE := branch_PSTATE _ _ _
theorem b_action_FPCR (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).regs.FPCR = s.regs.FPCR := branch_FPCR _ _ _
theorem b_action_FPSR (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).regs.FPSR = s.regs.FPSR := branch_FPSR _ _ _
theorem b_action__Z (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).regs._Z = s.regs._Z := branch__Z _ _ _
theorem b_action_mem (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).mem = s.mem := branch_mem _ _ _
theorem b_action_events (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).events = s.events := branch_events _ _ _
theorem b_action_tags (imm26 : BitVec 26) (s : NativeState) :
    (bActionState imm26 s).tags = s.tags := branch_tags _ _ _

/-- Packaged frame for: success with gpr / SP_EL0 / PSTATE (so NZCV) unchanged. -/
theorem B_frame (imm26 : BitVec 26) (s : NativeState) (hp : CallerControls s)
    (low : (blTarget imm26 s).toNat < 2^55) :
    ∃ u, (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 0#1 : SailM Unit) s = .ok () u ∧
      u.regs.gpr = s.regs.gpr ∧ u.regs.SP_EL0 = s.regs.SP_EL0 ∧ u.regs.PSTATE = s.regs.PSTATE ∧
      u.regs._PC = blTarget imm26 s ∧ u.regs.__BranchTaken = true ∧ u.regs.BTypeNext = s.regs.BTypeNext ∧
      u.mem = s.mem ∧ u.events = s.events :=
  ⟨_, b_run imm26 s hp low, b_action_gpr _ _, b_action_SP_EL0 _ _, b_action_PSTATE _ _,
    b_action_pc _ _ hp low, b_action_taken _ _, b_action_btn _ _, b_action_mem _ _, b_action_events _ _⟩

#print axioms b_run
#print axioms B_frame
end NativeR14B
