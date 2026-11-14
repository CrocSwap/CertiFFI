import NativeEntryCallerParts.Compose
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeEntryCallerParts
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/- Exact result of the actual selected caller decoder. -/
noncomputable def blActionState (imm26 : BitVec 26) (s : NativeState) : NativeState :=
  branchState (blTarget imm26 s) BranchType.BranchType_DIRCALL (blBeforeCall imm26 s)

theorem bl_run (imm26 : BitVec 26) (s : NativeState) (hp : CallerControls s)
    (low : (blTarget imm26 s).toNat < 2^55) :
    (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1 : SailM Unit) s = .ok () (blActionState imm26 s) := by
  rw [bl_boundary imm26 s hp]
  exact branch_run _ _ _ (bl_controls imm26 s hp) (low_bit55 _ low)

theorem bl_action_controls (imm26 : BitVec 26) (s : NativeState) (hp : CallerControls s) :
    CallerControls (blActionState imm26 s) :=
  branch_controls _ _ _ (bl_controls imm26 s hp)

theorem bl_action_btn (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.BTypeNext = s.regs.BTypeNext := by
  exact (branch_BTypeNext _ _ _).trans (bl_btn imm26 s)

theorem bl_action_taken (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.__BranchTaken = true := branch_taken _ _ _

theorem bl_action_type (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.Branchtypetaken = BranchType.BranchType_DIRCALL := branch_type _ _ _

theorem bl_action_pc (imm26 : BitVec 26) (s : NativeState) (hp : CallerControls s)
    (low : (blTarget imm26 s).toNat < 2^55) :
    (blActionState imm26 s).regs._PC = blTarget imm26 s :=
  (branch_pc _ _ _).trans (address_low _ _ (hint_controls _ _ (bl_controls imm26 s hp)) low)

theorem bl_action_PSTATE (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.PSTATE = s.regs.PSTATE :=
  (branch_PSTATE _ _ _).trans (bl_PSTATE imm26 s)

theorem bl_action_FPCR (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.FPCR = s.regs.FPCR :=
  (branch_FPCR _ _ _).trans (bl_FPCR imm26 s)

theorem bl_action_FPSR (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.FPSR = s.regs.FPSR :=
  (branch_FPSR _ _ _).trans (bl_FPSR imm26 s)

theorem bl_action__Z (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs._Z = s.regs._Z :=
  (branch__Z _ _ _).trans (bl__Z imm26 s)

theorem bl_action_SP_EL0 (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).regs.SP_EL0 = s.regs.SP_EL0 :=
  (branch_SP_EL0 _ _ _).trans (bl_SP_EL0 imm26 s)

theorem bl_action_mem (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).mem = s.mem :=
  (branch_mem _ _ _).trans (bl_mem imm26 s)

theorem bl_action_events (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).events = s.events :=
  (branch_events _ _ _).trans (bl_events imm26 s)

theorem bl_action_tags (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).tags = s.tags :=
  (branch_tags _ _ _).trans (bl_tags imm26 s)

theorem bl_action_cycleCount (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).cycleCount = s.cycleCount :=
  (branch_cycleCount _ _ _).trans (bl_cycleCount imm26 s)

theorem bl_action_sailOutput (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).sailOutput = s.sailOutput :=
  (branch_sailOutput _ _ _).trans (bl_sailOutput imm26 s)

theorem bl_action_choiceState (imm26 : BitVec 26) (s : NativeState) :
    (blActionState imm26 s).choiceState = s.choiceState :=
  (branch_choiceState _ _ _).trans (bl_choiceState imm26 s)

#print axioms bl_run
#print axioms bl_action_controls
#print axioms bl_action_btn
#print axioms bl_action_taken
#print axioms bl_action_type
#print axioms bl_action_pc
#print axioms bl_action_PSTATE
#print axioms bl_action_FPCR
#print axioms bl_action_FPSR
#print axioms bl_action__Z
#print axioms bl_action_SP_EL0
#print axioms bl_action_mem
#print axioms bl_action_events
#print axioms bl_action_tags
#print axioms bl_action_cycleCount
#print axioms bl_action_sailOutput
#print axioms bl_action_choiceState
end NativeEntryCallerParts
