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
noncomputable def blrActionState (Rn : BitVec 5) (s : NativeState) : NativeState :=
  branchState (blrTarget Rn s) BranchType.BranchType_INDCALL (blrBeforeCall Rn s)

theorem blr_run (Rn : BitVec 5) (s : NativeState) (hp : CallerControls s) (rn : Rn.toNat < 31)
    (low : (blrTarget Rn s).toNat < 2^55) :
    (decode_blr_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 1#2 0#1 : SailM Unit) s = .ok () (blrActionState Rn s) := by
  rw [blr_boundary Rn s hp rn]
  exact branch_run _ _ _ (blr_controls Rn s hp) (low_bit55 _ low)

theorem blr_action_controls (Rn : BitVec 5) (s : NativeState) (hp : CallerControls s) :
    CallerControls (blrActionState Rn s) :=
  branch_controls _ _ _ (blr_controls Rn s hp)

theorem blr_action_btn (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.BTypeNext = 2#2 := by
  exact (branch_BTypeNext _ _ _).trans (blr_btn Rn s)

theorem blr_action_taken (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.__BranchTaken = true := branch_taken _ _ _

theorem blr_action_type (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.Branchtypetaken = BranchType.BranchType_INDCALL := branch_type _ _ _

theorem blr_action_pc (Rn : BitVec 5) (s : NativeState) (hp : CallerControls s)
    (low : (blrTarget Rn s).toNat < 2^55) :
    (blrActionState Rn s).regs._PC = blrTarget Rn s :=
  (branch_pc _ _ _).trans (address_low _ _ (hint_controls _ _ (blr_controls Rn s hp)) low)

theorem blr_action_PSTATE (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.PSTATE = s.regs.PSTATE :=
  (branch_PSTATE _ _ _).trans (blr_PSTATE Rn s)

theorem blr_action_FPCR (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.FPCR = s.regs.FPCR :=
  (branch_FPCR _ _ _).trans (blr_FPCR Rn s)

theorem blr_action_FPSR (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.FPSR = s.regs.FPSR :=
  (branch_FPSR _ _ _).trans (blr_FPSR Rn s)

theorem blr_action__Z (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs._Z = s.regs._Z :=
  (branch__Z _ _ _).trans (blr__Z Rn s)

theorem blr_action_SP_EL0 (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).regs.SP_EL0 = s.regs.SP_EL0 :=
  (branch_SP_EL0 _ _ _).trans (blr_SP_EL0 Rn s)

theorem blr_action_mem (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).mem = s.mem :=
  (branch_mem _ _ _).trans (blr_mem Rn s)

theorem blr_action_events (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).events = s.events :=
  (branch_events _ _ _).trans (blr_events Rn s)

theorem blr_action_tags (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).tags = s.tags :=
  (branch_tags _ _ _).trans (blr_tags Rn s)

theorem blr_action_cycleCount (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).cycleCount = s.cycleCount :=
  (branch_cycleCount _ _ _).trans (blr_cycleCount Rn s)

theorem blr_action_sailOutput (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).sailOutput = s.sailOutput :=
  (branch_sailOutput _ _ _).trans (blr_sailOutput Rn s)

theorem blr_action_choiceState (Rn : BitVec 5) (s : NativeState) :
    (blrActionState Rn s).choiceState = s.choiceState :=
  (branch_choiceState _ _ _).trans (blr_choiceState Rn s)

#print axioms blr_run
#print axioms blr_action_controls
#print axioms blr_action_btn
#print axioms blr_action_taken
#print axioms blr_action_type
#print axioms blr_action_pc
#print axioms blr_action_PSTATE
#print axioms blr_action_FPCR
#print axioms blr_action_FPSR
#print axioms blr_action__Z
#print axioms blr_action_SP_EL0
#print axioms blr_action_mem
#print axioms blr_action_events
#print axioms blr_action_tags
#print axioms blr_action_cycleCount
#print axioms blr_action_sailOutput
#print axioms blr_action_choiceState
end NativeEntryCallerParts
