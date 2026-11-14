import Bridge.CruxGenGuarded.EntryCallerFrames
import NativeEntryCallerRegisters.Registers
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
open NativeEntryCallerParts NativeEntryCallerTransport
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryTail (EntryPins)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/- Internal selected-action join into the unchanged canonical tail. All
premises concern its current input. Original dispatch, fetch and the whole
Entry domain are separate producers. The last frame starts at the actual
action state: SPE may really clear input PrevValid. -/
run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.bl_action_tail"
  (← IO.getStderr).flush

theorem bl_action_tail (real : Type) [Sail.SailReal real]
    (initial : NativeState) (w : BitVec 32) (enc0 : __InstrEnc)
    (imm26 : BitVec 26) (s : NativeState) (b : Nat)
    (controls : CallerControls s)
    (low : (blTarget imm26 s).toNat < 2^55)
    (hq : HookQuiet (b + 1) s) (hp : EntryPins s)
    (hEnc : s.regs.__ThisInstrEnc = .__A64)
    (hEret : (Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false)
    (hIT : s.regs.ShouldAdvanceIT = false) (hSS : s.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeAtAction real initial w (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1) enc0 s = .ok () fin ∧
      HookQuiet b fin ∧ EntryPins fin ∧
      fin.regs.PSTATE.BTYPE = s.regs.BTypeNext ∧ fin.regs.BTypeNext = s.regs.BTypeNext ∧
      SysEq2 s.regs fin.regs ∧ BrSysEq s.regs fin.regs ∧
      CongOut fin (blActionState imm26 s) ∧ fin.events = s.events ∧
      fin.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending ∧
      fin.regs.PSTATE.DIT = s.regs.PSTATE.DIT ∧
      fin.regs._PC = blTarget imm26 s ∧
      fin.mem = s.mem ∧ fin.regs.gpr = s.regs.gpr.set 30 (NativeEntryCallerRegisters.linkValue s) ∧
      fin.regs.gpr[30] = s.regs._PC + 4#64 ∧
      ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap
        (blActionState imm26 s).regs fin.regs := by
  have hEncA : (blActionState imm26 s).regs.__ThisInstrEnc = .__A64 :=
    (bl___ThisInstrEnc imm26 s).trans hEnc
  have hEretA : (Sail.BitVec.extractLsb ((blActionState imm26 s).regs.bank_BitVec_32 .__ThisInstr) 31 12 == 879088#20) = false := by
    rw [bl_bank_BitVec_32]; exact hEret
  obtain ⟨fin, run, quiet, pins, btype, next, sys, branch, out, events, gic, dit, pc, frame⟩ :=
    guarded_after_action_current real initial w enc0 (blActionState imm26 s) b
      (bl_quiet imm26 s (b + 1) hq) (bl_pins imm26 s hp) hEncA hEretA
      ((bl_ShouldAdvanceIT imm26 s).trans hIT)
      ((bl_ShouldAdvanceSS imm26 s).trans hSS)
  refine ⟨fin, ?_, quiet, pins, btype.trans (bl_action_btn imm26 s),
    next.trans (bl_action_btn imm26 s),
    sysEq2_trans _ _ _ (bl_action_sys imm26 s) sys,
    brSysEq_trans _ _ _ (bl_action_branch imm26 s) branch, out,
    events.trans (bl_action_events imm26 s),
    gic.trans (congrFun (bl_bank_Option_InterruptID imm26 s) _),
    dit.trans (congrArg ProcState.DIT (bl_action_PSTATE imm26 s)), ?_,
    out.mem.trans (bl_action_mem imm26 s),
    out.gpr.trans (NativeEntryCallerRegisters.bl_gpr imm26 s), ?_, frame⟩
  · exact (action_boundary real initial w (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1) enc0 s _
      (bl_run imm26 s controls low)).trans run
  · simpa only [bl_action_taken, Bool.true_eq, ite_true] using
      pc.trans (by rw [bl_action_taken]; exact bl_action_pc imm26 s controls low)
  · rw [out.gpr]
    exact NativeEntryCallerRegisters.bl_lr imm26 s

#print axioms bl_action_tail
end ArmBridge.CruxGenGuarded
