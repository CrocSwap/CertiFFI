import ArmCertLoop.CopyBody
import LoopNative.RetABI
import LoopNative.MemoryFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open HeapV2StepCerts.RegBind (regVal Reg)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.CopyNative
open ContractDraft

theorem offset_exit (c : Context) (positive : 0 < c.n) :
    offset c.base c.returnPC c.n (2 + 6 * c.n) = 452#64 := by
  have nz : c.n ≠ 0 := by omega
  have index : 2 + 6 * c.n ≠ Schedule.copySteps c.n := by
    simp only [Schedule.copySteps, if_neg nz]
    omega
  have elapsed : 2 + 6 * c.n = 6 * c.n + 2 := by omega
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg index, elapsed, Schedule.copy_exit_offset c.n positive]
  rfl

/-- Actual final RET and the complete memcpy functional/ABI postcondition. -/
theorem exit (real : Type) [Sail.SailReal real] (c : Context) (entry x : NativeState)
    (header : Header c entry c.n x) :
    ∃ y, Uget.Chain.modelRun real 1 x = .ok () y ∧ Env c (Schedule.copySteps c.n) y ∧
      y.mem = x.mem ∧ CopyPost c.mapping c.d c.s c.returnPC c.n entry y := by
  have nz : c.n ≠ 0 := by have := header.positive; omega
  have finalIndex : 2 + 6 * c.n + 1 = Schedule.copySteps c.n := by
    simp only [Schedule.copySteps, if_neg nz]
    omega
  have fetch : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) x := by
    exact fetch_index c (2 + 6 * c.n) 8 x header.environment (by decide) (by
      rw [header.environment.v2.v1.pc, offset_exit c header.positive]
      rfl)
  have placed : x.regs.gpr[30] = c.base + offset c.base c.returnPC c.n (2 + 6 * c.n + 1) := by
    rw [header.link, finalIndex]
    simpa only [offset] using (Schedule.return_landing c.base c.returnPC (Schedule.copySteps c.n)
      (fun k => Generated.armcert_memcpy_entry + Schedule.copyWordOffset c.n k)).symm
  obtain ⟨y, run, nextInv, memory, gpr, sp, kept, pc⟩ :=
    LoopNative.RetABI.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget (2 + 6 * c.n)
      (by simp only [Context.budget, Schedule.copySteps, if_neg nz]; omega) c.page
      (by rw [offset_exit c header.positive]; decide) 30#5 (by decide) x header.environment
      (by change x.regs.gpr[30].toNat < 2 ^ 55; rw [header.link]; have := c.returnLow; omega) placed fetch
  rw [finalIndex] at nextInv
  have abi := header.protectedRegs.trans kept
  refine ⟨y, by simp only [Uget.Chain.modelRun, run], nextInv, memory, pc.trans header.link, ?_, ?_, ?_, ?_,
    sp.trans header.sp, LoopNative.MemoryFrame.vector abi rfl,
    LoopNative.MemoryFrame.fpcr abi rfl, LoopNative.MemoryFrame.fpsr abi rfl⟩
  · change y.regs.gpr[0] = c.d
    rw [gpr]
    exact header.dest
  · intro i room
    obtain ⟨sourcePA, mappedS, _, _⟩ := source_mapped c i room
    obtain ⟨destPA, mappedD, _, _⟩ := dest_mapped c i room
    have source : c.srcPA i = sourcePA.toNat := by simp only [Context.srcPA, mappedS, Option.getD_some]
    have dest : c.dstPA i = destPA.toNat := by simp only [Context.dstPA, mappedD, Option.getD_some]
    simp only [readByte, mappedD, mappedS, Option.bind_some, memory]
    simpa only [Aux.memoryView, source, dest] using header.bytes.copied i room
  · intro pa outside
    rw [memory]
    exact final_frame c entry x header.bytes pa outside
  · intro r saved
    change y.regs.gpr[r.val] = entry.regs.gpr[r.val]
    rw [gpr]
    exact header.saved r saved

#print axioms offset_exit
#print axioms exit
end ArmCertLoop.CopyNative
