import ArmCertLoop.CopyFinish
import LoopNative.ArithmeticABI
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

theorem cost_positive (c : Context) : 0 < Schedule.copySteps c.n := by
  unfold Schedule.copySteps
  split <;> omega

theorem budget_positive (c : Context) : 0 < c.budget := Nat.lt_of_lt_of_le (cost_positive c) (budget_enough c)

theorem offset_entry (c : Context) : offset c.base c.returnPC c.n 0 = 420#64 := by
  have index : 0 ≠ Schedule.copySteps c.n := by have := cost_positive c; omega
  simp only [offset, Schedule.nativeOffset, if_neg index, Schedule.copyWordOffset, if_pos rfl]
  rfl

theorem offset_setup (c : Context) (positive : 0 < c.n) : offset c.base c.returnPC c.n 1 = 424#64 := by
  have nz : c.n ≠ 0 := by omega
  have index : 1 ≠ Schedule.copySteps c.n := by simp only [Schedule.copySteps, if_neg nz]; omega
  simp only [offset, Schedule.nativeOffset, if_neg index, Schedule.copyWordOffset,
    if_neg (by decide : ¬ (1 : Nat) = 0), if_neg nz, if_pos rfl]
  rfl

/-- Positive entry: actual CBZ64-not-taken followed by actual MOV x3,x0.
The original RAM snapshot and the stronger x6..x30 frame are established here. -/
theorem enter (real : Type) [Sail.SailReal real] (c : Context) (entry : NativeState)
    (positive : 0 < c.n) (args : Args c.d c.s c.returnPC c.n entry) (env : Env c 0 entry) :
    ∃ x, Uget.Chain.modelRun real 2 entry = .ok () x ∧ Header c entry 0 x := by
  obtain ⟨dest, source, counterArg, link⟩ := args
  change entry.regs.gpr[0] = c.d at dest
  change entry.regs.gpr[1] = c.s at source
  change entry.regs.gpr[2].toNat = c.n at counterArg
  change entry.regs.gpr[30] = c.returnPC at link
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (LoopNative.Cbz64.Dispatch.selected 2#5 8#19) entry := by
    exact fetch_index c 0 0 entry env (by decide) (by rw [env.v2.v1.pc, offset_entry]; rfl)
  have condition : ¬ LoopNative.Cbz64.condition 2#5 entry := by
    intro h
    have zero := congrArg BitVec.toNat ((LoopNative.Cbz64.condition_iff 2#5 entry).1 h)
    change entry.regs.gpr[2].toNat = 0 at zero
    omega
  have placed0 : entry.regs._PC + 4#64 = c.base + offset c.base c.returnPC c.n 1 := by
    rw [env.v2.v1.pc, offset_entry, offset_setup c positive]
    bv_omega
  obtain ⟨a, run0, env1, holds0, memory0, _, _, frame0⟩ :=
    LoopNative.Cbz64.next_not_taken_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget 0 (budget_positive c) c.page
      (by rw [offset_entry]; decide) 2#5 8#19 (by decide) entry env condition placed0 fetch0
  have gpr0 := ValueFacts.nil_gpr entry a holds0
  have sp0 := ValueFacts.nil_sp entry a holds0
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.OrrMov64.selected 3#5 0#6 0#5) a := by
    exact fetch_index c 1 1 a env1 (by decide) (by rw [env1.v2.v1.pc, offset_setup c positive]; rfl)
  have placed1 : a.regs._PC + 4#64 = c.base + offset c.base c.returnPC c.n 2 := by
    rw [env1.v2.v1.pc, offset_setup c positive]
    have index : (2 : Nat) = 2 + 6 * 0 + 0 := by omega
    rw [index, offset_body c 0 0 positive (by decide)]
    change c.base + 424#64 + 4#64 = c.base + 428#64
    bv_omega
  have nz : c.n ≠ 0 := by omega
  obtain ⟨x, run1, env2, holds1, memory1, _, frame1⟩ :=
    LoopNative.Mov64.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget 1
      (by simp only [Context.budget, Schedule.copySteps, if_neg nz]; omega) c.page
      (by rw [offset_setup c positive]; decide) 3#5 0#5 (by decide) (by decide) a env1 placed1 fetch1
  obtain ⟨gpr1, sp1⟩ := ValueFacts.mov 3#5 0#5 a x holds1
  change x.regs.gpr = a.regs.gpr.set 3 a.regs.gpr[0] at gpr1
  have gpr : x.regs.gpr = entry.regs.gpr.set 3 c.d := by rw [gpr1, gpr0, dest]
  have memory : x.mem = entry.mem := memory1.trans memory0
  have bytes : Bytes.CopyPrefix c.srcPA c.dstPA (Aux.memoryView entry) (Aux.memoryView x) c.n 0 := by
    have view : Aux.memoryView x = Aux.memoryView entry := by unfold Aux.memoryView; rw [memory]
    rw [view]
    exact Bytes.copyPrefix_zero c.srcPA c.dstPA (Aux.memoryView entry) c.n
  refine ⟨x, by simp only [Uget.Chain.modelRun, run0, run1], positive, by omega, env2, ?_, ?_, ?_, ?_, ?_, ?_,
    sp1.trans sp0, frame0.trans frame1, bytes⟩
  · rw [gpr]; simpa using dest
  · rw [gpr]; simpa using source
  · rw [gpr]; simp
  · rw [gpr]; simpa using counterArg
  · rw [gpr]; simpa using link
  · intro r saved
    have different : 3 ≠ r.val := by omega
    rw [gpr]
    simp [Vector.getElem_set, different]

#print axioms cost_positive
#print axioms budget_positive
#print axioms offset_entry
#print axioms offset_setup
#print axioms enter
end ArmCertLoop.CopyNative
