import ArmCertLoop.CopyEntry
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

theorem offset_empty_ret (c : Context) (zero : c.n = 0) :
    offset c.base c.returnPC c.n 1 = 452#64 := by
  simp only [offset, zero, Schedule.nativeOffset, Schedule.copySteps, Schedule.copyWordOffset,
    if_pos rfl, if_neg (by decide : ¬ (1 : Nat) = 2), if_neg (by decide : ¬ (1 : Nat) = 0)]
  rfl

/-- Empty memcpy performs CBZ/RET and touches no data bytes. Source/destination
can be unmapped: data geometry and source presence have empty ranges. -/
theorem empty (real : Type) [Sail.SailReal real] (c : Context) (entry : NativeState)
    (zero : c.n = 0) (args : Args c.d c.s c.returnPC c.n entry) (env : Env c 0 entry) :
    ∃ fin, Uget.Chain.modelRun real (Schedule.copySteps c.n) entry = .ok () fin ∧
      Env c (Schedule.copySteps c.n) fin ∧ CopyPost c.mapping c.d c.s c.returnPC c.n entry fin := by
  obtain ⟨dest, _, counterArg, link⟩ := args
  change entry.regs.gpr[0] = c.d at dest
  change entry.regs.gpr[2].toNat = c.n at counterArg
  change entry.regs.gpr[30] = c.returnPC at link
  have cost : Schedule.copySteps c.n = 2 := by simp [zero, Schedule.copySteps]
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (LoopNative.Cbz64.Dispatch.selected 2#5 8#19) entry := by
    exact fetch_index c 0 0 entry env (by decide) (by rw [env.v2.v1.pc, offset_entry]; rfl)
  have regZero : entry.regs.gpr[2] = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    change entry.regs.gpr[2].toNat = 0
    omega
  have condition : LoopNative.Cbz64.condition 2#5 entry := (LoopNative.Cbz64.condition_iff 2#5 entry).2 regZero
  have target : LoopNative.Cbz64.target 8#19 entry = c.base + 452#64 := by
    change entry.regs._PC + 32#64 = c.base + 452#64
    rw [env.v2.v1.pc, offset_entry]
    bv_omega
  have low : (LoopNative.Cbz64.target 8#19 entry).toNat < 2 ^ 55 := by
    rw [target]
    have := c.low
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have placed0 : LoopNative.Cbz64.target 8#19 entry = c.base + offset c.base c.returnPC c.n 1 := by
    rw [target, offset_empty_ret c zero]
  obtain ⟨a, run0, env1, holds0, memory0, _, _, frame0⟩ :=
    LoopNative.Cbz64.next_taken_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget 0 (budget_positive c) c.page
      (by rw [offset_entry]; decide) 2#5 8#19 (by decide) entry env condition low placed0 fetch0
  have gpr0 := ValueFacts.nil_gpr entry a holds0
  have sp0 := ValueFacts.nil_sp entry a holds0
  have aLink : a.regs.gpr[30] = c.returnPC := by rw [gpr0]; exact link
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) a := by
    exact fetch_index c 1 8 a env1 (by decide) (by rw [env1.v2.v1.pc, offset_empty_ret c zero]; rfl)
  have finalIndex : (1 : Nat) + 1 = Schedule.copySteps c.n := by rw [cost]
  have placed1 : a.regs.gpr[30] = c.base + offset c.base c.returnPC c.n (1 + 1) := by
    rw [aLink, finalIndex]
    simpa only [offset] using (Schedule.return_landing c.base c.returnPC (Schedule.copySteps c.n)
      (fun k => Generated.armcert_memcpy_entry + Schedule.copyWordOffset c.n k)).symm
  obtain ⟨fin, run1, env2, memory1, gpr1, sp1, frame1, pc⟩ :=
    LoopNative.RetABI.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget 1 (by rw [Context.budget, cost]; omega) c.page
      (by rw [offset_empty_ret c zero]; decide) 30#5 (by decide) a env1
      (by change a.regs.gpr[30].toNat < 2 ^ 55; rw [aLink]; have := c.returnLow; omega) placed1 fetch1
  rw [finalIndex] at env2
  have memory : fin.mem = entry.mem := memory1.trans memory0
  have gpr : fin.regs.gpr = entry.regs.gpr := gpr1.trans gpr0
  have abi := frame0.trans frame1
  refine ⟨fin, ?_, env2, pc.trans aLink, ?_, ?_, ?_, ?_, sp1.trans sp0,
    LoopNative.MemoryFrame.vector abi rfl, LoopNative.MemoryFrame.fpcr abi rfl, LoopNative.MemoryFrame.fpsr abi rfl⟩
  · rw [cost]
    simp only [Uget.Chain.modelRun, run0, run1]
  · change fin.regs.gpr[0] = c.d
    rw [gpr]
    exact dest
  · intro i impossible
    omega
  · intro pa _
    rw [memory]
  · intro r _
    change fin.regs.gpr[r.val] = entry.regs.gpr[r.val]
    rw [gpr]

#print axioms offset_empty_ret
#print axioms empty
end ArmCertLoop.CopyNative
