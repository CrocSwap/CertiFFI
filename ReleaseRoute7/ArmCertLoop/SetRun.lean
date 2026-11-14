import ArmCertLoop.SetBody
import LoopNative.RetABI
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.SetNative
open ContractDraft

theorem cost_positive (c : Context) : 0 < Schedule.setSteps c.n := by
  unfold Schedule.setSteps
  split <;> omega

theorem offset_entry (c : Context) : offset c 0 = 456#64 := by
  have index : 0 ≠ Schedule.setSteps c.n := by have := cost_positive c; omega
  simp only [offset, Schedule.nativeOffset, if_neg index, Schedule.setWordOffset, if_pos rfl]
  rfl

theorem offset_setup (c : Context) (positive : 0 < c.n) : offset c 1 = 460#64 := by
  have nz : c.n ≠ 0 := by omega
  have index : 1 ≠ Schedule.setSteps c.n := by simp only [Schedule.setSteps, if_neg nz]; omega
  simp only [offset, Schedule.nativeOffset, if_neg index, Schedule.setWordOffset,
    if_neg (by decide : ¬ (1 : Nat) = 0), if_neg nz, if_pos rfl]
  rfl

/-- Positive entry: actual CBZ64-not-taken followed by actual MOV x3,x0.
Establish the initial fill invariant and actual x4..x30 frame. -/
theorem enter (real : Type) [Sail.SailReal real] (c : Context) (entry : NativeState)
    (positive : 0 < c.n) (args : Args c entry) (env : Env c 0 entry) :
    ∃ x, Uget.Chain.modelRun real 2 entry = .ok () x ∧ Header c entry 0 x := by
  obtain ⟨dest, source, counterArg, link⟩ := args
  change entry.regs.gpr[0] = c.d at dest
  change entry.regs.gpr[1] = c.fill at source
  change entry.regs.gpr[2].toNat = c.n at counterArg
  change entry.regs.gpr[30] = c.returnPC at link
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (LoopNative.Cbz64.Dispatch.selected 2#5 6#19) entry := by
    exact fetch_index c 0 9 entry env (by decide) (by rw [env.v2.v1.pc, offset_entry]; rfl)
  have condition : ¬ LoopNative.Cbz64.condition 2#5 entry := by
    intro h
    have zero := congrArg BitVec.toNat ((LoopNative.Cbz64.condition_iff 2#5 entry).1 h)
    change entry.regs.gpr[2].toNat = 0 at zero
    omega
  have placed0 : entry.regs._PC + 4#64 = c.base + offset c 1 := by
    rw [env.v2.v1.pc, offset_entry, offset_setup c positive]
    bv_omega
  obtain ⟨a, run0, env1, holds0, memory0, _, _, frame0⟩ :=
    LoopNative.Cbz64.next_not_taken_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) 0 (cost_positive c) c.page
      (by rw [offset_entry]; decide) 2#5 6#19 (by decide) entry env condition placed0 fetch0
  have gpr0 := ValueFacts.nil_gpr entry a holds0
  have sp0 := ValueFacts.nil_sp entry a holds0
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.OrrMov64.selected 3#5 0#6 0#5) a := by
    exact fetch_index c 1 10 a env1 (by decide) (by rw [env1.v2.v1.pc, offset_setup c positive]; rfl)
  have placed1 : a.regs._PC + 4#64 = c.base + offset c 2 := by
    rw [env1.v2.v1.pc, offset_setup c positive]
    have index : (2 : Nat) = 2 + 4 * 0 + 0 := by omega
    rw [index, offset_body c 0 0 positive (by decide)]
    change c.base + 460#64 + 4#64 = c.base + 464#64
    bv_omega
  have nz : c.n ≠ 0 := by omega
  obtain ⟨x, run1, env2, holds1, memory1, _, frame1⟩ :=
    LoopNative.Mov64.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) 1
      (by simp only [Schedule.setSteps, if_neg nz]; omega) c.page
      (by rw [offset_setup c positive]; decide) 3#5 0#5 (by decide) (by decide) a env1 placed1 fetch1
  obtain ⟨gpr1, sp1⟩ := ValueFacts.mov 3#5 0#5 a x holds1
  change x.regs.gpr = a.regs.gpr.set 3 a.regs.gpr[0] at gpr1
  have gpr : x.regs.gpr = entry.regs.gpr.set 3 c.d := by rw [gpr1, gpr0, dest]
  have memory : x.mem = entry.mem := memory1.trans memory0
  have bytes : Bytes.FillPrefix c.dstPA (Aux.memoryView entry) (Aux.memoryView x) (c.fill.setWidth 8) c.n 0 := by
    have view : Aux.memoryView x = Aux.memoryView entry := by unfold Aux.memoryView; rw [memory]
    rw [view]
    exact Bytes.fillPrefix_zero c.dstPA (Aux.memoryView entry) (c.fill.setWidth 8) c.n
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

theorem offset_empty_ret (c : Context) (zero : c.n = 0) :
    offset c 1 = 480#64 := by
  simp only [offset, zero, Schedule.nativeOffset, Schedule.setSteps, Schedule.setWordOffset,
    if_pos rfl, if_neg (by decide : ¬ (1 : Nat) = 2), if_neg (by decide : ¬ (1 : Nat) = 0)]
  rfl

/-- Empty memset takes the actual CBZ/RET path and touches no data bytes.
The destination may be unmapped. -/
theorem empty (real : Type) [Sail.SailReal real] (c : Context) (entry : NativeState)
    (zero : c.n = 0) (args : Args c entry) (env : Env c 0 entry) :
    ∃ fin, Uget.Chain.modelRun real (Schedule.setSteps c.n) entry = .ok () fin ∧
      Env c (Schedule.setSteps c.n) fin ∧ Post c entry fin := by
  obtain ⟨dest, _, counterArg, link⟩ := args
  change entry.regs.gpr[0] = c.d at dest
  change entry.regs.gpr[2].toNat = c.n at counterArg
  change entry.regs.gpr[30] = c.returnPC at link
  have cost : Schedule.setSteps c.n = 2 := by simp [zero, Schedule.setSteps]
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (LoopNative.Cbz64.Dispatch.selected 2#5 6#19) entry := by
    exact fetch_index c 0 9 entry env (by decide) (by rw [env.v2.v1.pc, offset_entry]; rfl)
  have regZero : entry.regs.gpr[2] = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    change entry.regs.gpr[2].toNat = 0
    omega
  have condition : LoopNative.Cbz64.condition 2#5 entry := (LoopNative.Cbz64.condition_iff 2#5 entry).2 regZero
  have target : LoopNative.Cbz64.target 6#19 entry = c.base + 480#64 := by
    change entry.regs._PC + 24#64 = c.base + 480#64
    rw [env.v2.v1.pc, offset_entry]
    bv_omega
  have low : (LoopNative.Cbz64.target 6#19 entry).toNat < 2 ^ 55 := by
    rw [target]
    have := c.low
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have placed0 : LoopNative.Cbz64.target 6#19 entry = c.base + offset c 1 := by
    rw [target, offset_empty_ret c zero]
  obtain ⟨a, run0, env1, holds0, memory0, _, _, frame0⟩ :=
    LoopNative.Cbz64.next_taken_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) 0 (cost_positive c) c.page
      (by rw [offset_entry]; decide) 2#5 6#19 (by decide) entry env condition low placed0 fetch0
  have gpr0 := ValueFacts.nil_gpr entry a holds0
  have sp0 := ValueFacts.nil_sp entry a holds0
  have aLink : a.regs.gpr[30] = c.returnPC := by rw [gpr0]; exact link
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) a := by
    exact fetch_index c 1 15 a env1 (by decide) (by rw [env1.v2.v1.pc, offset_empty_ret c zero]; rfl)
  have finalIndex : (1 : Nat) + 1 = Schedule.setSteps c.n := by rw [cost]
  have placed1 : a.regs.gpr[30] = c.base + offset c (1 + 1) := by
    rw [aLink, finalIndex]
    simpa only [offset] using (Schedule.return_landing c.base c.returnPC (Schedule.setSteps c.n)
      (fun k => Generated.armcert_memset_entry + Schedule.setWordOffset c.n k)).symm
  obtain ⟨fin, run1, env2, memory1, gpr1, sp1, frame1, pc⟩ :=
    LoopNative.RetABI.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) 1 (by rw [cost]; omega) c.page
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

/-- Actual final RET and the complete memset functional/ABI postcondition. -/
theorem exit (real : Type) [Sail.SailReal real] (c : Context) (entry x : NativeState)
    (header : Header c entry c.n x) :
    ∃ y, Uget.Chain.modelRun real 1 x = .ok () y ∧ Env c (Schedule.setSteps c.n) y ∧
      y.mem = x.mem ∧ Post c entry y := by
  have nz : c.n ≠ 0 := by have := header.positive; omega
  have finalIndex : 2 + 4 * c.n + 1 = Schedule.setSteps c.n := by
    simp only [Schedule.setSteps, if_neg nz]
    omega
  have fetch : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) x := by
    exact fetch_index c (2 + 4 * c.n) 15 x header.environment (by decide) (by
      rw [header.environment.v2.v1.pc, offset_exit c header.positive]
      rfl)
  have placed : x.regs.gpr[30] = c.base + offset c (2 + 4 * c.n + 1) := by
    rw [header.link, finalIndex]
    simpa only [offset] using (Schedule.return_landing c.base c.returnPC (Schedule.setSteps c.n)
      (fun k => Generated.armcert_memset_entry + Schedule.setWordOffset c.n k)).symm
  obtain ⟨y, run, nextInv, memory, gpr, sp, kept, pc⟩ :=
    LoopNative.RetABI.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) (2 + 4 * c.n)
      (by simp only [Schedule.setSteps, if_neg nz]; omega) c.page
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
    obtain ⟨destPA, mappedD, _, _⟩ := c.data i room
    have dest : c.dstPA i = destPA.toNat := by simp only [Context.dstPA, mappedD, Option.getD_some]
    simp only [readByte, mappedD, Option.bind_some, memory]
    simpa only [Aux.memoryView, dest] using header.bytes.filled i room
  · intro pa outside
    rw [memory]
    apply header.bytes.frame pa
    rintro ⟨i, room, same⟩
    obtain ⟨p, mapped, _, _⟩ := c.data i room
    have physical : c.dstPA i = p.toNat := by simp only [Context.dstPA, mapped, Option.getD_some]
    apply outside
    refine ⟨i, room, ?_⟩
    rw [mapped, ← physical, same]
  · intro r saved
    change y.regs.gpr[r.val] = entry.regs.gpr[r.val]
    rw [gpr]
    exact header.saved r saved

/-- Complete arbitrary-length memset loop and RET. The natural variant is the
actual full64 remaining counter. Body/exit callbacks are discharged by concrete
native instruction proofs; the exact instruction count is derived. -/
theorem finish (real : Type) [Sail.SailReal real] (c : Context) (entry : NativeState)
    (i : Nat) (x : NativeState) (header : Header c entry i x) :
    ∃ fin, Uget.Chain.modelRun real (4 * (c.n - i) + 1) x = .ok () fin ∧
      Env c (Schedule.setSteps c.n) fin ∧ Post c entry fin := by
  suffices all : ∀ remaining i x, c.n - i = remaining → Header c entry i x →
      ∃ fin, Uget.Chain.modelRun real (4 * remaining + 1) x = .ok () fin ∧
        Env c (Schedule.setSteps c.n) fin ∧ Post c entry fin by
    exact all (c.n - i) i x rfl header
  intro remaining
  induction remaining using Nat.strongRecOn with
  | ind remaining ih =>
    intro i x rank header
    by_cases zero : remaining = 0
    · have last : i = c.n := by have bound := header.bound; omega
      subst i
      obtain ⟨fin, run, finalEnv, _, post⟩ := exit real c entry x header
      exact ⟨fin, by simpa only [zero, Nat.mul_zero, Nat.zero_add] using run, finalEnv, post⟩
    · have room : i < c.n := by have bound := header.bound; omega
      obtain ⟨next, run, _, nextHeader⟩ := body real c entry x i room header
      have lower : c.n - (i + 1) < remaining := by omega
      obtain ⟨fin, rest, finalEnv, post⟩ := ih (c.n - (i + 1)) lower (i + 1) next rfl nextHeader
      have cost : 4 + (4 * (c.n - (i + 1)) + 1) = 4 * remaining + 1 := by omega
      refine ⟨fin, ?_, finalEnv, post⟩
      rw [← cost]
      exact Aux.modelRun_append real 4 (4 * (c.n - (i + 1)) + 1) x next fin run rest

/-- Entire scalar memset, with exact native cost and no future-state premises. -/
theorem run (real : Type) [Sail.SailReal real] (c : Context) (entry : NativeState)
    (args : Args c entry) (env : Env c 0 entry) :
    ∃ fin, Uget.Chain.modelRun real (Schedule.setSteps c.n) entry = .ok () fin ∧
      Env c (Schedule.setSteps c.n) fin ∧ Post c entry fin := by
  by_cases zero : c.n = 0
  · exact empty real c entry zero args env
  · have positive : 0 < c.n := by omega
    obtain ⟨headerState, prefixRun, header⟩ := enter real c entry positive args env
    obtain ⟨fin, loopRun, finalEnv, post⟩ := finish real c entry 0 headerState header
    have cost : 2 + (4 * (c.n - 0) + 1) = Schedule.setSteps c.n := by
      simp only [Schedule.setSteps, ite_eq_right zero, Nat.sub_zero]; omega
    refine ⟨fin, ?_, finalEnv, post⟩
    rw [← cost]
    exact Aux.modelRun_append real 2 (4 * (c.n - 0) + 1) entry headerState fin prefixRun loopRun

#print axioms cost_positive
#print axioms offset_entry
#print axioms offset_setup
#print axioms enter
#print axioms offset_empty_ret
#print axioms empty
#print axioms exit
#print axioms finish
#print axioms run
end ArmCertLoop.SetNative
