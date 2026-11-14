-- Route 7 unit 3: positive entry (CBZ not taken, MOV x3,x0) over EnvR, ported from loops CopyEntry.enter.
import Route7Copy.Body
import ArmCertLoop.CopyEntry
import Route7Trace.Copy
import Route7StepsE.Class
import Route7StepsE.Branch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 1024
set_option Elab.async false
namespace Route7Copy
open ArmCertLoop ArmCertLoop.CopyNative ArmCertLoop.ContractDraft

/-- The CBZ X condition on X2 is X2 = 0 (via loops' LoopNative.Cbz64.condition_iff). -/
theorem cbz_cond_iff (s : NativeState) :
    Crypto.CruxCbz.cbzC 1#1 2#5 s ↔ s.regs.gpr[(GPRSummary.key (2#5).toNat).val] = 0#64 := by
  rw [← LoopNative.Cbz64.condition_iff 2#5 s]
  exact Iff.rfl

/-- A zero-draw step at a pre-loop index (0 or 1) advances EnvR. -/
theorem advance_pre (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat) (hk : k < 2)
    (x fin : NativeState) (env : EnvR c catalogue entry k x)
    (core : ReleaseProfile.DefaultCurrent.CurrentInv c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
      (offset c.base c.returnPC c.n) c.budget (k + 1) catalogue fin)
    (choice : NativeMteTagCheck.ChoiceDelta x fin 0) : EnvR c catalogue entry (k + 1) fin :=
  ReleaseProfile.DefaultRuntime.InvG.advance env core True.intro ⟨0, choice, Nat.le_refl 0⟩
    (by rw [memPast_succ, memStep_pre c.n k hk]; exact Nat.le_refl _)

attribute [local instance 10] Classical.propDecidable in
theorem enter_r (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (positive : 0 < c.n) (args : Args c.d c.s c.returnPC c.n entry) (env : EnvR c catalogue entry 0 entry) :
    ∃ x, Uget.Chain.modelRun real 2 entry = .ok () x ∧ HeaderR c catalogue entry 0 x ∧
      Covered real (PcOk c) 2 entry ∧ Route7Trace.Traced real c.spec c.mapping (recsOf c) (pcOf c) 2 0 entry := by
  obtain ⟨dest, source, counterArg, link⟩ := args
  change entry.regs.gpr[0] = c.d at dest
  change entry.regs.gpr[1] = c.s at source
  change entry.regs.gpr[2].toNat = c.n at counterArg
  change entry.regs.gpr[30] = c.returnPC at link
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyCbz.W 2#5 8#19) entry := by
    exact fetch_index_r c catalogue entry 0 0 entry env (by decide) (by rw [env.core.v1.pc, offset_entry]; rfl)
  have nonzero : ¬ Crypto.CruxCbz.cbzC 1#1 2#5 entry := by
    intro h
    have zero := congrArg BitVec.toNat ((cbz_cond_iff entry).1 h)
    change entry.regs.gpr[2].toNat = 0 at zero
    omega
  have placed0 : entry.regs._PC + 4#64 = c.base + offset c.base c.returnPC c.n 1 := by
    rw [env.core.v1.pc, offset_entry, offset_setup c positive]
    bv_omega
  have hlow : (entry.regs._PC + sign_extend (8#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [env.core.v1.pc, offset_entry]
    have low := c.low
    change (c.base + 420#64 + 32#64).toNat < 2 ^ 55
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  obtain ⟨a, run0, core1, holds0, memory0, _, _, _, frame0, choice0, ev0⟩ :=
    Route7Steps.cbz64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget 0 catalogue (budget_positive c) c.page
      (by rw [offset_entry]; decide) 2#5 8#19 entry env.core nodup hlow (entry.regs._PC + 4#64)
      (by rw [if_neg nonzero]) placed0 fetch0
  have env1 : EnvR c catalogue entry 1 a := advance_pre c catalogue entry 0 (by omega) entry a env core1 choice0
  have gpr0 := ValueFacts.nil_gpr entry a holds0
  have sp0 := ValueFacts.nil_sp entry a holds0
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.OrrMov64.selected 3#5 0#6 0#5) a := by
    exact fetch_index_r c catalogue entry 1 1 a env1 (by decide) (by rw [env1.core.v1.pc, offset_setup c positive]; rfl)
  have placed1 : a.regs._PC + 4#64 = c.base + offset c.base c.returnPC c.n 2 := by
    rw [env1.core.v1.pc, offset_setup c positive]
    have index : (2 : Nat) = 2 + 6 * 0 + 0 := by omega
    rw [index, offset_body c 0 0 positive (by decide)]
    change c.base + 424#64 + 4#64 = c.base + 428#64
    bv_omega
  have nz : c.n ≠ 0 := by omega
  obtain ⟨x, run1, core2, holds1, memory1, _, _, _, frame1, choice1, ev1⟩ :=
    Route7Steps.mov64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget 1 catalogue
      (by simp only [Context.budget, Schedule.copySteps, if_neg nz]; omega) c.page
      (by rw [offset_setup c positive]; decide) 3#5 0#5 (by decide) (by decide) a env1.core nodup placed1 fetch1
  have env2 : EnvR c catalogue entry 2 x := advance_pre c catalogue entry 1 (by omega) a x env1 core2 choice1
  obtain ⟨gpr1, sp1⟩ := ValueFacts.mov 3#5 0#5 a x holds1
  change x.regs.gpr = a.regs.gpr.set 3 a.regs.gpr[0] at gpr1
  have gpr : x.regs.gpr = entry.regs.gpr.set 3 c.d := by rw [gpr1, gpr0, dest]
  have memory : x.mem = entry.mem := memory1.trans memory0
  have bytes : Bytes.CopyPrefix c.srcPA c.dstPA (Aux.memoryView entry) (Aux.memoryView x) c.n 0 := by
    have view : Aux.memoryView x = Aux.memoryView entry := by unfold Aux.memoryView; rw [memory]
    rw [view]
    exact Bytes.copyPrefix_zero c.srcPA c.dstPA (Aux.memoryView entry) c.n
  have runX : Uget.Chain.modelRun real 2 entry = .ok () x := by simp only [Uget.Chain.modelRun, run0, run1]
  have cov : Covered real (PcOk c) 2 entry := by
    intro t ht
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with h | h | h <;> subst h
    · exact ⟨entry, rfl, pcOk_of_env c catalogue entry _ entry env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env c catalogue entry _ a env1⟩
    · exact ⟨x, runX, pcOk_of_env c catalogue entry _ x env2⟩
  refine ⟨x, runX, ⟨positive, by omega, by simpa using env2, ?_, ?_, ?_, ?_, ?_, ?_,
    sp1.trans sp0, frame0.trans frame1, bytes⟩, cov,
    Route7Trace.traced_append real c.spec c.mapping (recsOf c) (pcOf c) 1 1 0 entry a (Route7Trace.run_one real entry a run0)
      (Route7Trace.traced_one real c.spec c.mapping (recsOf c) (pcOf c) 0 entry a run0
        (pcAt_of_env c catalogue entry _ entry env) (by rw [recs_pre c 0 (by omega)]; exact ev0) frame0)
      (Route7Trace.traced_one real c.spec c.mapping (recsOf c) (pcOf c) (0 + 1) a x run1
        (pcAt_of_env c catalogue entry _ a env1) (by rw [recs_pre c (0 + 1) (by omega)]; exact ev1) frame1)⟩
  · rw [gpr]; simpa using dest
  · rw [gpr]; simpa using source
  · rw [gpr]; simp
  · rw [gpr]; simpa using counterArg
  · rw [gpr]; simpa using link
  · intro r saved
    have different : 3 ≠ r.val := by omega
    rw [gpr]
    simp [Vector.getElem_set, different]

end Route7Copy
#print axioms Route7Copy.enter_r
