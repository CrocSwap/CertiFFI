-- Route 7 unit 3: ADD/ADD/SUB/CBNZ tail of a copy iteration over EnvR (Runtime InvG), ported from loops CopyRest/CopyControl.
import Route7Copy.Pair
import Route7Steps.Class
import Route7Steps.Branch
import Route7StepsE.Class
import Route7StepsE.Branch
import ArmCertLoop.CopyControl
import ArmCertLoop.ValueFacts
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

variable (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)

theorem branch_target_r (i : Nat) (room : i < c.n) (x : NativeState) (env : EnvR c catalogue entry (2 + 6 * i + 5) x) :
    LoopNative.Cbnz64.target backImmediate x = c.base + 428#64 := by
  rw [LoopNative.Cbnz64.target, back_delta, pc_body_r c catalogue entry i 5 room (by decide) x env]
  unfold MemReloc.imageAddress
  change c.base + 448#64 + BitVec.ofInt 64 (-20) = c.base + 428#64
  bv_omega

theorem branch_low_r (i : Nat) (room : i < c.n) (x : NativeState) (env : EnvR c catalogue entry (2 + 6 * i + 5) x) :
    (LoopNative.Cbnz64.target backImmediate x).toNat < 2 ^ 55 := by
  rw [branch_target_r c catalogue entry i room x env]
  have low := c.low
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem branch_taken_placed_r (i : Nat) (again : i + 1 < c.n) (x : NativeState) (env : EnvR c catalogue entry (2 + 6 * i + 5) x) :
    LoopNative.Cbnz64.target backImmediate x = c.base + offset c.base c.returnPC c.n (2 + 6 * i + 5 + 1) := by
  rw [branch_target_r c catalogue entry i (by omega) x env, offset_after_body c i (by omega), if_pos again]
  rfl

theorem branch_not_placed_r (i : Nat) (last : i + 1 = c.n) (room : i < c.n) (x : NativeState)
    (env : EnvR c catalogue entry (2 + 6 * i + 5) x) :
    x.regs._PC + 4#64 = c.base + offset c.base c.returnPC c.n (2 + 6 * i + 5 + 1) := by
  rw [pc_body_r c catalogue entry i 5 room (by decide) x env, offset_after_body c i room, if_neg (by omega : ¬ i + 1 < c.n)]
  unfold MemReloc.imageAddress
  change c.base + 448#64 + 4#64 = c.base + 452#64
  bv_omega

/-- The CBNZ condition (op = 1, sf = 1) on X2 is X2 ≠ 0 (via loops' LoopNative.Cbnz64.condition_iff). -/
theorem cbnz_cond_iff (s : NativeState) :
    ReleaseProfile.HeapCbzAction.cbzCond s 1#1 1#1 2#5 ↔ s.regs.gpr[(GPRSummary.key (2#5).toNat).val] ≠ 0#64 := by
  rw [← LoopNative.Cbnz64.condition_iff 2#5 s]
  exact Iff.rfl

attribute [local instance 10] Classical.propDecidable in
theorem branch_step_r (real : Type) [Sail.SailReal real] (nodup : (c.spec.logicalRows.map (·.logical)).Nodup)
    (i : Nat) (room : i < c.n)
    (x : NativeState) (env : EnvR c catalogue entry (2 + 6 * i + 5) x)
    (remaining : x.regs.gpr[2].toNat = c.n - (i + 1)) :
    ∃ y, modelStep real x = .ok () y ∧ EnvR c catalogue entry (2 + 6 * i + 6) y ∧ y.mem = x.mem ∧
      y.regs.gpr = x.regs.gpr ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧ NativeEntry.Effects.Frame {} x.regs y.regs ∧
      StepEvents.EvShape c.spec c.mapping [] x y := by
  have fetch : FetchObligations c.spec c.config c.rows c.mapping (Route7Cbnz.Tail.W 2#5 backImmediate) x := by
    exact fetch_index_r c catalogue entry (2 + 6 * i + 5) 7 x env (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry] using
        pc_body_r c catalogue entry i 5 room (by decide) x env)
  have placed : (if ReleaseProfile.HeapCbzAction.cbzCond x 1#1 1#1 2#5
      then x.regs._PC + sign_extend (backImmediate ++ 0#2) 64 else x.regs._PC + 4#64) =
      c.base + offset c.base c.returnPC c.n (2 + 6 * i + 5 + 1) := by
    by_cases again : i + 1 < c.n
    · have nonzero : x.regs.gpr[(GPRSummary.key (2#5).toNat).val] ≠ 0#64 := by
        intro same
        have zero := congrArg BitVec.toNat same
        change x.regs.gpr[2].toNat = (0#64).toNat at zero
        simp only [BitVec.toNat_ofNat] at zero
        omega
      rw [if_pos ((cbnz_cond_iff x).2 nonzero)]
      change LoopNative.Cbnz64.target backImmediate x = _
      exact branch_taken_placed_r c catalogue entry i again x env
    · have zero : x.regs.gpr[(GPRSummary.key (2#5).toNat).val] = 0#64 := by
        apply BitVec.eq_of_toNat_eq
        change x.regs.gpr[2].toNat = 0
        omega
      rw [if_neg (fun h => (cbnz_cond_iff x).1 h zero)]
      exact branch_not_placed_r c catalogue entry i (by omega) room x env
  obtain ⟨y, run, inv', holds, memory, sys, z, dit, kept, choice, ev⟩ :=
    Route7Steps.cbnz64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget (2 + 6 * i + 5) catalogue
      (body_room c i 5 room (by decide)) c.page (body_aligned c i 5 room (by decide))
      2#5 backImmediate x env.core nodup (branch_low_r c catalogue entry i room x env) _ rfl placed fetch
  have env' : EnvR c catalogue entry (2 + 6 * i + 6) y := by
    have adv := ReleaseProfile.DefaultRuntime.InvG.advance env inv' True.intro ⟨0, choice, Nat.le_refl 0⟩
      (by rw [show 2 + 6 * i + 5 + 1 = 2 + 6 * i + 5 + 1 from rfl, memPast_step c.n i 5 room (by omega)]; simp)
    simpa only [show 2 + 6 * i + 5 + 1 = 2 + 6 * i + 6 by omega] using adv
  exact ⟨y, run, env', memory, ValueFacts.nil_gpr x y holds, ValueFacts.nil_sp x y holds, kept, ev⟩

end Route7Copy
#print axioms Route7Copy.branch_step_r

namespace Route7Copy
open ArmCertLoop ArmCertLoop.CopyNative ArmCertLoop.ContractDraft

/-- A zero-draw step (class/branch) advances EnvR at a non-memory index. -/
theorem advance0 (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (i j : Nat)
    (room : i < c.n) (hj : 2 ≤ j) (hj6 : j < 6) (x fin : NativeState)
    (env : EnvR c catalogue entry (2 + 6 * i + j) x)
    (core : ReleaseProfile.DefaultCurrent.CurrentInv c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
      (offset c.base c.returnPC c.n) c.budget (2 + 6 * i + j + 1) catalogue fin)
    (choice : NativeMteTagCheck.ChoiceDelta x fin 0) : EnvR c catalogue entry (2 + 6 * i + j + 1) fin :=
  ReleaseProfile.DefaultRuntime.InvG.advance env core True.intro ⟨0, choice, Nat.le_refl 0⟩
    (by rw [memPast_step c.n i j room hj6, if_neg (by omega)]; exact Nat.le_refl _)

theorem arithmetic_tail_r (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState) (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (i : Nat) (room : i < c.n)
    (x : NativeState) (env : EnvR c catalogue entry (2 + 6 * i + 2) x)
    (sourceCursor : x.regs.gpr[1] = c.s + BitVec.ofNat 64 i)
    (destCursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i)
    (remaining : x.regs.gpr[2].toNat = c.n - i) :
    ∃ y, Uget.Chain.modelRun real 4 x = .ok () y ∧ EnvR c catalogue entry (2 + 6 * (i + 1)) y ∧
      y.regs.gpr = ((x.regs.gpr.set 1 (c.s + BitVec.ofNat 64 (i + 1))).set 3
        (c.d + BitVec.ofNat 64 (i + 1))).set 2 (x.regs.gpr[2] - 1#64) ∧
      y.regs.gpr[2].toNat = c.n - (i + 1) ∧ y.mem = x.mem ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧
      NativeEntry.Effects.Frame {} x.regs y.regs ∧ Covered real (PcOk c) 4 x ∧
      Route7Trace.Traced real c.spec c.mapping (recsOf c) (pcOf c) 4 (2 + 6 * i + 2) x := by
  let k := 2 + 6 * i
  have fetch2 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.AddImm64.selected 1#5 1#5 1#12) x := by
    exact fetch_index_r c catalogue entry (k + 2) 4 x env (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry] using
        pc_body_r c catalogue entry i 2 room (by decide) x env)
  obtain ⟨a, run2, core3, values2, memory2, _, _, _, frame2, choice2, ev2⟩ :=
    Route7Steps.addImm64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget (k + 2) catalogue
      (body_room c i 2 room (by decide)) c.page (body_aligned c i 2 room (by decide))
      1#5 1#5 1#12 (by decide) (by decide) x env.core nodup
      (body_next_placed_r c catalogue entry i 2 room (by decide) x env) fetch2
  have env3 : EnvR c catalogue entry (2 + 6 * i + 3) a := advance0 c catalogue entry i 2 room (by omega) (by omega) x a env core3 choice2
  obtain ⟨gpr2, sp2⟩ := ValueFacts.add 1#5 1#5 1#12 x a values2
  change a.regs.gpr = x.regs.gpr.set 1 (x.regs.gpr[1] + 1#64) at gpr2
  have fetch3 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.AddImm64.selected 3#5 3#5 1#12) a := by
    exact fetch_index_r c catalogue entry (k + 3) 5 a env3 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry] using
        pc_body_r c catalogue entry i 3 room (by decide) a env3)
  obtain ⟨b, run3, core4, values3, memory3, _, _, _, frame3, choice3, ev3⟩ :=
    Route7Steps.addImm64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget (k + 3) catalogue
      (body_room c i 3 room (by decide)) c.page (body_aligned c i 3 room (by decide))
      3#5 3#5 1#12 (by decide) (by decide) a env3.core nodup
      (body_next_placed_r c catalogue entry i 3 room (by decide) a env3) fetch3
  have env4 : EnvR c catalogue entry (2 + 6 * i + 4) b := advance0 c catalogue entry i 3 room (by omega) (by omega) a b env3 core4 choice3
  obtain ⟨gpr3, sp3⟩ := ValueFacts.add 3#5 3#5 1#12 a b values3
  change b.regs.gpr = a.regs.gpr.set 3 (a.regs.gpr[3] + 1#64) at gpr3
  have fetch4 : FetchObligations c.spec c.config c.rows c.mapping
      (Route7Sub.Dispatch.selected 2#5 2#5 1#12) b := by
    exact fetch_index_r c catalogue entry (k + 4) 6 b env4 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry] using
        pc_body_r c catalogue entry i 4 room (by decide) b env4)
  obtain ⟨d, run4, core5, values4, memory4, _, _, _, frame4, choice4, ev4⟩ :=
    Route7Steps.subImm64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget (k + 4) catalogue
      (body_room c i 4 room (by decide)) c.page (body_aligned c i 4 room (by decide))
      2#5 2#5 1#12 (by decide) (by decide) b env4.core nodup
      (body_next_placed_r c catalogue entry i 4 room (by decide) b env4) fetch4
  have env5 : EnvR c catalogue entry (2 + 6 * i + 5) d := advance0 c catalogue entry i 4 room (by omega) (by omega) b d env4 core5 choice4
  obtain ⟨gpr4, sp4⟩ := ValueFacts.sub 2#5 2#5 1#12 b d values4
  change d.regs.gpr = b.regs.gpr.set 2 (b.regs.gpr[2] - 1#64) at gpr4
  have counterB : b.regs.gpr[2] = x.regs.gpr[2] := by rw [gpr3, gpr2]; simp
  have counterD : d.regs.gpr[2] = x.regs.gpr[2] - 1#64 := by rw [gpr4, Vector.getElem_set_self, counterB]
  have positive : 0 < x.regs.gpr[2].toNat := by omega
  have remainingD : d.regs.gpr[2].toNat = c.n - (i + 1) := by
    rw [counterD, Schedule.counter_pred _ positive, remaining]
    omega
  obtain ⟨y, run5, env6, memory5, gpr5, sp5, frame5, ev5⟩ := branch_step_r c catalogue entry real nodup i room d env5 remainingD
  have advance (base : BitVec 64) : base + BitVec.ofNat 64 i + 1#64 = base + BitVec.ofNat 64 (i + 1) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  have gpr : y.regs.gpr = ((x.regs.gpr.set 1 (c.s + BitVec.ofNat 64 (i + 1))).set 3
      (c.d + BitVec.ofNat 64 (i + 1))).set 2 (x.regs.gpr[2] - 1#64) := by
    rw [gpr5, gpr4, gpr3, gpr2]
    simp [sourceCursor, destCursor, advance]
  have elapsed : 2 + 6 * i + 6 = 2 + 6 * (i + 1) := by omega
  have pcY : PcOk c y := pcOk_of_env c catalogue entry _ y env6
  have pcD : d.regs._PC = pcOf c (2 + 6 * i + 5) := pcAt_of_env c catalogue entry _ d env5
  rw [elapsed] at env6
  have runY : Uget.Chain.modelRun real 4 x = .ok () y := by simp only [Uget.Chain.modelRun, run2, run3, run4, run5]
  refine ⟨y, runY, env6, gpr, ?_, memory5.trans (memory4.trans (memory3.trans memory2)),
    sp5.trans (sp4.trans (sp3.trans sp2)), ((frame2.trans frame3).trans frame4).trans frame5, ?_, ?_⟩
  · rw [gpr5]
    exact remainingD
  · -- coverage (loops): every state of the 4-step tail carries EnvR
    intro t ht
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) with h | h | h | h | h <;> subst h
    · exact ⟨x, rfl, pcOk_of_env c catalogue entry _ x env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run2], pcOk_of_env c catalogue entry _ a env3⟩
    · exact ⟨b, by simp only [Uget.Chain.modelRun, run2, run3], pcOk_of_env c catalogue entry _ b env4⟩
    · exact ⟨d, by simp only [Uget.Chain.modelRun, run2, run3, run4], pcOk_of_env c catalogue entry _ d env5⟩
    · exact ⟨y, runY, pcY⟩
  · -- trace (loops CT0): ADD / ADD / SUB / CBNZ carry no data records
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with h | h | h | h <;> subst h
    · refine ⟨x, a, rfl, run2, ?_, ?_⟩
      · rw [show 2 + 6 * i + 2 + 0 = 2 + 6 * i + 2 by omega]; exact pcAt_of_env c catalogue entry _ x env
      · rw [show 2 + 6 * i + 2 + 0 = 2 + 6 * i + 2 by omega, recs_body c i 2 room (by omega) (by omega)]; exact ⟨ev2, frame2⟩
    · refine ⟨a, b, by simp only [Uget.Chain.modelRun, run2], run3, ?_, ?_⟩
      · rw [show 2 + 6 * i + 2 + 1 = 2 + 6 * i + 3 by omega]; exact pcAt_of_env c catalogue entry _ a env3
      · rw [show 2 + 6 * i + 2 + 1 = 2 + 6 * i + 3 by omega, recs_body c i 3 room (by omega) (by omega)]; exact ⟨ev3, frame3⟩
    · refine ⟨b, d, by simp only [Uget.Chain.modelRun, run2, run3], run4, ?_, ?_⟩
      · rw [show 2 + 6 * i + 2 + 2 = 2 + 6 * i + 4 by omega]; exact pcAt_of_env c catalogue entry _ b env4
      · rw [show 2 + 6 * i + 2 + 2 = 2 + 6 * i + 4 by omega, recs_body c i 4 room (by omega) (by omega)]; exact ⟨ev4, frame4⟩
    · refine ⟨d, y, by simp only [Uget.Chain.modelRun, run2, run3, run4], run5, ?_, ?_⟩
      · rw [show 2 + 6 * i + 2 + 3 = 2 + 6 * i + 5 by omega]; exact pcAt_of_env c catalogue entry _ d env5
      · rw [show 2 + 6 * i + 2 + 3 = 2 + 6 * i + 5 by omega, recs_body c i 5 room (by omega) (by omega)]; exact ⟨ev5, frame5⟩

end Route7Copy
#print axioms Route7Copy.arithmetic_tail_r
