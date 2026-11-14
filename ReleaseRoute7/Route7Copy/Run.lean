-- Route 7 unit 3: empty memcpy, the iteration induction and the complete memcpy run over EnvR (Runtime InvG),
-- ported from loops CopyZero/CopyFinish/CopyRun.
import Route7Copy.Entry
import ArmCertLoop.CopyZero
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

theorem header_source_r (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry x : NativeState) (i : Nat)
    (room : i < c.n) (present : SourcePresent c.mapping c.s c.n entry) (header : HeaderR c catalogue entry i x) :
    ∃ byte, x.mem[c.srcPA i]? = some byte := by
  obtain ⟨pa, mapped, _, _⟩ := source_mapped c i room
  obtain ⟨byte, initial⟩ := present i room
  have physical : c.srcPA i = pa.toNat := by simp only [Context.srcPA, mapped, Option.getD_some]
  simp only [readByte, mapped, Option.bind_some] at initial
  refine ⟨byte, ?_⟩
  change Aux.memoryView x (c.srcPA i) = some byte
  rw [header.bytes.unread i (Nat.le_refl _) room]
  simpa only [Aux.memoryView, physical] using initial

attribute [local instance 10] Classical.propDecidable in
/-- Empty memcpy over EnvR: CBZ taken, then RET; no data byte is touched. -/
theorem empty_r (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (zero : c.n = 0) (args : Args c.d c.s c.returnPC c.n entry) (env : EnvR c catalogue entry 0 entry) :
    ∃ fin, Uget.Chain.modelRun real (Schedule.copySteps c.n) entry = .ok () fin ∧
      CopyPost c.mapping c.d c.s c.returnPC c.n entry fin ∧ Covered real (PcOk c) (Schedule.copySteps c.n) entry ∧
      Route7Trace.Traced real c.spec c.mapping (recsOf c) (pcOf c) (Schedule.copySteps c.n) 0 entry := by
  obtain ⟨dest, _, counterArg, link⟩ := args
  change entry.regs.gpr[0] = c.d at dest
  change entry.regs.gpr[2].toNat = c.n at counterArg
  change entry.regs.gpr[30] = c.returnPC at link
  have cost : Schedule.copySteps c.n = 2 := by simp [zero, Schedule.copySteps]
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyCbz.W 2#5 8#19) entry := by
    exact fetch_index_r c catalogue entry 0 0 entry env (by decide) (by rw [env.core.v1.pc, offset_entry]; rfl)
  have regZero : entry.regs.gpr[(GPRSummary.key (2#5).toNat).val] = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    change entry.regs.gpr[2].toNat = 0
    omega
  have condition : Crypto.CruxCbz.cbzC 1#1 2#5 entry := (cbz_cond_iff entry).2 regZero
  have target : entry.regs._PC + sign_extend (8#19 ++ 0#2) 64 = c.base + 452#64 := by
    change entry.regs._PC + 32#64 = c.base + 452#64
    rw [env.core.v1.pc, offset_entry]
    bv_omega
  have low : (entry.regs._PC + sign_extend (8#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [target]
    have := c.low
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have placed0 : entry.regs._PC + sign_extend (8#19 ++ 0#2) 64 = c.base + offset c.base c.returnPC c.n (0 + 1) := by
    rw [target, offset_empty_ret c zero]
  obtain ⟨a, run0, core1, holds0, memory0, _, _, _, frame0, choice0, ev0⟩ :=
    Route7Steps.cbz64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget 0 catalogue (budget_positive c) c.page
      (by rw [offset_entry]; decide) 2#5 8#19 entry env.core nodup low _ (by rw [if_pos condition]) placed0 fetch0
  have env1 : EnvR c catalogue entry 1 a := advance_pre c catalogue entry 0 (by omega) entry a env core1 choice0
  have gpr0 := ValueFacts.nil_gpr entry a holds0
  have sp0 := ValueFacts.nil_sp entry a holds0
  have aLink : a.regs.gpr[30] = c.returnPC := by rw [gpr0]; exact link
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) a := by
    exact fetch_index_r c catalogue entry 1 8 a env1 (by decide) (by rw [env1.core.v1.pc, offset_empty_ret c zero]; rfl)
  obtain ⟨fin, run1, pc, holds1, memory1, _, _, _, frame1, _, ev1⟩ :=
    Route7Steps.retE real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget 1 catalogue (by rw [Context.budget, cost]; omega) c.page
      (by rw [offset_empty_ret c zero]; decide) 30#5 (by decide) a env1.core nodup
      (by change a.regs.gpr[30].toNat < 2 ^ 55; rw [aLink]; have := c.returnLow; omega) fetch1
  have memory : fin.mem = entry.mem := memory1.trans memory0
  have gpr : fin.regs.gpr = entry.regs.gpr := (ValueFacts.nil_gpr a fin holds1).trans gpr0
  have sp1 := ValueFacts.nil_sp a fin holds1
  have abi := frame0.trans frame1
  have runFin : Uget.Chain.modelRun real 2 entry = .ok () fin := by simp only [Uget.Chain.modelRun, run0, run1]
  have cov : Covered real (PcOk c) (Schedule.copySteps c.n) entry := by
    rw [cost]
    intro t ht
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with h | h | h <;> subst h
    · exact ⟨entry, rfl, pcOk_of_env c catalogue entry _ entry env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env c catalogue entry _ a env1⟩
    · exact ⟨fin, runFin, Or.inl (pc.trans aLink), CT1.Route7Word.imageWords_of_mem memory1 (pcOk_of_env c catalogue entry _ a env1).2⟩
  refine ⟨fin, ?_, ⟨pc.trans aLink, ?_, ?_, ?_, ?_, sp1.trans sp0,
    LoopNative.MemoryFrame.vector abi rfl, LoopNative.MemoryFrame.fpcr abi rfl, LoopNative.MemoryFrame.fpsr abi rfl⟩, cov, ?_⟩
  rotate_right
  · rw [cost]
    exact Route7Trace.traced_append real c.spec c.mapping (recsOf c) (pcOf c) 1 1 0 entry a (Route7Trace.run_one real entry a run0)
      (Route7Trace.traced_one real c.spec c.mapping (recsOf c) (pcOf c) 0 entry a run0
        (pcAt_of_env c catalogue entry _ entry env) (by rw [recs_pre c 0 (by omega)]; exact ev0) frame0)
      (Route7Trace.traced_one real c.spec c.mapping (recsOf c) (pcOf c) (0 + 1) a fin run1
        (pcAt_of_env c catalogue entry _ a env1) (by rw [recs_pre c (0 + 1) (by omega)]; exact ev1) frame1)
  · rw [cost]
    exact runFin
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

theorem finish_r (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (present : SourcePresent c.mapping c.s c.n entry) (i : Nat) (x : NativeState) (header : HeaderR c catalogue entry i x) :
    ∃ fin, Uget.Chain.modelRun real (6 * (c.n - i) + 1) x = .ok () fin ∧
      CopyPost c.mapping c.d c.s c.returnPC c.n entry fin ∧ Covered real (PcOk c) (6 * (c.n - i) + 1) x ∧
      Route7Trace.Traced real c.spec c.mapping (recsOf c) (pcOf c) (6 * (c.n - i) + 1) (2 + 6 * i) x := by
  suffices all : ∀ remaining i x, c.n - i = remaining → HeaderR c catalogue entry i x →
      ∃ fin, Uget.Chain.modelRun real (6 * remaining + 1) x = .ok () fin ∧
        CopyPost c.mapping c.d c.s c.returnPC c.n entry fin ∧ Covered real (PcOk c) (6 * remaining + 1) x ∧
        Route7Trace.Traced real c.spec c.mapping (recsOf c) (pcOf c) (6 * remaining + 1) (2 + 6 * i) x by
    exact all (c.n - i) i x rfl header
  intro remaining
  induction remaining using Nat.strongRecOn with
  | ind remaining ih =>
    intro i x rank header
    by_cases zero : remaining = 0
    · have last : i = c.n := by have bound := header.bound; omega
      subst i
      obtain ⟨fin, run, pcFin, memFin, post, tr1⟩ := exit_r real c catalogue nodup entry x header
      have cov1 : Covered real (PcOk c) 1 x :=
        covered_one real (PcOk c) x fin run (pcOk_of_env c catalogue entry _ x header.environment)
          ⟨Or.inl pcFin, CT1.Route7Word.imageWords_of_mem memFin (pcOk_of_env c catalogue entry _ x header.environment).2⟩
      subst zero
      exact ⟨fin, run, post, cov1, tr1⟩
    · have room : i < c.n := by have bound := header.bound; omega
      obtain ⟨byte, value⟩ := header_source_r c catalogue entry x i room present header
      obtain ⟨next, run, _, nextHeader, bodyCov, bodyTr⟩ := body_r real c catalogue nodup entry x i room byte header value
      have lower : c.n - (i + 1) < remaining := by omega
      obtain ⟨fin, rest, post, restCov, restTr⟩ := ih (c.n - (i + 1)) lower (i + 1) next rfl nextHeader
      have cost : 6 + (6 * (c.n - (i + 1)) + 1) = 6 * remaining + 1 := by omega
      refine ⟨fin, ?_, post, ?_, ?_⟩
      · rw [← cost]
        exact Aux.modelRun_append real 6 (6 * (c.n - (i + 1)) + 1) x next fin run rest
      · rw [← cost]
        exact covered_append real (PcOk c) 6 (6 * (c.n - (i + 1)) + 1) x next run bodyCov restCov
      · rw [← cost]
        have tr := Route7Trace.traced_append real c.spec c.mapping (recsOf c) (pcOf c) 6 (6 * (c.n - (i + 1)) + 1)
          (2 + 6 * i) x next run bodyTr (by rw [show 2 + 6 * i + 6 = 2 + 6 * (i + 1) by omega]; exact restTr)
        exact tr

/-- **Complete memcpy over the MTE2-general Runtime InvG** (route 7 unit 3): from EnvR at the actual entry (CurrentInv +
tag-status rows), the exact schedule length copySteps n runs successfully to CopyPost. -/
theorem run_r (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (args : Args c.d c.s c.returnPC c.n entry)
    (present : SourcePresent c.mapping c.s c.n entry) (env : EnvR c catalogue entry 0 entry) :
    ∃ fin, Uget.Chain.modelRun real (Schedule.copySteps c.n) entry = .ok () fin ∧
      CopyPost c.mapping c.d c.s c.returnPC c.n entry fin ∧ Covered real (PcOk c) (Schedule.copySteps c.n) entry ∧
      Route7Trace.Traced real c.spec c.mapping (recsOf c) (pcOf c) (Schedule.copySteps c.n) 0 entry := by
  by_cases zero : c.n = 0
  · exact empty_r real c catalogue nodup entry zero args env
  · have positive : 0 < c.n := by omega
    obtain ⟨header, firstRun, init, enterCov, enterTr⟩ := enter_r real c catalogue nodup entry positive args env
    obtain ⟨fin, restRun, post, restCov, restTr⟩ := finish_r real c catalogue nodup entry present 0 header init
    have cost : 2 + (6 * (c.n - 0) + 1) = Schedule.copySteps c.n := by
      simp only [Schedule.copySteps, if_neg zero, Nat.sub_zero]
      omega
    refine ⟨fin, ?_, post, ?_, ?_⟩
    · rw [← cost]
      exact Aux.modelRun_append real 2 (6 * (c.n - 0) + 1) entry header fin firstRun restRun
    · rw [← cost]
      exact covered_append real (PcOk c) 2 (6 * (c.n - 0) + 1) entry header firstRun enterCov restCov
    · rw [← cost]
      exact Route7Trace.traced_append real c.spec c.mapping (recsOf c) (pcOf c) 2 (6 * (c.n - 0) + 1) 0 entry header
        firstRun enterTr (by simpa only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] using restTr)

/-- **Fetched-PC coverage of the complete memcpy over EnvR** (route 7 unit 3, fetched_pc_evidence): every state of the
exact-length run, including the start, is at a reviewed memcpy word (0x1a4 + 4j, j < 9), or at returnPC after the
final RET. With `Route7Coverage.memcpy_closed` (every memcpy word's successors stay in the region), only reviewed words
are ever fetched. -/
theorem memcpy_fetch_covered (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (args : Args c.d c.s c.returnPC c.n entry)
    (present : SourcePresent c.mapping c.s c.n entry) (env : EnvR c catalogue entry 0 entry) :
    ∀ k, k ≤ Schedule.copySteps c.n → ∃ z, Uget.Chain.modelRun real k entry = .ok () z ∧ PcOk c z := by
  obtain ⟨_, _, _, cov, _⟩ := run_r real c catalogue nodup entry args present env
  exact cov

end Route7Copy
#print axioms Route7Copy.empty_r
#print axioms Route7Copy.finish_r
#print axioms Route7Copy.run_r
#print axioms Route7Copy.memcpy_fetch_covered
