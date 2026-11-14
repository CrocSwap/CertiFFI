-- Route 7 breadth: memset entry (CBZ, MOV), empty path (CBZ, RET), final RET, the iteration induction
-- and the complete memset run over EnvS (Runtime InvG), ported from loops SetRun the way ported CopyRun.
-- loops overlay: + fetched-PC coverage (Covered (PcOkS c)) on enter_s / empty_s / exit_s / finish_s / run_s.
import Route7Set.Body
import ArmCertLoop.SetRun
import Route7Copy.Entry
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option Elab.async false
namespace Route7Set
open ArmCertLoop ArmCertLoop.SetNative ArmCertLoop.ContractDraft

theorem setStep_pre (n k : Nat) (hk : k < 2) : setStep n k = false := by
  unfold setStep; simp; omega

/-- A zero-draw step at a pre-loop index (0 or 1) advances EnvS. -/
theorem advance_pre_s (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat) (hk : k < 2)
    (x fin : NativeState) (env : EnvS c catalogue entry k x)
    (core : ReleaseProfile.DefaultCurrent.CurrentInv c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
      (offset c) (Schedule.setSteps c.n) (k + 1) catalogue fin)
    (choice : NativeMteTagCheck.ChoiceDelta x fin 0) : EnvS c catalogue entry (k + 1) fin :=
  ReleaseProfile.DefaultRuntime.InvG.advance env core True.intro ⟨0, choice, Nat.le_refl 0⟩
    (by rw [setPast_succ, setStep_pre c.n k hk]; simp)

/-- CBZ X2 taken / not taken from the count (outside the classical-decidable scope). -/
theorem cbz_taken_of (x : NativeState) (h : x.regs.gpr[2].toNat = 0) : Crypto.CruxCbz.cbzC 1#1 2#5 x :=
  (Route7Copy.cbz_cond_iff x).2 (BitVec.eq_of_toNat_eq h)

theorem cbz_not_of (x : NativeState) (h : x.regs.gpr[2].toNat ≠ 0) : ¬ Crypto.CruxCbz.cbzC 1#1 2#5 x := by
  intro cond
  apply h
  have zero := congrArg BitVec.toNat ((Route7Copy.cbz_cond_iff x).1 cond)
  exact zero

attribute [local instance 10] Classical.propDecidable in
theorem enter_s (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (positive : 0 < c.n) (args : Args c entry) (env : EnvS c catalogue entry 0 entry) :
    ∃ x, Uget.Chain.modelRun real 2 entry = .ok () x ∧ HeaderS c catalogue entry 0 x ∧
      Route7Copy.Covered real (PcOkS c) 2 entry ∧ Route7Trace.Traced real c.spec c.mapping (recsOfS c) (pcOfS c) 2 0 entry := by
  obtain ⟨dest, source, counterArg, link⟩ := args
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyCbz.W 2#5 6#19) entry := by
    exact fetch_index_s c catalogue entry 0 9 entry env (by decide) (by rw [env.core.v1.pc, offset_entry]; rfl)
  have nonzero := cbz_not_of entry (by omega)
  have placed0 : entry.regs._PC + 4#64 = c.base + offset c 1 := by
    rw [env.core.v1.pc, offset_entry, offset_setup c positive]
    bv_omega
  have hlow : (entry.regs._PC + sign_extend (6#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [env.core.v1.pc, offset_entry]
    have low := c.low
    change (c.base + 456#64 + 24#64).toNat < 2 ^ 55
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  obtain ⟨a, run0, core1, holds0, memory0, _, _, _, frame0, choice0, ev0⟩ :=
    Route7Steps.cbz64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) 0 catalogue (cost_positive c) c.page
      (by rw [offset_entry]; decide) 2#5 6#19 entry env.core nodup hlow (entry.regs._PC + 4#64)
      (by rw [if_neg nonzero]) placed0 fetch0
  have env1 : EnvS c catalogue entry 1 a := advance_pre_s c catalogue entry 0 (by omega) entry a env core1 choice0
  have gpr0 := ValueFacts.nil_gpr entry a holds0
  have sp0 := ValueFacts.nil_sp entry a holds0
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.OrrMov64.selected 3#5 0#6 0#5) a := by
    exact fetch_index_s c catalogue entry 1 10 a env1 (by decide) (by rw [env1.core.v1.pc, offset_setup c positive]; rfl)
  have placed1 : a.regs._PC + 4#64 = c.base + offset c 2 := by
    rw [env1.core.v1.pc, offset_setup c positive]
    have index : (2 : Nat) = 2 + 4 * 0 + 0 := by omega
    rw [index, offset_body c 0 0 positive (by decide)]
    change c.base + 460#64 + 4#64 = c.base + 464#64
    bv_omega
  have nz : c.n ≠ 0 := by omega
  obtain ⟨x, run1, core2, holds1, memory1, _, _, _, frame1, choice1, ev1⟩ :=
    Route7Steps.mov64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) 1 catalogue
      (by simp only [Schedule.setSteps, if_neg nz]; omega) c.page
      (by rw [offset_setup c positive]; decide) 3#5 0#5 (by decide) (by decide) a env1.core nodup placed1 fetch1
  have env2 : EnvS c catalogue entry 2 x := advance_pre_s c catalogue entry 1 (by omega) a x env1 core2 choice1
  obtain ⟨gpr1, sp1⟩ := ValueFacts.mov 3#5 0#5 a x holds1
  change x.regs.gpr = a.regs.gpr.set 3 a.regs.gpr[0] at gpr1
  have gpr : x.regs.gpr = entry.regs.gpr.set 3 c.d := by rw [gpr1, gpr0, dest]
  have memory : x.mem = entry.mem := memory1.trans memory0
  have bytes : Bytes.FillPrefix c.dstPA (Aux.memoryView entry) (Aux.memoryView x) (c.fill.setWidth 8) c.n 0 := by
    have view : Aux.memoryView x = Aux.memoryView entry := by unfold Aux.memoryView; rw [memory]
    rw [view]
    exact Bytes.fillPrefix_zero c.dstPA (Aux.memoryView entry) (c.fill.setWidth 8) c.n
  refine ⟨x, by simp only [Uget.Chain.modelRun, run0, run1], ⟨positive, by omega, by simpa using env2, ?_, ?_, ?_, ?_, ?_, ?_,
    sp1.trans sp0, frame0.trans frame1, bytes⟩, ?_, ?_⟩
  · rw [gpr]; simpa using dest
  · rw [gpr]; simpa using source
  · rw [gpr]; simp
  · rw [gpr]; simpa using counterArg
  · rw [gpr]; simpa using link
  · intro r saved
    have different : 3 ≠ r.val := by omega
    rw [gpr]
    simp [Vector.getElem_set, different]
  · intro m hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with h | h | h <;> subst h
    · exact ⟨entry, rfl, pcOk_of_env_s c catalogue entry _ entry env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env_s c catalogue entry _ a env1⟩
    · exact ⟨x, by simp only [Uget.Chain.modelRun, run0, run1], pcOk_of_env_s c catalogue entry _ x env2⟩
  · -- trace (loops CT0): CBZ, MOV carry no data records
    exact Route7Trace.traced_append real c.spec c.mapping (recsOfS c) (pcOfS c) 1 1 0 entry a (Route7Trace.run_one real entry a run0)
      (Route7Trace.traced_one real c.spec c.mapping (recsOfS c) (pcOfS c) 0 entry a run0 (pcAt_of_env_s c catalogue entry _ entry env) (by rw [recs_pre_s c 0 (by omega)]; exact ev0) frame0)
      (Route7Trace.traced_one real c.spec c.mapping (recsOfS c) (pcOfS c) (0 + 1) a x run1 (pcAt_of_env_s c catalogue entry _ a env1) (by rw [recs_pre_s c (0 + 1) (by omega)]; exact ev1) frame1)

attribute [local instance 10] Classical.propDecidable in
/-- Empty memset over EnvS: CBZ taken, then RET; no data byte is touched (the destination may be unmapped). -/
theorem empty_s (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (zero : c.n = 0) (args : Args c entry) (env : EnvS c catalogue entry 0 entry) :
    ∃ fin, Uget.Chain.modelRun real (Schedule.setSteps c.n) entry = .ok () fin ∧ Post c entry fin ∧
      Route7Copy.Covered real (PcOkS c) (Schedule.setSteps c.n) entry ∧ Route7Trace.Traced real c.spec c.mapping (recsOfS c) (pcOfS c) (Schedule.setSteps c.n) 0 entry := by
  obtain ⟨dest, _, counterArg, link⟩ := args
  have cost : Schedule.setSteps c.n = 2 := by simp [zero, Schedule.setSteps]
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyCbz.W 2#5 6#19) entry := by
    exact fetch_index_s c catalogue entry 0 9 entry env (by decide) (by rw [env.core.v1.pc, offset_entry]; rfl)
  have condition := cbz_taken_of entry (by omega)
  have target : entry.regs._PC + sign_extend (6#19 ++ 0#2) 64 = c.base + 480#64 := by
    change entry.regs._PC + 24#64 = c.base + 480#64
    rw [env.core.v1.pc, offset_entry]
    bv_omega
  have low : (entry.regs._PC + sign_extend (6#19 ++ 0#2) 64).toNat < 2 ^ 55 := by
    rw [target]
    have := c.low
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have placed0 : entry.regs._PC + sign_extend (6#19 ++ 0#2) 64 = c.base + offset c (0 + 1) := by
    rw [target, offset_empty_ret c zero]
  obtain ⟨a, run0, core1, holds0, memory0, _, _, _, frame0, choice0, ev0⟩ :=
    Route7Steps.cbz64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) 0 catalogue (cost_positive c) c.page
      (by rw [offset_entry]; decide) 2#5 6#19 entry env.core nodup low _ (by rw [if_pos condition]) placed0 fetch0
  have env1 : EnvS c catalogue entry 1 a := advance_pre_s c catalogue entry 0 (by omega) entry a env core1 choice0
  have gpr0 := ValueFacts.nil_gpr entry a holds0
  have sp0 := ValueFacts.nil_sp entry a holds0
  have aLink : a.regs.gpr[30] = c.returnPC := by rw [gpr0]; exact link
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) a := by
    exact fetch_index_s c catalogue entry 1 15 a env1 (by decide) (by rw [env1.core.v1.pc, offset_empty_ret c zero]; rfl)
  obtain ⟨fin, run1, pc, holds1, memory1, _, _, _, frame1, _, ev1⟩ :=
    Route7Steps.retE real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) 1 catalogue (by rw [cost]; omega) c.page
      (by rw [offset_empty_ret c zero]; decide) 30#5 (by decide) a env1.core nodup
      (by change a.regs.gpr[30].toNat < 2 ^ 55; rw [aLink]; have := c.returnLow; omega) fetch1
  have memory : fin.mem = entry.mem := memory1.trans memory0
  have gpr : fin.regs.gpr = entry.regs.gpr := (ValueFacts.nil_gpr a fin holds1).trans gpr0
  have sp1 := ValueFacts.nil_sp a fin holds1
  have abi := frame0.trans frame1
  have runFin : Uget.Chain.modelRun real 2 entry = .ok () fin := by simp only [Uget.Chain.modelRun, run0, run1]
  refine ⟨fin, ?_, ⟨pc.trans aLink, ?_, ?_, ?_, ?_, sp1.trans sp0,
    LoopNative.MemoryFrame.vector abi rfl, LoopNative.MemoryFrame.fpcr abi rfl, LoopNative.MemoryFrame.fpsr abi rfl⟩, ?_, ?_⟩
  · rw [cost]
    exact runFin
  · rw [gpr]; exact dest
  · intro i impossible
    omega
  · intro pa _
    rw [memory]
  · intro r _
    rw [gpr]
  · rw [cost]
    intro m hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with h | h | h <;> subst h
    · exact ⟨entry, rfl, pcOk_of_env_s c catalogue entry _ entry env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env_s c catalogue entry _ a env1⟩
    · exact ⟨fin, runFin, Or.inl (pc.trans aLink), CT1.Route7Word.imageWords_of_mem memory1 (pcOk_of_env_s c catalogue entry _ a env1).2⟩
  · -- trace (loops CT0): CBZ, RET carry no data records
    rw [cost]
    exact Route7Trace.traced_append real c.spec c.mapping (recsOfS c) (pcOfS c) 1 1 0 entry a (Route7Trace.run_one real entry a run0)
      (Route7Trace.traced_one real c.spec c.mapping (recsOfS c) (pcOfS c) 0 entry a run0 (pcAt_of_env_s c catalogue entry _ entry env) (by rw [recs_pre_s c 0 (by omega)]; exact ev0) frame0)
      (Route7Trace.traced_one real c.spec c.mapping (recsOfS c) (pcOfS c) (0 + 1) a fin run1 (pcAt_of_env_s c catalogue entry _ a env1) (by rw [recs_pre_s c (0 + 1) (by omega)]; exact ev1) frame1)

/-- Final RET over EnvS: return to returnPC with the complete memset functional/ABI postcondition. -/
theorem exit_s (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry x : NativeState)
    (header : HeaderS c catalogue entry c.n x) :
    ∃ y, Uget.Chain.modelRun real 1 x = .ok () y ∧ y.mem = x.mem ∧ Post c entry y ∧
      Route7Copy.Covered real (PcOkS c) 1 x ∧ Route7Trace.Traced real c.spec c.mapping (recsOfS c) (pcOfS c) 1 (2 + 4 * c.n) x := by
  have nz : c.n ≠ 0 := by have := header.positive; omega
  have fetch : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) x := by
    exact fetch_index_s c catalogue entry (2 + 4 * c.n) 15 x header.environment (by decide) (by
      rw [header.environment.core.v1.pc, offset_exit c header.positive]
      rfl)
  obtain ⟨y, run, pc, holds, memory, _, _, _, kept, _, ev⟩ :=
    Route7Steps.retE real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) (2 + 4 * c.n) catalogue
      (by simp only [Schedule.setSteps, if_neg nz]; omega) c.page
      (by rw [offset_exit c header.positive]; decide) 30#5 (by decide) x header.environment.core nodup
      (by change x.regs.gpr[30].toNat < 2 ^ 55; rw [header.link]; have := c.returnLow; omega) fetch
  have gpr := ValueFacts.nil_gpr x y holds
  have sp := ValueFacts.nil_sp x y holds
  have abi := header.protectedRegs.trans kept
  have runY : Uget.Chain.modelRun real 1 x = .ok () y := by simp only [Uget.Chain.modelRun, run]
  refine ⟨y, runY, memory, ⟨pc.trans header.link, ?_, ?_, ?_, ?_,
    sp.trans header.sp, LoopNative.MemoryFrame.vector abi rfl,
    LoopNative.MemoryFrame.fpcr abi rfl, LoopNative.MemoryFrame.fpsr abi rfl⟩,
    Route7Copy.covered_one real (PcOkS c) x y runY (pcOk_of_env_s c catalogue entry _ x header.environment)
      ⟨Or.inl (pc.trans header.link), CT1.Route7Word.imageWords_of_mem memory (pcOk_of_env_s c catalogue entry _ x header.environment).2⟩,
    Route7Trace.traced_one real c.spec c.mapping (recsOfS c) (pcOfS c) _ x y run (pcAt_of_env_s c catalogue entry _ x header.environment) (by rw [recs_exit_s]; exact ev) kept⟩
  · rw [gpr]; exact header.dest
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
    rw [gpr]
    exact header.saved r saved

theorem finish_s (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (i : Nat) (x : NativeState) (header : HeaderS c catalogue entry i x) :
    ∃ fin, Uget.Chain.modelRun real (4 * (c.n - i) + 1) x = .ok () fin ∧ Post c entry fin ∧
      Route7Copy.Covered real (PcOkS c) (4 * (c.n - i) + 1) x ∧ Route7Trace.Traced real c.spec c.mapping (recsOfS c) (pcOfS c) (4 * (c.n - i) + 1) (2 + 4 * i) x := by
  suffices all : ∀ remaining i x, c.n - i = remaining → HeaderS c catalogue entry i x →
      ∃ fin, Uget.Chain.modelRun real (4 * remaining + 1) x = .ok () fin ∧ Post c entry fin ∧
        Route7Copy.Covered real (PcOkS c) (4 * remaining + 1) x ∧ Route7Trace.Traced real c.spec c.mapping (recsOfS c) (pcOfS c) (4 * remaining + 1) (2 + 4 * i) x by
    exact all (c.n - i) i x rfl header
  intro remaining
  induction remaining using Nat.strongRecOn with
  | ind remaining ih =>
    intro i x rank header
    by_cases zero : remaining = 0
    · have last : i = c.n := by have bound := header.bound; omega
      subst i
      obtain ⟨fin, run, _, post, cov, tr1⟩ := exit_s real c catalogue nodup entry x header
      subst zero
      exact ⟨fin, run, post, cov, tr1⟩
    · have room : i < c.n := by have bound := header.bound; omega
      obtain ⟨next, run, _, nextHeader, bodyCov, bodyTr⟩ := body_s real c catalogue nodup entry x i room header
      have lower : c.n - (i + 1) < remaining := by omega
      obtain ⟨fin, rest, post, restCov, restTr⟩ := ih (c.n - (i + 1)) lower (i + 1) next rfl nextHeader
      have cost : 4 + (4 * (c.n - (i + 1)) + 1) = 4 * remaining + 1 := by omega
      refine ⟨fin, ?_, post, ?_, ?_⟩
      · rw [← cost]
        exact Aux.modelRun_append real 4 (4 * (c.n - (i + 1)) + 1) x next fin run rest
      · rw [← cost]
        exact Route7Copy.covered_append real (PcOkS c) 4 (4 * (c.n - (i + 1)) + 1) x next run bodyCov restCov
      · rw [← cost]
        exact Route7Trace.traced_append real c.spec c.mapping (recsOfS c) (pcOfS c) 4 (4 * (c.n - (i + 1)) + 1) (2 + 4 * i) x next run bodyTr
          (by rw [show 2 + 4 * i + 4 = 2 + 4 * (i + 1) by omega]; exact restTr)

/-- **Complete memset over the MTE2-general Runtime InvG** (route 7 breadth): from EnvS at the actual entry
(CurrentInv + tag-status rows, capacity n), the exact schedule setSteps n runs successfully to loops' memset Post. -/
theorem run_s (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry : NativeState)
    (args : Args c entry) (env : EnvS c catalogue entry 0 entry) :
    ∃ fin, Uget.Chain.modelRun real (Schedule.setSteps c.n) entry = .ok () fin ∧ Post c entry fin ∧
      Route7Copy.Covered real (PcOkS c) (Schedule.setSteps c.n) entry ∧ Route7Trace.Traced real c.spec c.mapping (recsOfS c) (pcOfS c) (Schedule.setSteps c.n) 0 entry := by
  by_cases zero : c.n = 0
  · exact empty_s real c catalogue nodup entry zero args env
  · have positive : 0 < c.n := by omega
    obtain ⟨header, firstRun, init, enterCov, enterTr⟩ := enter_s real c catalogue nodup entry positive args env
    obtain ⟨fin, restRun, post, restCov, restTr⟩ := finish_s real c catalogue nodup entry 0 header init
    have cost : 2 + (4 * (c.n - 0) + 1) = Schedule.setSteps c.n := by
      simp only [Schedule.setSteps, if_neg zero, Nat.sub_zero]
      omega
    refine ⟨fin, ?_, post, ?_, ?_⟩
    · rw [← cost]
      exact Aux.modelRun_append real 2 (4 * (c.n - 0) + 1) entry header fin firstRun restRun
    · rw [← cost]
      exact Route7Copy.covered_append real (PcOkS c) 2 (4 * (c.n - 0) + 1) entry header firstRun enterCov restCov
    · rw [← cost]
      exact Route7Trace.traced_append real c.spec c.mapping (recsOfS c) (pcOfS c) 2 (4 * (c.n - 0) + 1) 0 entry header firstRun enterTr
        (by simpa only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] using restTr)

end Route7Set
#print axioms Route7Set.enter_s
#print axioms Route7Set.empty_s
#print axioms Route7Set.exit_s
#print axioms Route7Set.finish_s
#print axioms Route7Set.run_s
