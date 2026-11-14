-- Route 7 breadth: one memset iteration (STRB, ADD x3, SUB x2, CBNZ) over EnvS, ported from loops
-- SetBody (body / branch_step) the way ported CopyBody/CopyRest to Route7Copy.
import Route7Set.Context
import Route7Set.Cover
import Route7Trace.Set
import Route7StepsE.Class
import Route7StepsE.Branch
import Route7Copy.Body
import ArmCertLoop.SetBody
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

/-- loops SetNative.Header with the environment over EnvS (entry = run entry = tag-status oracle entry). -/
structure HeaderS (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (i : Nat) (x : NativeState) : Prop where
  positive : 0 < c.n
  bound : i ≤ c.n
  environment : EnvS c catalogue entry (2 + 4 * i) x
  dest : x.regs.gpr[0] = c.d
  fill : x.regs.gpr[1] = c.fill
  cursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i
  remaining : x.regs.gpr[2].toNat = c.n - i
  link : x.regs.gpr[30] = c.returnPC
  saved : ∀ r : Fin 31, 4 ≤ r.val → x.regs.gpr[r.val] = entry.regs.gpr[r.val]
  sp : x.regs.SP_EL0 = entry.regs.SP_EL0
  protectedRegs : NativeEntry.Effects.Frame {} entry.regs x.regs
  bytes : Bytes.FillPrefix c.dstPA (Aux.memoryView entry) (Aux.memoryView x) (c.fill.setWidth 8) c.n i

/-- CBNZ X2 taken / not taken, from the remaining count (outside the classical-decidable scope). -/
theorem cbnz_taken_of (x : NativeState) (h : x.regs.gpr[2].toNat ≠ 0) :
    ReleaseProfile.HeapCbzAction.cbzCond x 1#1 1#1 2#5 := by
  apply (Route7Copy.cbnz_cond_iff x).2
  intro same
  apply h
  have zero := congrArg BitVec.toNat same
  exact zero

theorem cbnz_not_of (x : NativeState) (h : x.regs.gpr[2].toNat = 0) :
    ¬ ReleaseProfile.HeapCbzAction.cbzCond x 1#1 1#1 2#5 := by
  intro cond
  apply (Route7Copy.cbnz_cond_iff x).1 cond
  exact BitVec.eq_of_toNat_eq h

attribute [local instance 10] Classical.propDecidable in
theorem branch_step_s (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState) (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (i : Nat) (room : i < c.n)
    (x : NativeState) (env : EnvS c catalogue entry (2 + 4 * i + 3) x)
    (remaining : x.regs.gpr[2].toNat = c.n - (i + 1)) :
    ∃ y, modelStep real x = .ok () y ∧ EnvS c catalogue entry (2 + 4 * (i + 1)) y ∧ y.mem = x.mem ∧
      y.regs.gpr = x.regs.gpr ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧ NativeEntry.Effects.Frame {} x.regs y.regs ∧
      StepEvents.EvShape c.spec c.mapping [] x y := by
  have branchPC := pc_body_s c catalogue entry i 3 room (by decide) x env
  have fetch : FetchObligations c.spec c.config c.rows c.mapping (Route7Cbnz.Tail.W 2#5 backImmediate) x :=
    fetch_index_s c catalogue entry (2 + 4 * i + 3) 14 x env (by decide) branchPC
  have target : LoopNative.Cbnz64.target backImmediate x = c.base + 464#64 := by
    rw [LoopNative.Cbnz64.target, back_delta, branchPC]
    change c.base + 476#64 + BitVec.ofInt 64 (-12) = c.base + 464#64
    bv_omega
  have low : (LoopNative.Cbnz64.target backImmediate x).toNat < 2 ^ 55 := by
    rw [target]; have := c.low; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have index : 2 + 4 * i + 3 + 1 = 2 + 4 * (i + 1) := by omega
  have placed : (if ReleaseProfile.HeapCbzAction.cbzCond x 1#1 1#1 2#5
      then x.regs._PC + sign_extend (backImmediate ++ 0#2) 64 else x.regs._PC + 4#64) =
      c.base + offset c (2 + 4 * i + 3 + 1) := by
    by_cases again : i + 1 < c.n
    · rw [if_pos (cbnz_taken_of x (by omega))]
      change LoopNative.Cbnz64.target backImmediate x = _
      rw [target, index]
      exact congrArg (c.base + ·) (offset_body c (i + 1) 0 again (by decide)).symm
    · rw [if_neg (cbnz_not_of x (by omega))]
      have last : i + 1 = c.n := by omega
      rw [branchPC, index, last, offset_exit c (by omega)]
      change c.base + 476#64 + 4#64 = c.base + 480#64
      bv_omega
  obtain ⟨y, run, inv', holds, memory, _, _, _, kept, choice, ev⟩ :=
    Route7Steps.cbnz64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) (2 + 4 * i + 3) catalogue
      (body_room c i 3 room (by decide)) c.page (body_aligned c i 3 room (by decide))
      2#5 backImmediate x env.core nodup low _ rfl placed fetch
  have env' : EnvS c catalogue entry (2 + 4 * i + 3 + 1) y :=
    advance0_s c catalogue entry i 3 room (by decide) (by decide) x y env inv' choice
  rw [index] at env'
  exact ⟨y, run, env', memory, ValueFacts.nil_gpr x y holds, ValueFacts.nil_sp x y holds, kept, ev⟩

/-- One four-instruction fill iteration over EnvS (the STRB draws one tag status). -/
theorem body_s (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry x : NativeState)
    (i : Nat) (room : i < c.n) (header : HeaderS c catalogue entry i x) :
    ∃ y, Uget.Chain.modelRun real 4 x = .ok () y ∧
      Bytes.SingleWrite (Aux.memoryView x) (Aux.memoryView y) (c.dstPA i) (c.fill.setWidth 8) ∧
      HeaderS c catalogue entry (i + 1) y ∧ Route7Copy.Covered real (PcOkS c) 4 x ∧
      Route7Trace.Traced real c.spec c.mapping (recsOfS c) (pcOfS c) 4 (2 + 4 * i) x := by
  let k := 2 + 4 * i
  have env : EnvS c catalogue entry k x := header.environment
  have env0 : EnvS c catalogue entry (2 + 4 * i + 0) x := header.environment
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.StrbUoff.selected 1#5 3#5 0#12) x :=
    fetch_index_s c catalogue entry k 11 x env (by decide)
      (pc_body_s c catalogue entry i 0 room (by decide) x env0)
  have codeD : ImageTableSeparated codeScope c.base c.mapping (DestinationPA c.mapping c.d c.n) :=
    fun off pa inside mapped => c.codeWrite off inside pa mapped
  have past0 : setPast c.n k = i := setPast_body c.n i (by omega)
  have allowed0 := ReleaseProfile.DefaultRuntime.current_status env (by rw [past0]; exact room)
  obtain ⟨a, run0, ms0, frame0⟩ :=
    Route7Mem.DefaultStrbU.routeF real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) k catalogue
      (by simpa only [Nat.add_zero] using body_room c i 0 room (by decide)) c.page
      (by simpa only [Nat.add_zero] using body_aligned c i 0 room (by decide))
      (NativeEntryBodyDispatch.StrbUoff.selected 1#5 3#5 0#12) 651 (by decide) 0#12 3#5 1#5 (by decide) (by decide)
      (fun pc t see => NativeEntryBodyDispatch.StrbUoff.dispatch_at real pc 1#5 3#5 0#12 t (by simpa using see))
      (LoopNative.Encoding.StrbU_noEret 1#5 3#5 0#12) (DestinationPA c.mapping c.d c.n) codeD x env.core allowed0
      (store_facts c i room x header.cursor)
      (by simpa only [Nat.add_zero] using body_next_placed_s c catalogue entry i 0 room (by decide) x env0)
      fetch0 nodup
  have env1 : EnvS c catalogue entry (2 + 4 * i + 1) a :=
    ReleaseProfile.DefaultRuntime.InvG.advance env ms0.current True.intro ms0.choice
      (by rw [setPast_succ, setStep_store c.n i room]; simp)
  obtain ⟨pa, mapped, write, gpr0, sp0⟩ := NativeBytes.store_payload c.mapping 0#12 3#5 1#5 x a ms0.pay
  have addr : MemClass.StrbU.addr x 3#5 0#12 = c.d + BitVec.ofNat 64 i := by
    rw [CopyNative.store_addr_zero]; exact header.cursor
  have physical : c.dstPA i = pa.toNat := by simp only [Context.dstPA, ← addr, mapped, Option.getD_some]
  change Bytes.SingleWrite (Aux.memoryView x) (Aux.memoryView a) pa.toNat (x.regs.gpr[1].setWidth 8) at write
  rw [← physical, header.fill] at write
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.AddImm64.selected 3#5 3#5 1#12) a :=
    fetch_index_s c catalogue entry (k + 1) 12 a env1 (by decide) (pc_body_s c catalogue entry i 1 room (by decide) a env1)
  obtain ⟨b, run1, core2, values1, mem1, _, _, _, frame1, choice1, ev1⟩ :=
    Route7Steps.addImm64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) (k + 1) catalogue
      (body_room c i 1 room (by decide)) c.page (body_aligned c i 1 room (by decide))
      3#5 3#5 1#12 (by decide) (by decide) a env1.core nodup
      (body_next_placed_s c catalogue entry i 1 room (by decide) a env1) fetch1
  have env2 : EnvS c catalogue entry (2 + 4 * i + 2) b :=
    advance0_s c catalogue entry i 1 room (by decide) (by decide) a b env1 core2 choice1
  obtain ⟨gpr1, sp1⟩ := ValueFacts.add 3#5 3#5 1#12 a b values1
  change b.regs.gpr = a.regs.gpr.set 3 (a.regs.gpr[3] + 1#64) at gpr1
  have fetch2 : FetchObligations c.spec c.config c.rows c.mapping
      (Route7Sub.Dispatch.selected 2#5 2#5 1#12) b :=
    fetch_index_s c catalogue entry (k + 2) 13 b env2 (by decide) (pc_body_s c catalogue entry i 2 room (by decide) b env2)
  obtain ⟨t, run2, core3, values2, mem2, _, _, _, frame2, choice2, ev2⟩ :=
    Route7Steps.subImm64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) (k + 2) catalogue
      (body_room c i 2 room (by decide)) c.page (body_aligned c i 2 room (by decide))
      2#5 2#5 1#12 (by decide) (by decide) b env2.core nodup
      (body_next_placed_s c catalogue entry i 2 room (by decide) b env2) fetch2
  have env3 : EnvS c catalogue entry (2 + 4 * i + 3) t :=
    advance0_s c catalogue entry i 2 room (by decide) (by decide) b t env2 core3 choice2
  obtain ⟨gpr2, sp2⟩ := ValueFacts.sub 2#5 2#5 1#12 b t values2
  change t.regs.gpr = b.regs.gpr.set 2 (b.regs.gpr[2] - 1#64) at gpr2
  have counterB : b.regs.gpr[2] = x.regs.gpr[2] := by rw [gpr1, gpr0]; simp
  have counterT : t.regs.gpr[2] = x.regs.gpr[2] - 1#64 := by rw [gpr2, Vector.getElem_set_self, counterB]
  have counterPositive : 0 < x.regs.gpr[2].toNat := by have := header.remaining; omega
  have remaining : t.regs.gpr[2].toNat = c.n - (i + 1) := by
    rw [counterT, Schedule.counter_pred _ counterPositive, header.remaining]; omega
  obtain ⟨y, run3, env4, mem3, gpr3, sp3, frame3, ev3⟩ := branch_step_s real c catalogue entry nodup i room t env3 remaining
  have written := NativeBytes.write_after_memory_frames
    (before := x) (load := x) (store := a) (after := y) rfl write (mem3.trans (mem2.trans mem1))
  have filled := Bytes.fillPrefix_succ header.bytes room written
    (fun j prior => dest_distinct c i j room (by omega) (by omega))
  have advance : c.d + BitVec.ofNat 64 i + 1#64 = c.d + BitVec.ofNat 64 (i + 1) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  have gpr : y.regs.gpr = (x.regs.gpr.set 3 (c.d + BitVec.ofNat 64 (i + 1))).set 2 (x.regs.gpr[2] - 1#64) := by
    rw [gpr3, gpr2, counterB, gpr1, gpr0, header.cursor, advance]
  refine ⟨y, ?_, written, ⟨header.positive, by omega, env4, ?_, ?_, ?_, ?_, ?_, ?_,
    sp3.trans (sp2.trans (sp1.trans (sp0.trans header.sp))),
    (((header.protectedRegs.trans frame0).trans frame1).trans frame2).trans frame3, filled⟩, ?_, ?_⟩
  · simp only [Uget.Chain.modelRun, run0, run1, run2, run3]
  · rw [gpr]; simpa using header.dest
  · rw [gpr]; simpa using header.fill
  · rw [gpr]; simp
  · rw [gpr3]; exact remaining
  · rw [gpr]; simpa using header.link
  · intro r saved
    have n2 : 2 ≠ r.val := by omega
    have n3 : 3 ≠ r.val := by omega
    rw [gpr]
    simpa [Vector.getElem_set, n2, n3] using header.saved r saved
  · -- coverage (loops): every state of the iteration carries EnvS
    intro m hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with h | h | h | h | h <;> subst h
    · exact ⟨x, rfl, pcOk_of_env_s c catalogue entry _ x env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env_s c catalogue entry _ a env1⟩
    · exact ⟨b, by simp only [Uget.Chain.modelRun, run0, run1], pcOk_of_env_s c catalogue entry _ b env2⟩
    · exact ⟨t, by simp only [Uget.Chain.modelRun, run0, run1, run2], pcOk_of_env_s c catalogue entry _ t env3⟩
    · exact ⟨y, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3], pcOk_of_env_s c catalogue entry _ y env4⟩
  · -- trace (loops CT0): STRB records d + i; ADD / SUB / CBNZ carry none
    intro m hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with h | h | h | h <;> subst h
    · refine ⟨x, a, rfl, run0, ?_, ?_⟩
      · exact pcAt_of_env_s c catalogue entry _ x env
      · have ev0 := ms0.events
        rw [addr, ← recs_strb_s c i room] at ev0
        exact ⟨by simpa using ev0, frame0⟩
    · refine ⟨a, b, by simp only [Uget.Chain.modelRun, run0], run1, ?_, ?_⟩
      · exact pcAt_of_env_s c catalogue entry _ a env1
      · rw [recs_body_s c i 1 (by omega) (by omega)]; exact ⟨ev1, frame1⟩
    · refine ⟨b, t, by simp only [Uget.Chain.modelRun, run0, run1], run2, ?_, ?_⟩
      · exact pcAt_of_env_s c catalogue entry _ b env2
      · rw [recs_body_s c i 2 (by omega) (by omega)]; exact ⟨ev2, frame2⟩
    · refine ⟨t, y, by simp only [Uget.Chain.modelRun, run0, run1, run2], run3, ?_, ?_⟩
      · exact pcAt_of_env_s c catalogue entry _ t env3
      · rw [recs_body_s c i 3 (by omega) (by omega)]; exact ⟨ev3, frame3⟩

end Route7Set
#print axioms Route7Set.branch_step_s
#print axioms Route7Set.body_s
