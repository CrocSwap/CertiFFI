-- Route 7 breadth: memmove BACKWARD path (s <u d) loop over EnvM. Iteration t (t < n) runs at
-- k = 6 + 6t over words 508..528 (SUB x3; SUB x4; LDRB w5,[x4]; STRB w5,[x3]; SUB x2; CBNZ x2) and copies byte
-- n-1-t. The byte invariant is loops' CopyPrefix over the REVERSED index maps, and `backward_future` is the
-- overlap side condition of copyPrefix_succ.
import CT2Route7.MoveFwd
import Route7Move.Bwd
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option Elab.async false

namespace Route7Move.CT2
open ArmCertLoop ArmCertLoop.ContractDraft

/-- Reversed index maps: iteration t copies byte n-1-t. -/

theorem cursor_pred (a : BitVec 64) (m : Nat) (h : 0 < m) :
    a + BitVec.ofNat 64 m - 1#64 = a + BitVec.ofNat 64 (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

/-! ## Backward geometry -/

section geometry
variable (c : Context) (bwd : c.path = .backward)
include bwd

theorem bwd_budget : c.budget = 6 * c.n + 7 := by simp only [Context.budget, bwd, Schedule.moveSteps]

theorem bwd_body_room (t j : Nat) (room : t < c.n) (slot : j < 6) : 6 + 6 * t + j < c.budget := by
  rw [bwd_budget c bwd]; omega

theorem bwd_offset_body (t j : Nat) (room : t < c.n) (slot : j < 6) :
    offset c (6 + 6 * t + j) = BitVec.ofNat 64 (Generated.armcert_memmove_entry + 24 + 4 * j) := by
  have index : 6 + 6 * t + j ≠ c.budget := by have := bwd_body_room c bwd t j room slot; omega
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg index, bwd, backward_loop_offset c.n t j room slot, Nat.add_assoc]

theorem bwd_body_aligned (t j : Nat) (room : t < c.n) (slot : j < 6) :
    (offset c (6 + 6 * t + j)).toNat % 4 = 0 := by
  rw [bwd_offset_body c bwd t j room slot]
  have bound : Generated.armcert_memmove_entry + 24 + 4 * j < 2 ^ 64 := by
    simp only [Generated.armcert_memmove_entry]; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Generated.armcert_memmove_entry]
  omega

theorem bwd_offset_after (t : Nat) (room : t < c.n) :
    offset c (6 + 6 * t + 5 + 1) =
      BitVec.ofNat 64 (Generated.armcert_memmove_entry + (if t + 1 < c.n then 24 else 48)) := by
  have index : 6 + 6 * t + 5 + 1 ≠ c.budget := by rw [bwd_budget c bwd]; omega
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg index, bwd]
  simp only [Schedule.moveWordOffset]
  rw [if_neg (by omega)]
  by_cases again : t + 1 < c.n
  · rw [if_pos (by omega), if_pos again]
    congr 2
    omega
  · rw [if_neg (by omega), if_neg again]

theorem bwd_offset_exit : offset c (6 + 6 * c.n) = BitVec.ofNat 64 (Generated.armcert_memmove_entry + 48) := by
  have index : 6 + 6 * c.n ≠ c.budget := by rw [bwd_budget c bwd]; omega
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg index, bwd]
  simp only [Schedule.moveWordOffset]
  rw [if_neg (by omega), if_neg (by omega)]

end geometry

theorem bwd_memStep_body (n t j : Nat) (ht : t < n) (hj : j < 6) :
    memStep .backward n (6 + 6 * t + j) = decide (2 ≤ j ∧ j < 4) := by
  unfold memStep
  have h1 : (6 + 6 * t + j - 6) % 6 = j := by omega
  have h2 : (6 + 6 * t + j - 6) / 6 = t := by omega
  rw [h1, h2]
  by_cases h : 2 ≤ j ∧ j < 4
  · simp [h, ht]; (try omega)
  · simp only [h, decide_false]
    simp only [decide_eq_false_iff_not]
    omega

theorem bwd_movePast_step (n t j : Nat) (ht : t < n) (hj : j < 6) :
    movePast .backward n (6 + 6 * t + j + 1) =
      movePast .backward n (6 + 6 * t + j) + (if 2 ≤ j ∧ j < 4 then 1 else 0) := by
  rw [movePast_succ, bwd_memStep_body n t j ht hj]
  by_cases h : 2 ≤ j ∧ j < 4 <;> simp [h]

theorem bwd_movePast_pre (n k : Nat) (hk : k ≤ 6) : movePast .backward n k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [movePast_succ, ih (by omega)]
    have : memStep .backward n k = false := by unfold memStep; simp; omega
    simp [this]

theorem bwd_movePast_body (n t : Nat) (ht : t ≤ n) : movePast .backward n (6 + 6 * t) = 2 * t := by
  induction t with
  | zero => simpa using bwd_movePast_pre n 6 (by omega)
  | succ t ih =>
    have lt : t < n := by omega
    have e0 := bwd_movePast_step n t 0 lt (by omega)
    have e1 := bwd_movePast_step n t 1 lt (by omega)
    have e2 := bwd_movePast_step n t 2 lt (by omega)
    have e3 := bwd_movePast_step n t 3 lt (by omega)
    have e4 := bwd_movePast_step n t 4 lt (by omega)
    have e5 := bwd_movePast_step n t 5 lt (by omega)
    rw [Nat.add_zero, if_neg (by omega)] at e0
    rw [if_neg (by omega)] at e1
    rw [if_pos (by omega)] at e2
    rw [if_pos (by omega)] at e3
    rw [if_neg (by omega)] at e4
    rw [if_neg (by omega)] at e5
    rw [show 6 + 6 * (t + 1) = 6 + 6 * t + 5 + 1 by omega, e5,
      show 6 + 6 * t + 5 = 6 + 6 * t + 4 + 1 by omega, e4, show 6 + 6 * t + 4 = 6 + 6 * t + 3 + 1 by omega, e3,
      show 6 + 6 * t + 3 = 6 + 6 * t + 2 + 1 by omega, e2, show 6 + 6 * t + 2 = 6 + 6 * t + 1 + 1 by omega, e1, e0, show 6 + 6 * t + 0 = 6 + 6 * t from rfl,
      ih (by omega)]
    omega

/-! ## EnvM over the backward loop -/

section env
variable (c : Context) (bwd : c.path = .backward) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)

include bwd in
theorem pc_bwd (t j : Nat) (room : t < c.n) (slot : j < 6) (x : NativeState) (env : EnvM c catalogue entry (6 + 6 * t + j) x) :
    x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memmove_entry + 24 + 4 * j) := by
  rw [env.core.v1.pc, bwd_offset_body c bwd t j room slot]
  rfl

include bwd in
theorem bwd_next_placed (t j : Nat) (room : t < c.n) (slot : j < 5) (x : NativeState)
    (env : EnvM c catalogue entry (6 + 6 * t + j) x) :
    x.regs._PC + 4#64 = c.base + offset c (6 + 6 * t + j + 1) := by
  rw [pc_bwd c bwd catalogue entry t j room (by omega) x env]
  rw [show 6 + 6 * t + j + 1 = 6 + 6 * t + (j + 1) by omega, bwd_offset_body c bwd t (j + 1) room (by omega)]
  unfold MemReloc.imageAddress
  rw [show Generated.armcert_memmove_entry + 24 + 4 * (j + 1) = (Generated.armcert_memmove_entry + 24 + 4 * j) + 4 by omega]
  simp only [BitVec.ofNat_add, BitVec.add_assoc]

include bwd in
/-- A zero-draw step advances EnvM at a non-memory index (j ∈ {0, 1, 4, 5}) of a backward iteration. -/
theorem bwd_advance0 (t j : Nat) (room : t < c.n) (hj : ¬ (2 ≤ j ∧ j < 4)) (hj6 : j < 6) (x fin : NativeState)
    (env : EnvM c catalogue entry (6 + 6 * t + j) x)
    (core : ReleaseProfile.DefaultCurrent.CurrentInv c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
      (offset c) c.budget (6 + 6 * t + j + 1) catalogue fin)
    (choice : NativeMteTagCheck.ChoiceDelta x fin 0) : EnvM c catalogue entry (6 + 6 * t + j + 1) fin :=
  ReleaseProfile.DefaultRuntime.InvG.advance env core True.intro ⟨0, choice, Nat.le_refl 0⟩
    (by rw [bwd, bwd_movePast_step c.n t j room hj6, if_neg hj]; exact Nat.le_refl _)

end env

/-! ## Memory facts with the backward registers (LDRB w5,[x4]; STRB w5,[x3]) -/

theorem load_facts_b (c : Context) (i : Nat) (room : i < c.n) (x : NativeState) (byte : BitVec 8)
    (cursor : x.regs.gpr[4] = c.s + BitVec.ofNat 64 i)
    (present : x.mem[c.srcPA i]? = some byte) :
    ArmCertMemPipe.LdrbU.Facts c.spec c.config c.rows c.mapping c.consumer 0#12 4#5 x := by
  obtain ⟨pa, mapped, mmio, outside⟩ := source_mapped c i room
  have addr : MemClass.LdrbU.addr x 4#5 0#12 = c.s + BitVec.ofNat 64 i := by
    rw [CopyNative.load_addr_zero]; exact cursor
  have physical : c.srcPA i = pa.toNat := by simp only [Context.srcPA, mapped, Option.getD_some]
  refine ⟨pa, by rw [addr]; exact mapped, mmio, outside, ⟨byte, ?_⟩, ?_⟩
  · intro j bounded
    have : j = 0 := by omega
    subst j
    simpa [physical] using present
  · intro acc shape
    rw [addr]
    exact SpanMap.data_permitted (spans c.d c.s c.n)
      (Image.codeVAs c.base Generated.imageStart Generated.imageWords) c.mapping (rowsFootprint c.spec.imageRows).byte
      (sourceSpan c.s c.n) (by simp [spans]) i room acc shape

/-! ## CBNZ back-edge of the backward loop (word 528 → 508 / 532) -/

section branch
variable (c : Context) (bwd : c.path = .backward) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
include bwd

theorem bwd_branch_target (t : Nat) (room : t < c.n) (x : NativeState) (env : EnvM c catalogue entry (6 + 6 * t + 5) x) :
    LoopNative.Cbnz64.target CopyNative.backImmediate x = c.base + 508#64 := by
  rw [LoopNative.Cbnz64.target, CopyNative.back_delta, pc_bwd c bwd catalogue entry t 5 room (by decide) x env]
  unfold MemReloc.imageAddress
  change c.base + 528#64 + BitVec.ofInt 64 (-20) = c.base + 508#64
  bv_omega

theorem bwd_branch_low (t : Nat) (room : t < c.n) (x : NativeState) (env : EnvM c catalogue entry (6 + 6 * t + 5) x) :
    (LoopNative.Cbnz64.target CopyNative.backImmediate x).toNat < 2 ^ 55 := by
  rw [bwd_branch_target c bwd catalogue entry t room x env]
  have low := c.low
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem bwd_branch_taken_placed (t : Nat) (again : t + 1 < c.n) (x : NativeState)
    (env : EnvM c catalogue entry (6 + 6 * t + 5) x) :
    LoopNative.Cbnz64.target CopyNative.backImmediate x = c.base + offset c (6 + 6 * t + 5 + 1) := by
  rw [bwd_branch_target c bwd catalogue entry t (by omega) x env, bwd_offset_after c bwd t (by omega), if_pos again]
  rfl

theorem bwd_branch_not_placed (t : Nat) (last : t + 1 = c.n) (room : t < c.n) (x : NativeState)
    (env : EnvM c catalogue entry (6 + 6 * t + 5) x) :
    x.regs._PC + 4#64 = c.base + offset c (6 + 6 * t + 5 + 1) := by
  rw [pc_bwd c bwd catalogue entry t 5 room (by decide) x env, bwd_offset_after c bwd t room,
    if_neg (by omega : ¬ t + 1 < c.n)]
  unfold MemReloc.imageAddress
  change c.base + 528#64 + 4#64 = c.base + 532#64
  bv_omega

attribute [local instance 10] Classical.propDecidable in
theorem bwd_branch_step (real : Type) [Sail.SailReal real] (nodup : (c.spec.logicalRows.map (·.logical)).Nodup)
    (t : Nat) (room : t < c.n)
    (x : NativeState) (env : EnvM c catalogue entry (6 + 6 * t + 5) x)
    (remaining : x.regs.gpr[2].toNat = c.n - (t + 1)) :
    ∃ y, modelStep real x = .ok () y ∧ EnvM c catalogue entry (6 + 6 * (t + 1)) y ∧ y.mem = x.mem ∧
      y.regs.gpr = x.regs.gpr ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧ NativeEntry.Effects.Frame {} x.regs y.regs ∧
      StepEvents.EvShape c.spec c.mapping [] x y := by
  have fetch : FetchObligations c.spec c.config c.rows c.mapping (Route7Cbnz.Tail.W 2#5 CopyNative.backImmediate) x := by
    exact fetch_index_m c catalogue entry (6 + 6 * t + 5) 27 x env (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry] using
        pc_bwd c bwd catalogue entry t 5 room (by decide) x env)
  have placed : (if ReleaseProfile.HeapCbzAction.cbzCond x 1#1 1#1 2#5
      then x.regs._PC + sign_extend (CopyNative.backImmediate ++ 0#2) 64 else x.regs._PC + 4#64) =
      c.base + offset c (6 + 6 * t + 5 + 1) := by
    by_cases again : t + 1 < c.n
    · have nonzero : x.regs.gpr[(GPRSummary.key (2#5).toNat).val] ≠ 0#64 := by
        intro same
        have zero := congrArg BitVec.toNat same
        change x.regs.gpr[2].toNat = (0#64).toNat at zero
        simp only [BitVec.toNat_ofNat] at zero
        omega
      rw [if_pos ((Route7Copy.cbnz_cond_iff x).2 nonzero)]
      change LoopNative.Cbnz64.target CopyNative.backImmediate x = _
      exact bwd_branch_taken_placed c bwd catalogue entry t again x env
    · have zero : x.regs.gpr[(GPRSummary.key (2#5).toNat).val] = 0#64 := by
        apply BitVec.eq_of_toNat_eq
        change x.regs.gpr[2].toNat = 0
        omega
      rw [if_neg (fun h => (Route7Copy.cbnz_cond_iff x).1 h zero)]
      exact bwd_branch_not_placed c bwd catalogue entry t (by omega) room x env
  obtain ⟨y, run, inv', holds, memory, sys, z, dit, kept, choice, ev⟩ :=
    Route7Steps.cbnz64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (6 + 6 * t + 5) catalogue
      (bwd_body_room c bwd t 5 room (by decide)) c.page (bwd_body_aligned c bwd t 5 room (by decide))
      2#5 CopyNative.backImmediate x env.core nodup (bwd_branch_low c bwd catalogue entry t room x env) _ rfl placed fetch
  have env' : EnvM c catalogue entry (6 + 6 * (t + 1)) y := by
    have adv := bwd_advance0 c bwd catalogue entry t 5 room (by omega) (by omega) x y env inv' choice
    simpa only [show 6 + 6 * t + 5 + 1 = 6 + 6 * (t + 1) by omega] using adv
  exact ⟨y, run, env', memory, ValueFacts.nil_gpr x y holds, ValueFacts.nil_sp x y holds, kept, ev⟩

end branch

/-! ## Backward iteration -/

/-- Backward loop header at iteration t (k = 6 + 6t): x3/x4 one past the next byte n-1-t. -/
structure HeaderB (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (t : Nat) (x : NativeState) : Prop where
  positive : 0 < c.n
  bound : t ≤ c.n
  environment : EnvM c catalogue entry (6 + 6 * t) x
  dest : x.regs.gpr[0] = c.d
  destCursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 (c.n - t)
  sourceCursor : x.regs.gpr[4] = c.s + BitVec.ofNat 64 (c.n - t)
  remaining : x.regs.gpr[2].toNat = c.n - t
  link : x.regs.gpr[30] = c.returnPC
  saved : ∀ r : Fin 31, (r.val = 1 ∨ 6 ≤ r.val) → x.regs.gpr[r.val] = entry.regs.gpr[r.val]
  sp : x.regs.SP_EL0 = entry.regs.SP_EL0
  protectedRegs : NativeEntry.Effects.Frame {} entry.regs x.regs
  bytes : Bytes.CopyPrefix c.srcR c.dstR (Aux.memoryView entry) (Aux.memoryView x) c.n t

/-- One backward iteration (6 steps): copies byte n-1-t, re-establishes the header at t+1. -/
theorem bwd_body (real : Type) [Sail.SailReal real] (c : Context) (bwd : c.path = .backward)
    (gt : c.s.toNat < c.d.toNat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry x : NativeState)
    (t : Nat) (room : t < c.n) (byte : BitVec 8) (header : HeaderB c catalogue entry t x)
    (value : Aux.memoryView x (c.srcR t) = some byte) :
    ∃ y, Uget.Chain.modelRun real 6 x = .ok () y ∧
      Bytes.SingleWrite (Aux.memoryView x) (Aux.memoryView y) (c.dstR t) byte ∧ HeaderB c catalogue entry (t + 1) y ∧
      Route7Copy.Covered real (PcOkM c) 6 x ∧ Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) 6 (6 + 6 * t) x := by
  let k := 6 + 6 * t
  have env := header.environment
  have ir : c.n - 1 - t < c.n := by omega
  -- j = 0: SUB x3, x3, #1
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping (Route7Sub.Dispatch.selected 3#5 3#5 1#12) x := by
    exact fetch_index_m c catalogue entry k 22 x env (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry, Nat.add_zero] using
        pc_bwd c bwd catalogue entry t 0 room (by decide) x env)
  obtain ⟨a, run0, core1, values0, memory0, _, _, _, frame0, choice0, ev0⟩ :=
    Route7Steps.subImm64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget k catalogue
      (by simpa only [Nat.add_zero] using bwd_body_room c bwd t 0 room (by decide)) c.page
      (by simpa only [Nat.add_zero] using bwd_body_aligned c bwd t 0 room (by decide))
      3#5 3#5 1#12 (by decide) (by decide) x env.core nodup
      (by simpa only [Nat.add_zero] using bwd_next_placed c bwd catalogue entry t 0 room (by decide) x env) fetch0
  have env1 : EnvM c catalogue entry (6 + 6 * t + 1) a := by
    have adv := bwd_advance0 c bwd catalogue entry t 0 room (by omega) (by omega) x a
      (by simpa only [Nat.add_zero] using env) (by simpa only [Nat.add_zero] using core1) choice0
    simpa only [Nat.add_zero] using adv
  obtain ⟨gpr0, sp0⟩ := ValueFacts.sub 3#5 3#5 1#12 x a values0
  change a.regs.gpr = x.regs.gpr.set 3 (x.regs.gpr[3] - 1#64) at gpr0
  -- j = 1: SUB x4, x4, #1
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping (Route7Sub.Dispatch.selected 4#5 4#5 1#12) a := by
    exact fetch_index_m c catalogue entry (k + 1) 23 a env1 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry] using
        pc_bwd c bwd catalogue entry t 1 room (by decide) a env1)
  obtain ⟨b, run1, core2, values1, memory1, _, _, _, frame1, choice1, ev1⟩ :=
    Route7Steps.subImm64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (k + 1) catalogue
      (bwd_body_room c bwd t 1 room (by decide)) c.page (bwd_body_aligned c bwd t 1 room (by decide))
      4#5 4#5 1#12 (by decide) (by decide) a env1.core nodup
      (bwd_next_placed c bwd catalogue entry t 1 room (by decide) a env1) fetch1
  have env2 : EnvM c catalogue entry (6 + 6 * t + 2) b :=
    bwd_advance0 c bwd catalogue entry t 1 room (by omega) (by omega) a b env1 core2 choice1
  obtain ⟨gpr1, sp1⟩ := ValueFacts.sub 4#5 4#5 1#12 a b values1
  change b.regs.gpr = a.regs.gpr.set 4 (a.regs.gpr[4] - 1#64) at gpr1
  have destB : b.regs.gpr[3] = c.d + BitVec.ofNat 64 (c.n - 1 - t) := by
    rw [gpr1, Vector.getElem_set_ne _ _ (by decide), gpr0, Vector.getElem_set_self, header.destCursor,
      cursor_pred _ _ (by omega)]
    congr 2 <;> omega
  have sourceB : b.regs.gpr[4] = c.s + BitVec.ofNat 64 (c.n - 1 - t) := by
    rw [gpr1, Vector.getElem_set_self, gpr0, Vector.getElem_set_ne _ _ (by decide), header.sourceCursor,
      cursor_pred _ _ (by omega)]
    congr 2 <;> omega
  -- j = 2: LDRB w5, [x4]
  have past2 : movePast c.path c.n (k + 2) = 2 * t := by
    have p0 := bwd_movePast_step c.n t 0 room (by omega)
    have p1 := bwd_movePast_step c.n t 1 room (by omega)
    rw [Nat.add_zero, if_neg (by omega)] at p0
    rw [if_neg (by omega)] at p1
    rw [bwd, show k + 2 = 6 + 6 * t + 1 + 1 by omega, p1, p0, show 6 + 6 * t + 0 = 6 + 6 * t from rfl, bwd_movePast_body c.n t (by omega)]
    omega
  have fetch2 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.LdrbUoff.selected 5#5 4#5 0#12) b := by
    exact fetch_index_m c catalogue entry (k + 2) 24 b env2 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry] using
        pc_bwd c bwd catalogue entry t 2 room (by decide) b env2)
  have allowed2 := ReleaseProfile.DefaultRuntime.current_status env2 (by omega : movePast c.path c.n (k + 2) < 2 * c.n)
  have valueB : b.mem[c.srcPA (c.n - 1 - t)]? = some byte := by
    rw [memory1, memory0]; exact value
  obtain ⟨e3, run2, ms2, frame2⟩ :=
    Route7Mem.DefaultLdrbU.routeF real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (k + 2) catalogue
      (bwd_body_room c bwd t 2 room (by decide)) c.page (bwd_body_aligned c bwd t 2 room (by decide))
      (NativeEntryBodyDispatch.LdrbUoff.selected 5#5 4#5 0#12) 633 (by decide) 0#12 4#5 5#5 (by decide) (by decide)
      (fun pc u see => NativeEntryBodyDispatch.LdrbUoff.dispatch_at real pc 5#5 4#5 0#12 u (by simpa using see))
      (LoopNative.Encoding.LdrbU_noEret 5#5 4#5 0#12) b env2.core allowed2
      (load_facts_b c (c.n - 1 - t) ir b byte sourceB valueB)
      (bwd_next_placed c bwd catalogue entry t 2 room (by decide) b env2) fetch2 nodup
  have env3 : EnvM c catalogue entry (6 + 6 * t + 3) e3 :=
    ReleaseProfile.DefaultRuntime.InvG.advance env2 ms2.current True.intro ms2.choice
      (by rw [bwd, bwd_movePast_step c.n t 2 room (by omega)]; rw [bwd] at past2; simp [past2, k])
  obtain ⟨sourcePA, loadedByte, mapped2, present2, gpr2, sp2, memory2⟩ :=
    NativeBytes.load_payload c.mapping 0#12 4#5 5#5 b e3 ms2.pay
  have addr2 : MemClass.LdrbU.addr b 4#5 0#12 = c.s + BitVec.ofNat 64 (c.n - 1 - t) := by
    rw [CopyNative.load_addr_zero]; exact sourceB
  have physical2 : c.srcPA (c.n - 1 - t) = sourcePA.toNat := by
    simp only [Context.srcPA, ← addr2, mapped2, Option.getD_some]
  have byteEq : loadedByte = byte := by
    apply Option.some.inj
    exact present2.symm.trans (by simpa only [physical2] using valueB)
  subst loadedByte
  change e3.regs.gpr = b.regs.gpr.set 5 (byte.setWidth 64) at gpr2
  have dest3 : e3.regs.gpr[3] = c.d + BitVec.ofNat 64 (c.n - 1 - t) := by
    rw [gpr2]; simpa using destB
  -- j = 3: STRB w5, [x3]
  have fetch3 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.StrbUoff.selected 5#5 3#5 0#12) e3 := by
    exact fetch_index_m c catalogue entry (k + 3) 25 e3 env3 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry] using
        pc_bwd c bwd catalogue entry t 3 room (by decide) e3 env3)
  have codeD : ImageTableSeparated codeScope c.base c.mapping (DestinationPA c.mapping c.d c.n) := by
    intro off pa inside mapped target
    exact c.codeWrite off inside pa mapped target
  have past3 : movePast c.path c.n (k + 3) = 2 * t + 1 := by
    rw [bwd, show k + 3 = 6 + 6 * t + 2 + 1 by omega, bwd_movePast_step c.n t 2 room (by omega)]
    rw [bwd] at past2; simp [past2, k]
  have allowed3 := ReleaseProfile.DefaultRuntime.current_status env3 (by omega : movePast c.path c.n (k + 3) < 2 * c.n)
  obtain ⟨e4, run3, ms3, frame3⟩ :=
    Route7Mem.DefaultStrbU.routeF real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (k + 3) catalogue
      (bwd_body_room c bwd t 3 room (by decide)) c.page (bwd_body_aligned c bwd t 3 room (by decide))
      (NativeEntryBodyDispatch.StrbUoff.selected 5#5 3#5 0#12) 651 (by decide) 0#12 3#5 5#5 (by decide) (by decide)
      (fun pc u see => NativeEntryBodyDispatch.StrbUoff.dispatch_at real pc 5#5 3#5 0#12 u (by simpa using see))
      (LoopNative.Encoding.StrbU_noEret 5#5 3#5 0#12) (DestinationPA c.mapping c.d c.n) codeD e3 env3.core allowed3
      (store_facts_m c (c.n - 1 - t) ir e3 dest3) (bwd_next_placed c bwd catalogue entry t 3 room (by decide) e3 env3)
      fetch3 nodup
  have env4 : EnvM c catalogue entry (6 + 6 * t + 4) e4 :=
    ReleaseProfile.DefaultRuntime.InvG.advance env3 ms3.current True.intro ms3.choice
      (by rw [bwd, bwd_movePast_step c.n t 3 room (by omega)]; rw [bwd] at past3; simp [past3, k])
  obtain ⟨destPA, mapped3, written, gpr3, sp3⟩ := NativeBytes.store_payload c.mapping 0#12 3#5 5#5 e3 e4 ms3.pay
  have addr3 : MemClass.StrbU.addr e3 3#5 0#12 = c.d + BitVec.ofNat 64 (c.n - 1 - t) := by
    rw [CopyNative.store_addr_zero]; exact dest3
  have physical3 : c.dstPA (c.n - 1 - t) = destPA.toNat := by
    simp only [Context.dstPA, ← addr3, mapped3, Option.getD_some]
  have storedByte : e3.regs.gpr[5].setWidth 8 = byte := by
    rw [gpr2, Vector.getElem_set_self]
    exact NativeBytes.zeroExtend_lowByte byte
  change Bytes.SingleWrite (Aux.memoryView e3) (Aux.memoryView e4) destPA.toNat (e3.regs.gpr[5].setWidth 8) at written
  rw [← physical3, storedByte] at written
  have sameView : Aux.memoryView e3 = Aux.memoryView x := by
    unfold Aux.memoryView; rw [memory2, memory1, memory0]
  rw [sameView] at written
  -- j = 4: SUB x2, x2, #1
  have fetch4 : FetchObligations c.spec c.config c.rows c.mapping (Route7Sub.Dispatch.selected 2#5 2#5 1#12) e4 := by
    exact fetch_index_m c catalogue entry (k + 4) 26 e4 env4 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry] using
        pc_bwd c bwd catalogue entry t 4 room (by decide) e4 env4)
  obtain ⟨e5, run4, core5, values4, memory4, _, _, _, frame4, choice4, ev4⟩ :=
    Route7Steps.subImm64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (k + 4) catalogue
      (bwd_body_room c bwd t 4 room (by decide)) c.page (bwd_body_aligned c bwd t 4 room (by decide))
      2#5 2#5 1#12 (by decide) (by decide) e4 env4.core nodup
      (bwd_next_placed c bwd catalogue entry t 4 room (by decide) e4 env4) fetch4
  have env5 : EnvM c catalogue entry (6 + 6 * t + 5) e5 :=
    bwd_advance0 c bwd catalogue entry t 4 room (by omega) (by omega) e4 e5 env4 core5 choice4
  obtain ⟨gpr4, sp4⟩ := ValueFacts.sub 2#5 2#5 1#12 e4 e5 values4
  change e5.regs.gpr = e4.regs.gpr.set 2 (e4.regs.gpr[2] - 1#64) at gpr4
  have regs4 : e4.regs.gpr = (((x.regs.gpr.set 3 (x.regs.gpr[3] - 1#64)).set 4 (x.regs.gpr[4] - 1#64)).set 5
      (byte.setWidth 64)) := by
    rw [gpr3, gpr2, gpr1, gpr0]
    simp
  have counter4 : e4.regs.gpr[2] = x.regs.gpr[2] := by rw [regs4]; simp
  have positive : 0 < x.regs.gpr[2].toNat := by have := header.remaining; omega
  have remaining5 : e5.regs.gpr[2].toNat = c.n - (t + 1) := by
    rw [gpr4, Vector.getElem_set_self, counter4, Schedule.counter_pred _ positive, header.remaining]
    omega
  -- j = 5: CBNZ x2, 508 / fall through to RET
  obtain ⟨y, run5, env6, memory5, gpr5, sp5, kept5, ev5⟩ :=
    bwd_branch_step c bwd catalogue entry real nodup t room e5 env5 remaining5
  have regsY : y.regs.gpr = ((((x.regs.gpr.set 3 (x.regs.gpr[3] - 1#64)).set 4 (x.regs.gpr[4] - 1#64)).set 5
      (byte.setWidth 64)).set 2 (x.regs.gpr[2] - 1#64)) := by
    rw [gpr5, gpr4, counter4, regs4]
  -- bytes: copyPrefix_succ over the reversed maps; overlap side condition from s <u d
  have finalWritten := NativeBytes.write_after_memory_frames
    (before := x) (load := x) (store := e4) (after := y) rfl written (memory5.trans memory4)
  have copied := Bytes.copyPrefix_succ (src := c.srcR) (dst := c.dstR) header.bytes room value finalWritten
    (fun u prior => dest_distinct c (c.n - 1 - t) (c.n - 1 - u) ir (by omega) (by omega))
    (fun u later bounded => backward_future c gt t u room later bounded)
  have runY : Uget.Chain.modelRun real 6 x = .ok () y := by
    simp only [Uget.Chain.modelRun, run0, run1, run2, run3, run4, run5]
  refine ⟨y, runY, finalWritten, ⟨header.positive, by omega, env6, ?_, ?_, ?_, ?_, ?_, ?_,
    sp5.trans (sp4.trans (sp3.trans (sp2.trans (sp1.trans (sp0.trans header.sp))))),
    ((((header.protectedRegs.trans frame0).trans frame1).trans frame2).trans frame3).trans frame4 |>.trans kept5, copied⟩, ?_, ?_⟩
  · rw [regsY]; simpa using header.dest
  · rw [regsY]
    simp only [Vector.getElem_set_ne _ _ (by decide : (2 : Nat) ≠ 3), Vector.getElem_set_ne _ _ (by decide : (5 : Nat) ≠ 3),
      Vector.getElem_set_ne _ _ (by decide : (4 : Nat) ≠ 3), Vector.getElem_set_self, header.destCursor]
    rw [cursor_pred _ _ (by omega)]
    congr 2 <;> omega
  · rw [regsY]
    simp only [Vector.getElem_set_ne _ _ (by decide : (2 : Nat) ≠ 4), Vector.getElem_set_ne _ _ (by decide : (5 : Nat) ≠ 4),
      Vector.getElem_set_self, header.sourceCursor]
    rw [cursor_pred _ _ (by omega)]
    congr 2 <;> omega
  · rw [gpr5]; exact remaining5
  · rw [regsY]; simpa using header.link
  · intro r saved
    have n2 : 2 ≠ r.val := by omega
    have n3 : 3 ≠ r.val := by omega
    have n4 : 4 ≠ r.val := by omega
    have n5 : 5 ≠ r.val := by omega
    rw [regsY]
    simpa [Vector.getElem_set, n2, n3, n4, n5] using header.saved r saved
  · -- coverage (loops)
    intro m hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6) with hm | hm | hm | hm | hm | hm | hm <;> subst hm
    · exact ⟨x, rfl, pcOk_of_env_m c catalogue entry _ x env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env_m c catalogue entry _ a env1⟩
    · exact ⟨b, by simp only [Uget.Chain.modelRun, run0, run1], pcOk_of_env_m c catalogue entry _ b env2⟩
    · exact ⟨e3, by simp only [Uget.Chain.modelRun, run0, run1, run2], pcOk_of_env_m c catalogue entry _ e3 env3⟩
    · exact ⟨e4, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3], pcOk_of_env_m c catalogue entry _ e4 env4⟩
    · exact ⟨e5, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3, run4], pcOk_of_env_m c catalogue entry _ e5 env5⟩
    · exact ⟨y, runY, pcOk_of_env_m c catalogue entry _ y env6⟩
  · -- trace (loops CT0): SUB / SUB / LDRB s+(n-1-t) / STRB d+(n-1-t) / SUB / CBNZ
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with hj | hj | hj | hj | hj | hj <;> subst hj
    · refine ⟨x, a, rfl, run0, ?_, ?_⟩
      · rw [Nat.add_zero]; exact pcAt_of_env_m c catalogue entry _ x env
      · rw [recs_bwd_nil c bwd (6 + 6 * t + 0) (by omega) (by omega)]; exact ⟨ev0, frame0⟩
    · refine ⟨a, b, by simp only [Uget.Chain.modelRun, run0], run1, ?_, ?_⟩
      · exact pcAt_of_env_m c catalogue entry _ a env1
      · rw [recs_bwd_nil c bwd (6 + 6 * t + 1) (by omega) (by omega)]; exact ⟨ev1, frame1⟩
    · refine ⟨b, e3, by simp only [Uget.Chain.modelRun, run0, run1], run2, ?_, ?_⟩
      · exact pcAt_of_env_m c catalogue entry _ b env2
      · have ev2 := ms2.events; rw [addr2, ← recs_bwd_ldrb c bwd t room] at ev2; exact ⟨ev2, frame2⟩
    · refine ⟨e3, e4, by simp only [Uget.Chain.modelRun, run0, run1, run2], run3, ?_, ?_⟩
      · exact pcAt_of_env_m c catalogue entry _ e3 env3
      · have ev3 := ms3.events; rw [addr3, ← recs_bwd_strb c bwd t room] at ev3; exact ⟨ev3, frame3⟩
    · refine ⟨e4, e5, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3], run4, ?_, ?_⟩
      · exact pcAt_of_env_m c catalogue entry _ e4 env4
      · rw [recs_bwd_nil c bwd (6 + 6 * t + 4) (by omega) (by omega)]; exact ⟨ev4, frame4⟩
    · refine ⟨e5, y, by simp only [Uget.Chain.modelRun, run0, run1, run2, run3, run4], run5, ?_, ?_⟩
      · exact pcAt_of_env_m c catalogue entry _ e5 env5
      · rw [recs_bwd_nil c bwd (6 + 6 * t + 5) (by omega) (by omega)]; exact ⟨ev5, kept5⟩

/-- Final RET of the backward path (k = 6 + 6n, word 532) with the complete MovePost (reindexing n-1-t ↦ i). -/
theorem bwd_exit (real : Type) [Sail.SailReal real] (c : Context) (bwd : c.path = .backward)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry x : NativeState)
    (header : HeaderB c catalogue entry c.n x) :
    ∃ y, Uget.Chain.modelRun real 1 x = .ok () y ∧ y.regs._PC = c.returnPC ∧
      y.mem = x.mem ∧ (MovePost c.mapping c.d c.s c.returnPC c.n entry y ∧ ExtraM c entry y) ∧ Route7Copy.Covered real (PcOkM c) 1 x ∧
      Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) 1 (6 + 6 * c.n) x := by
  have fetch : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) x := by
    exact fetch_index_m c catalogue entry (6 + 6 * c.n) 28 x header.environment (by decide) (by
      rw [header.environment.core.v1.pc, bwd_offset_exit c bwd]
      rfl)
  obtain ⟨y, run, pc, holds, memory, _, _, _, kept, _, ev⟩ :=
    Route7Steps.retE real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (6 + 6 * c.n) catalogue
      (by rw [bwd_budget c bwd]; omega) c.page
      (by rw [bwd_offset_exit c bwd]; decide) 30#5 (by decide) x header.environment.core nodup
      (by change x.regs.gpr[30].toNat < 2 ^ 55; rw [header.link]; have := c.returnLow; omega) fetch
  have gpr := ValueFacts.nil_gpr x y holds
  have sp := ValueFacts.nil_sp x y holds
  have abi := header.protectedRegs.trans kept
  have runY : Uget.Chain.modelRun real 1 x = .ok () y := by simp only [Uget.Chain.modelRun, run]
  refine ⟨y, runY, pc.trans header.link, memory, ⟨⟨pc.trans header.link, ?_, ?_, ?_, ?_,
    sp.trans header.sp, LoopNative.MemoryFrame.vector abi rfl,
    LoopNative.MemoryFrame.fpcr abi rfl, LoopNative.MemoryFrame.fpsr abi rfl⟩, ?_⟩,
    Route7Copy.covered_one real (PcOkM c) x y runY (pcOk_of_env_m c catalogue entry _ x header.environment)
      ⟨Or.inl (pc.trans header.link), CT1.Route7Word.imageWords_of_mem memory (pcOk_of_env_m c catalogue entry _ x header.environment).2⟩,
    Route7Trace.traced_one real c.spec c.mapping (recsOfM c) (pcOfM c) _ x y run (pcAt_of_env_m c catalogue entry _ x header.environment)
      (by rw [recs_bwd_nil c bwd (6 + 6 * c.n) (by omega) (by omega)]; exact ev) kept⟩
  · change y.regs.gpr[0] = c.d
    rw [gpr]
    exact header.dest
  · intro i room
    obtain ⟨sourcePA, mappedS, _, _⟩ := source_mapped c i room
    obtain ⟨destPA, mappedD, _, _⟩ := dest_mapped c i room
    have source : c.srcPA i = sourcePA.toNat := by simp only [Context.srcPA, mappedS, Option.getD_some]
    have dest : c.dstPA i = destPA.toNat := by simp only [Context.dstPA, mappedD, Option.getD_some]
    have back : c.n - 1 - (c.n - 1 - i) = i := by omega
    have got := header.bytes.copied (c.n - 1 - i) (by omega)
    simp only [Context.srcR, Context.dstR, back] at got
    simp only [readByte, mappedD, mappedS, Option.bind_some, memory]
    simpa only [Aux.memoryView, source, dest] using got
  · intro pa outside
    rw [memory]
    apply header.bytes.frame pa
    rintro ⟨u, room, same⟩
    have ir : c.n - 1 - u < c.n := by omega
    obtain ⟨p, mapped, _, _⟩ := dest_mapped c (c.n - 1 - u) ir
    have physical : c.dstPA (c.n - 1 - u) = p.toNat := by simp only [Context.dstPA, mapped, Option.getD_some]
    apply outside
    refine ⟨c.n - 1 - u, ir, ?_⟩
    rw [mapped, ← physical]
    exact congrArg some same
  · intro r saved
    change y.regs.gpr[r.val] = entry.regs.gpr[r.val]
    rw [gpr]
    exact header.saved r (Or.inr saved)
  · refine ⟨fun h => (by rcases h with h | h <;> (rw [bwd] at h; cases h)), fun h => (by rw [bwd] at h; cases h),
      fun _ => ⟨?_, ?_, ?_, ?_, fun r hr => ?_⟩⟩
    · change y.regs.gpr[1] = _; rw [gpr]; exact header.saved ⟨1, by decide⟩ (Or.inl rfl)
    · change y.regs.gpr[2].toNat = 0; rw [gpr]; rw [header.remaining]; omega
    · change y.regs.gpr[3] = _; rw [gpr]; exact header.destCursor
    · change y.regs.gpr[4] = _; rw [gpr]; exact header.sourceCursor
    · change y.regs.gpr[r.val] = _; rw [gpr]; exact header.saved r (Or.inr hr)

end Route7Move.CT2

#print axioms Route7Move.CT2.bwd_movePast_body
#print axioms Route7Move.CT2.bwd_body
#print axioms Route7Move.CT2.bwd_exit
