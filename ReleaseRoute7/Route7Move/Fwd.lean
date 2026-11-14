-- Route 7 breadth: memmove FORWARD path (d <u s) loop over EnvM: geometry, LDRB/STRB pair,
-- ADD/ADD/SUB/CBNZ tail, iteration and final RET. Ported from Route7Copy (Pair/Rest/Body) with the loop
-- at k = 5 + 6i (words 540..560) and the overlap invariant `forward_future` in place of memcpy disjointness.
import Route7Move.Context
import Route7Move.Cover
import Route7Trace.Move
import Route7StepsE.Class
import Route7StepsE.Branch
import Route7Copy.Body
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option Elab.async false

namespace Route7Move
open ArmCertLoop ArmCertLoop.ContractDraft

/-- memmove postcondition = loops' CopyPost (bytes compared against the ENTRY source, so overlap-correct). -/
abbrev MovePost := CopyPost

/-! ## Forward geometry -/

section geometry
variable (c : Context) (fwd : c.path = .forward)
include fwd

theorem fwd_budget : c.budget = 6 * c.n + 6 := by simp only [Context.budget, fwd, Schedule.moveSteps]

theorem fwd_body_room (i j : Nat) (room : i < c.n) (slot : j < 6) : 5 + 6 * i + j < c.budget := by
  rw [fwd_budget c fwd]; omega

theorem fwd_offset_body (i j : Nat) (room : i < c.n) (slot : j < 6) :
    offset c (5 + 6 * i + j) = BitVec.ofNat 64 (Generated.armcert_memmove_entry + 56 + 4 * j) := by
  have index : 5 + 6 * i + j ≠ c.budget := by have := fwd_body_room c fwd i j room slot; omega
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg index, fwd, forward_loop_offset c.n i j room slot, Nat.add_assoc]

theorem fwd_body_aligned (i j : Nat) (room : i < c.n) (slot : j < 6) :
    (offset c (5 + 6 * i + j)).toNat % 4 = 0 := by
  rw [fwd_offset_body c fwd i j room slot]
  have bound : Generated.armcert_memmove_entry + 56 + 4 * j < 2 ^ 64 := by
    simp only [Generated.armcert_memmove_entry]; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Generated.armcert_memmove_entry]
  omega

theorem fwd_offset_after (i : Nat) (room : i < c.n) :
    offset c (5 + 6 * i + 5 + 1) =
      BitVec.ofNat 64 (Generated.armcert_memmove_entry + (if i + 1 < c.n then 56 else 80)) := by
  have index : 5 + 6 * i + 5 + 1 ≠ c.budget := by rw [fwd_budget c fwd]; omega
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg index, fwd]
  simp only [Schedule.moveWordOffset]
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases again : i + 1 < c.n
  · rw [if_pos (by omega), if_pos again]
    congr 2
    omega
  · rw [if_neg (by omega), if_neg again]

theorem fwd_offset_exit : offset c (5 + 6 * c.n) = BitVec.ofNat 64 (Generated.armcert_memmove_entry + 80) := by
  have index : 5 + 6 * c.n ≠ c.budget := by rw [fwd_budget c fwd]; omega
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg index, fwd]
  simp only [Schedule.moveWordOffset]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end geometry

/-- Memory steps on the forward path: LDRB at 5 + 6i, STRB at 6 + 6i. -/
theorem fwd_memStep_body (n i j : Nat) (hi : i < n) (hj : j < 6) :
    memStep .forward n (5 + 6 * i + j) = decide (j < 2) := by
  unfold memStep
  have h1 : (5 + 6 * i + j - 5) % 6 = j := by omega
  have h2 : (5 + 6 * i + j - 5) / 6 = i := by omega
  rw [h1, h2]
  by_cases h : j < 2
  · simp [h, hi]; (try omega)
  · simp [h]

theorem fwd_movePast_step (n i j : Nat) (hi : i < n) (hj : j < 6) :
    movePast .forward n (5 + 6 * i + j + 1) = movePast .forward n (5 + 6 * i + j) + (if j < 2 then 1 else 0) := by
  rw [movePast_succ, fwd_memStep_body n i j hi hj]
  by_cases h : j < 2 <;> simp [h]

theorem fwd_movePast_pre (n k : Nat) (hk : k ≤ 5) : movePast .forward n k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [movePast_succ, ih (by omega)]
    have : memStep .forward n k = false := by unfold memStep; simp; omega
    simp [this]

theorem fwd_movePast_body (n i : Nat) (hi : i ≤ n) : movePast .forward n (5 + 6 * i) = 2 * i := by
  induction i with
  | zero => simpa using fwd_movePast_pre n 5 (by omega)
  | succ i ih =>
    have lt : i < n := by omega
    have e0 := fwd_movePast_step n i 0 lt (by omega)
    have e1 := fwd_movePast_step n i 1 lt (by omega)
    have e2 := fwd_movePast_step n i 2 lt (by omega)
    have e3 := fwd_movePast_step n i 3 lt (by omega)
    have e4 := fwd_movePast_step n i 4 lt (by omega)
    have e5 := fwd_movePast_step n i 5 lt (by omega)
    simp only [Nat.add_zero, show (0 : Nat) < 2 from by omega, show (1 : Nat) < 2 from by omega,
      show ¬ (2 : Nat) < 2 from by omega, show ¬ (3 : Nat) < 2 from by omega, show ¬ (4 : Nat) < 2 from by omega,
      show ¬ (5 : Nat) < 2 from by omega, ite_true, ite_false] at e0 e1 e2 e3 e4 e5
    rw [show 5 + 6 * (i + 1) = 5 + 6 * i + 5 + 1 by omega, e5,
      show 5 + 6 * i + 5 = 5 + 6 * i + 4 + 1 by omega, e4, show 5 + 6 * i + 4 = 5 + 6 * i + 3 + 1 by omega, e3,
      show 5 + 6 * i + 3 = 5 + 6 * i + 2 + 1 by omega, e2, show 5 + 6 * i + 2 = 5 + 6 * i + 1 + 1 by omega, e1, e0,
      ih (by omega)]
    omega

/-! ## EnvM over the forward loop -/

section env
variable (c : Context) (fwd : c.path = .forward) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)

include fwd in
theorem pc_fwd (i j : Nat) (room : i < c.n) (slot : j < 6) (x : NativeState) (env : EnvM c catalogue entry (5 + 6 * i + j) x) :
    x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memmove_entry + 56 + 4 * j) := by
  rw [env.core.v1.pc, fwd_offset_body c fwd i j room slot]
  rfl

def fetch_index_m (k index : Nat) (x : NativeState) (env : EnvM c catalogue entry k x)
    (room : index < Generated.imageWords.length)
    (pc : x.regs._PC = MemReloc.imageAddress c.base (Generated.imageStart + 4 * index)) :
    FetchObligations c.spec c.config c.rows c.mapping (Generated.imageWords.getD index 0) x :=
  Route7Copy.fetch_word_cur c.spec c.config c.rows c.mapping (spans c.d c.s c.n)
    (rowsFootprint c.spec.imageRows).byte codeScope c.base Generated.imageStart Generated.imageWords
    (offset c) c.budget k catalogue index room x env.core pc
    (fun byte bounded => by unfold codeScope; have := room; simp only [Generated.imageWords_length, Generated.imageStart] at *; omega)
    (c.code index room).1 (c.code index room).2 c.separated

include fwd in
theorem fwd_next_placed (i j : Nat) (room : i < c.n) (slot : j < 5) (x : NativeState)
    (env : EnvM c catalogue entry (5 + 6 * i + j) x) :
    x.regs._PC + 4#64 = c.base + offset c (5 + 6 * i + j + 1) := by
  rw [pc_fwd c fwd catalogue entry i j room (by omega) x env]
  rw [show 5 + 6 * i + j + 1 = 5 + 6 * i + (j + 1) by omega, fwd_offset_body c fwd i (j + 1) room (by omega)]
  unfold MemReloc.imageAddress
  rw [show Generated.armcert_memmove_entry + 56 + 4 * (j + 1) = (Generated.armcert_memmove_entry + 56 + 4 * j) + 4 by omega]
  simp only [BitVec.ofNat_add, BitVec.add_assoc]

include fwd in
/-- A zero-draw step advances EnvM at a non-memory index of a forward iteration. -/
theorem fwd_advance0 (i j : Nat) (room : i < c.n) (hj : 2 ≤ j) (hj6 : j < 6) (x fin : NativeState)
    (env : EnvM c catalogue entry (5 + 6 * i + j) x)
    (core : ReleaseProfile.DefaultCurrent.CurrentInv c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
      (offset c) c.budget (5 + 6 * i + j + 1) catalogue fin)
    (choice : NativeMteTagCheck.ChoiceDelta x fin 0) : EnvM c catalogue entry (5 + 6 * i + j + 1) fin :=
  ReleaseProfile.DefaultRuntime.InvG.advance env core True.intro ⟨0, choice, Nat.le_refl 0⟩
    (by rw [fwd, fwd_movePast_step c.n i j room hj6, if_neg (by omega)]; exact Nat.le_refl _)

end env

/-! ## Memory facts (loops CopyFacts over the memmove context) -/

theorem load_facts_m (c : Context) (i : Nat) (room : i < c.n) (x : NativeState) (byte : BitVec 8)
    (cursor : x.regs.gpr[1] = c.s + BitVec.ofNat 64 i)
    (present : x.mem[c.srcPA i]? = some byte) :
    ArmCertMemPipe.LdrbU.Facts c.spec c.config c.rows c.mapping c.consumer 0#12 1#5 x := by
  obtain ⟨pa, mapped, mmio, outside⟩ := source_mapped c i room
  have addr : MemClass.LdrbU.addr x 1#5 0#12 = c.s + BitVec.ofNat 64 i := by
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

theorem store_facts_m (c : Context) (i : Nat) (room : i < c.n) (x : NativeState)
    (cursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i) :
    ArmCertMemPipe.StrbU.Facts c.spec c.mapping c.consumer (DestinationPA c.mapping c.d c.n) 0#12 3#5 x := by
  obtain ⟨pa, mapped, mmio, outside⟩ := dest_mapped c i room
  have addr : MemClass.StrbU.addr x 3#5 0#12 = c.d + BitVec.ofNat 64 i := by
    rw [CopyNative.store_addr_zero]; exact cursor
  refine ⟨pa, by rw [addr]; exact mapped, mmio, ?_, ?_, ?_⟩
  · intro j bounded
    have : j = 0 := by omega
    subst j
    simpa using outside
  · intro j bounded
    have : j = 0 := by omega
    subst j
    exact ⟨i, room, by simpa using mapped⟩
  · intro acc shape
    rw [addr]
    exact SpanMap.data_permitted (spans c.d c.s c.n)
      (Image.codeVAs c.base Generated.imageStart Generated.imageWords) c.mapping (rowsFootprint c.spec.imageRows).byte
      (destSpan c.d c.n) (by simp [spans]) i room acc shape

theorem final_frame_m (c : Context) (entry fin : NativeState)
    (bytes : Bytes.CopyPrefix c.srcPA c.dstPA (Aux.memoryView entry) (Aux.memoryView fin) c.n c.n) :
    ∀ pa, ¬ DestinationPA c.mapping c.d c.n pa → fin.mem[pa]? = entry.mem[pa]? := by
  intro pa outside
  apply bytes.frame pa
  rintro ⟨i, room, same⟩
  obtain ⟨p, mapped, _, _⟩ := dest_mapped c i room
  have physical : c.dstPA i = p.toNat := by simp only [Context.dstPA, mapped, Option.getD_some]
  apply outside
  refine ⟨i, room, ?_⟩
  rw [mapped, ← physical, same]

/-! ## LDRB/STRB pair (k = 5 + 6i, 6 + 6i) -/

theorem memory_pair_m (real : Type) [Sail.SailReal real] (c : Context) (fwd : c.path = .forward)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState) (nodup : (c.spec.logicalRows.map (·.logical)).Nodup)
    (i : Nat) (room : i < c.n)
    (x : NativeState) (byte : BitVec 8) (env : EnvM c catalogue entry (5 + 6 * i) x)
    (sourceCursor : x.regs.gpr[1] = c.s + BitVec.ofNat 64 i)
    (destCursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i)
    (value : x.mem[c.srcPA i]? = some byte) :
    ∃ y, Uget.Chain.modelRun real 2 x = .ok () y ∧ EnvM c catalogue entry (5 + 6 * i + 2) y ∧
      Bytes.SingleWrite (Aux.memoryView x) (Aux.memoryView y) (c.dstPA i) byte ∧
      y.regs.gpr = x.regs.gpr.set 4 (byte.setWidth 64) ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧
      NativeEntry.Effects.Frame {} x.regs y.regs ∧ Route7Copy.Covered real (PcOkM c) 2 x ∧
      Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) 2 (5 + 6 * i) x := by
  let k := 5 + 6 * i
  have past0 : movePast c.path c.n k = 2 * i := by rw [fwd]; exact fwd_movePast_body c.n i (by omega)
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.LdrbUoff.selected 4#5 1#5 0#12) x := by
    exact fetch_index_m c catalogue entry k 30 x env (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry, Nat.add_zero] using
        pc_fwd c fwd catalogue entry i 0 room (by decide) x env)
  have allowed0 := ReleaseProfile.DefaultRuntime.current_status env (by omega : movePast c.path c.n k < 2 * c.n)
  obtain ⟨a, run0, ms0, frame0⟩ :=
    Route7Mem.DefaultLdrbU.routeF real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget k catalogue
      (by simpa only [Nat.add_zero] using fwd_body_room c fwd i 0 room (by decide)) c.page
      (by simpa only [Nat.add_zero] using fwd_body_aligned c fwd i 0 room (by decide))
      (NativeEntryBodyDispatch.LdrbUoff.selected 4#5 1#5 0#12) 633 (by decide) 0#12 1#5 4#5 (by decide) (by decide)
      (fun pc t see => NativeEntryBodyDispatch.LdrbUoff.dispatch_at real pc 4#5 1#5 0#12 t (by simpa using see))
      (LoopNative.Encoding.LdrbU_noEret 4#5 1#5 0#12) x env.core allowed0 (load_facts_m c i room x byte sourceCursor value)
      (by simpa only [Nat.add_zero] using fwd_next_placed c fwd catalogue entry i 0 room (by decide) x env) fetch0 nodup
  have env1 : EnvM c catalogue entry (k + 1) a :=
    ReleaseProfile.DefaultRuntime.InvG.advance env ms0.current True.intro ms0.choice
      (by rw [fwd, show k + 1 = 5 + 6 * i + 0 + 1 by omega, fwd_movePast_step c.n i 0 room (by omega)]; simp [k])
  obtain ⟨sourcePA, loadedByte, mapped0, present0, gpr0, sp0, memory0⟩ :=
    NativeBytes.load_payload c.mapping 0#12 1#5 4#5 x a ms0.pay
  have addr0 : MemClass.LdrbU.addr x 1#5 0#12 = c.s + BitVec.ofNat 64 i := by
    rw [CopyNative.load_addr_zero]; exact sourceCursor
  have physical0 : c.srcPA i = sourcePA.toNat := by
    simp only [Context.srcPA, ← addr0, mapped0, Option.getD_some]
  have byteEq : loadedByte = byte := by
    apply Option.some.inj
    exact present0.symm.trans (by simpa only [physical0] using value)
  subst loadedByte
  change a.regs.gpr = x.regs.gpr.set 4 (byte.setWidth 64) at gpr0
  have dest1 : a.regs.gpr[3] = c.d + BitVec.ofNat 64 i := by
    rw [gpr0]
    simpa using destCursor
  have env1' : EnvM c catalogue entry (5 + 6 * i + 1) a := env1
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.StrbUoff.selected 4#5 3#5 0#12) a := by
    exact fetch_index_m c catalogue entry (k + 1) 31 a env1 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry] using
        pc_fwd c fwd catalogue entry i 1 room (by decide) a env1')
  have codeD : ImageTableSeparated codeScope c.base c.mapping (DestinationPA c.mapping c.d c.n) := by
    intro off pa inside mapped target
    exact c.codeWrite off inside pa mapped target
  have past1 : movePast c.path c.n (k + 1) = 2 * i + 1 := by
    rw [fwd, show k + 1 = 5 + 6 * i + 0 + 1 by omega, fwd_movePast_step c.n i 0 room (by omega)]
    rw [fwd] at past0; simp [past0, k]
  have allowed1 := ReleaseProfile.DefaultRuntime.current_status env1 (by omega : movePast c.path c.n (k + 1) < 2 * c.n)
  obtain ⟨y, run1, ms1, frame1⟩ :=
    Route7Mem.DefaultStrbU.routeF real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (k + 1) catalogue
      (fwd_body_room c fwd i 1 room (by decide)) c.page (fwd_body_aligned c fwd i 1 room (by decide))
      (NativeEntryBodyDispatch.StrbUoff.selected 4#5 3#5 0#12) 651 (by decide) 0#12 3#5 4#5 (by decide) (by decide)
      (fun pc t see => NativeEntryBodyDispatch.StrbUoff.dispatch_at real pc 4#5 3#5 0#12 t (by simpa using see))
      (LoopNative.Encoding.StrbU_noEret 4#5 3#5 0#12) (DestinationPA c.mapping c.d c.n) codeD a env1.core allowed1
      (store_facts_m c i room a dest1) (fwd_next_placed c fwd catalogue entry i 1 room (by decide) a env1') fetch1 nodup
  have env2 : EnvM c catalogue entry (5 + 6 * i + 2) y := by
    have adv := ReleaseProfile.DefaultRuntime.InvG.advance env1 ms1.current True.intro ms1.choice
      (by rw [fwd, show k + 1 + 1 = 5 + 6 * i + 1 + 1 by omega, show k + 1 = 5 + 6 * i + 1 by omega,
            fwd_movePast_step c.n i 1 room (by omega)]; simp)
    simpa only [show k + 1 + 1 = 5 + 6 * i + 2 by omega] using adv
  obtain ⟨destPA, mapped1, written, gpr1, sp1⟩ := NativeBytes.store_payload c.mapping 0#12 3#5 4#5 a y ms1.pay
  have addr1 : MemClass.StrbU.addr a 3#5 0#12 = c.d + BitVec.ofNat 64 i := by
    rw [CopyNative.store_addr_zero]; exact dest1
  have physical1 : c.dstPA i = destPA.toNat := by
    simp only [Context.dstPA, ← addr1, mapped1, Option.getD_some]
  have storedByte : a.regs.gpr[4].setWidth 8 = byte := by
    rw [gpr0, Vector.getElem_set_self]
    exact NativeBytes.zeroExtend_lowByte byte
  change Bytes.SingleWrite (Aux.memoryView a) (Aux.memoryView y) destPA.toNat (a.regs.gpr[4].setWidth 8) at written
  rw [← physical1, storedByte] at written
  have sameView : Aux.memoryView a = Aux.memoryView x := by unfold Aux.memoryView; rw [memory0]
  rw [sameView] at written
  have runY : Uget.Chain.modelRun real 2 x = .ok () y := by simp only [Uget.Chain.modelRun, run0, run1]
  refine ⟨y, runY, env2, written, gpr1.trans gpr0, sp1.trans sp0, frame0.trans frame1, ?_, ?_⟩
  intro m hm
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with hm | hm | hm <;> subst hm
  · exact ⟨x, rfl, pcOk_of_env_m c catalogue entry _ x env⟩
  · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env_m c catalogue entry _ a env1'⟩
  · exact ⟨y, runY, pcOk_of_env_m c catalogue entry _ y env2⟩
  -- trace (loops CT0): LDRB s + i, STRB d + i
  have ev0 := ms0.events
  rw [addr0, ← recs_fwd_ldrb c fwd i room] at ev0
  have ev1 := ms1.events
  rw [addr1, ← recs_fwd_strb c fwd i room] at ev1
  exact Route7Trace.traced_append real c.spec c.mapping (recsOfM c) (pcOfM c) 1 1 (5 + 6 * i) x a (Route7Trace.run_one real x a run0)
    (Route7Trace.traced_one real c.spec c.mapping (recsOfM c) (pcOfM c) _ x a run0 (pcAt_of_env_m c catalogue entry _ x env) ev0 frame0)
    (Route7Trace.traced_one real c.spec c.mapping (recsOfM c) (pcOfM c) _ a y run1 (pcAt_of_env_m c catalogue entry _ a env1') ev1 frame1)

/-! ## CBNZ back-edge (k = 10 + 6i, word 560 → 540 / 564) -/

section branch
variable (c : Context) (fwd : c.path = .forward) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
include fwd

theorem fwd_branch_target (i : Nat) (room : i < c.n) (x : NativeState) (env : EnvM c catalogue entry (5 + 6 * i + 5) x) :
    LoopNative.Cbnz64.target CopyNative.backImmediate x = c.base + 540#64 := by
  rw [LoopNative.Cbnz64.target, CopyNative.back_delta, pc_fwd c fwd catalogue entry i 5 room (by decide) x env]
  unfold MemReloc.imageAddress
  change c.base + 560#64 + BitVec.ofInt 64 (-20) = c.base + 540#64
  bv_omega

theorem fwd_branch_low (i : Nat) (room : i < c.n) (x : NativeState) (env : EnvM c catalogue entry (5 + 6 * i + 5) x) :
    (LoopNative.Cbnz64.target CopyNative.backImmediate x).toNat < 2 ^ 55 := by
  rw [fwd_branch_target c fwd catalogue entry i room x env]
  have low := c.low
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem fwd_branch_taken_placed (i : Nat) (again : i + 1 < c.n) (x : NativeState)
    (env : EnvM c catalogue entry (5 + 6 * i + 5) x) :
    LoopNative.Cbnz64.target CopyNative.backImmediate x = c.base + offset c (5 + 6 * i + 5 + 1) := by
  rw [fwd_branch_target c fwd catalogue entry i (by omega) x env, fwd_offset_after c fwd i (by omega), if_pos again]
  rfl

theorem fwd_branch_not_placed (i : Nat) (last : i + 1 = c.n) (room : i < c.n) (x : NativeState)
    (env : EnvM c catalogue entry (5 + 6 * i + 5) x) :
    x.regs._PC + 4#64 = c.base + offset c (5 + 6 * i + 5 + 1) := by
  rw [pc_fwd c fwd catalogue entry i 5 room (by decide) x env, fwd_offset_after c fwd i room,
    if_neg (by omega : ¬ i + 1 < c.n)]
  unfold MemReloc.imageAddress
  change c.base + 560#64 + 4#64 = c.base + 564#64
  bv_omega

attribute [local instance 10] Classical.propDecidable in
theorem fwd_branch_step (real : Type) [Sail.SailReal real] (nodup : (c.spec.logicalRows.map (·.logical)).Nodup)
    (i : Nat) (room : i < c.n)
    (x : NativeState) (env : EnvM c catalogue entry (5 + 6 * i + 5) x)
    (remaining : x.regs.gpr[2].toNat = c.n - (i + 1)) :
    ∃ y, modelStep real x = .ok () y ∧ EnvM c catalogue entry (5 + 6 * i + 6) y ∧ y.mem = x.mem ∧
      y.regs.gpr = x.regs.gpr ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧ NativeEntry.Effects.Frame {} x.regs y.regs ∧
      StepEvents.EvShape c.spec c.mapping [] x y := by
  have fetch : FetchObligations c.spec c.config c.rows c.mapping (Route7Cbnz.Tail.W 2#5 CopyNative.backImmediate) x := by
    exact fetch_index_m c catalogue entry (5 + 6 * i + 5) 35 x env (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry] using
        pc_fwd c fwd catalogue entry i 5 room (by decide) x env)
  have placed : (if ReleaseProfile.HeapCbzAction.cbzCond x 1#1 1#1 2#5
      then x.regs._PC + sign_extend (CopyNative.backImmediate ++ 0#2) 64 else x.regs._PC + 4#64) =
      c.base + offset c (5 + 6 * i + 5 + 1) := by
    by_cases again : i + 1 < c.n
    · have nonzero : x.regs.gpr[(GPRSummary.key (2#5).toNat).val] ≠ 0#64 := by
        intro same
        have zero := congrArg BitVec.toNat same
        change x.regs.gpr[2].toNat = (0#64).toNat at zero
        simp only [BitVec.toNat_ofNat] at zero
        omega
      rw [if_pos ((Route7Copy.cbnz_cond_iff x).2 nonzero)]
      change LoopNative.Cbnz64.target CopyNative.backImmediate x = _
      exact fwd_branch_taken_placed c fwd catalogue entry i again x env
    · have zero : x.regs.gpr[(GPRSummary.key (2#5).toNat).val] = 0#64 := by
        apply BitVec.eq_of_toNat_eq
        change x.regs.gpr[2].toNat = 0
        omega
      rw [if_neg (fun h => (Route7Copy.cbnz_cond_iff x).1 h zero)]
      exact fwd_branch_not_placed c fwd catalogue entry i (by omega) room x env
  obtain ⟨y, run, inv', holds, memory, sys, z, dit, kept, choice, ev⟩ :=
    Route7Steps.cbnz64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (5 + 6 * i + 5) catalogue
      (fwd_body_room c fwd i 5 room (by decide)) c.page (fwd_body_aligned c fwd i 5 room (by decide))
      2#5 CopyNative.backImmediate x env.core nodup (fwd_branch_low c fwd catalogue entry i room x env) _ rfl placed fetch
  have env' : EnvM c catalogue entry (5 + 6 * i + 6) y := by
    have adv := fwd_advance0 c fwd catalogue entry i 5 room (by omega) (by omega) x y env inv' choice
    simpa only [show 5 + 6 * i + 5 + 1 = 5 + 6 * i + 6 by omega] using adv
  exact ⟨y, run, env', memory, ValueFacts.nil_gpr x y holds, ValueFacts.nil_sp x y holds, kept, ev⟩

end branch

/-! ## ADD/ADD/SUB/CBNZ tail (k = 7 + 6i .. 10 + 6i) -/

theorem fwd_tail (real : Type) [Sail.SailReal real] (c : Context) (fwd : c.path = .forward)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState) (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (i : Nat) (room : i < c.n)
    (x : NativeState) (env : EnvM c catalogue entry (5 + 6 * i + 2) x)
    (sourceCursor : x.regs.gpr[1] = c.s + BitVec.ofNat 64 i)
    (destCursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i)
    (remaining : x.regs.gpr[2].toNat = c.n - i) :
    ∃ y, Uget.Chain.modelRun real 4 x = .ok () y ∧ EnvM c catalogue entry (5 + 6 * (i + 1)) y ∧
      y.regs.gpr = ((x.regs.gpr.set 1 (c.s + BitVec.ofNat 64 (i + 1))).set 3
        (c.d + BitVec.ofNat 64 (i + 1))).set 2 (x.regs.gpr[2] - 1#64) ∧
      y.regs.gpr[2].toNat = c.n - (i + 1) ∧ y.mem = x.mem ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧
      NativeEntry.Effects.Frame {} x.regs y.regs ∧ Route7Copy.Covered real (PcOkM c) 4 x ∧
      Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) 4 (5 + 6 * i + 2) x := by
  let k := 5 + 6 * i
  have fetch2 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.AddImm64.selected 1#5 1#5 1#12) x := by
    exact fetch_index_m c catalogue entry (k + 2) 32 x env (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry] using
        pc_fwd c fwd catalogue entry i 2 room (by decide) x env)
  obtain ⟨a, run2, core3, values2, memory2, _, _, _, frame2, choice2, ev2⟩ :=
    Route7Steps.addImm64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (k + 2) catalogue
      (fwd_body_room c fwd i 2 room (by decide)) c.page (fwd_body_aligned c fwd i 2 room (by decide))
      1#5 1#5 1#12 (by decide) (by decide) x env.core nodup
      (fwd_next_placed c fwd catalogue entry i 2 room (by decide) x env) fetch2
  have env3 : EnvM c catalogue entry (5 + 6 * i + 3) a :=
    fwd_advance0 c fwd catalogue entry i 2 room (by omega) (by omega) x a env core3 choice2
  obtain ⟨gpr2, sp2⟩ := ValueFacts.add 1#5 1#5 1#12 x a values2
  change a.regs.gpr = x.regs.gpr.set 1 (x.regs.gpr[1] + 1#64) at gpr2
  have fetch3 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.AddImm64.selected 3#5 3#5 1#12) a := by
    exact fetch_index_m c catalogue entry (k + 3) 33 a env3 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry] using
        pc_fwd c fwd catalogue entry i 3 room (by decide) a env3)
  obtain ⟨b, run3, core4, values3, memory3, _, _, _, frame3, choice3, ev3⟩ :=
    Route7Steps.addImm64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (k + 3) catalogue
      (fwd_body_room c fwd i 3 room (by decide)) c.page (fwd_body_aligned c fwd i 3 room (by decide))
      3#5 3#5 1#12 (by decide) (by decide) a env3.core nodup
      (fwd_next_placed c fwd catalogue entry i 3 room (by decide) a env3) fetch3
  have env4 : EnvM c catalogue entry (5 + 6 * i + 4) b :=
    fwd_advance0 c fwd catalogue entry i 3 room (by omega) (by omega) a b env3 core4 choice3
  obtain ⟨gpr3, sp3⟩ := ValueFacts.add 3#5 3#5 1#12 a b values3
  change b.regs.gpr = a.regs.gpr.set 3 (a.regs.gpr[3] + 1#64) at gpr3
  have fetch4 : FetchObligations c.spec c.config c.rows c.mapping
      (Route7Sub.Dispatch.selected 2#5 2#5 1#12) b := by
    exact fetch_index_m c catalogue entry (k + 4) 34 b env4 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memmove_entry] using
        pc_fwd c fwd catalogue entry i 4 room (by decide) b env4)
  obtain ⟨d, run4, core5, values4, memory4, _, _, _, frame4, choice4, ev4⟩ :=
    Route7Steps.subImm64E real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (k + 4) catalogue
      (fwd_body_room c fwd i 4 room (by decide)) c.page (fwd_body_aligned c fwd i 4 room (by decide))
      2#5 2#5 1#12 (by decide) (by decide) b env4.core nodup
      (fwd_next_placed c fwd catalogue entry i 4 room (by decide) b env4) fetch4
  have env5 : EnvM c catalogue entry (5 + 6 * i + 5) d :=
    fwd_advance0 c fwd catalogue entry i 4 room (by omega) (by omega) b d env4 core5 choice4
  obtain ⟨gpr4, sp4⟩ := ValueFacts.sub 2#5 2#5 1#12 b d values4
  change d.regs.gpr = b.regs.gpr.set 2 (b.regs.gpr[2] - 1#64) at gpr4
  have counterB : b.regs.gpr[2] = x.regs.gpr[2] := by rw [gpr3, gpr2]; simp
  have counterD : d.regs.gpr[2] = x.regs.gpr[2] - 1#64 := by rw [gpr4, Vector.getElem_set_self, counterB]
  have positive : 0 < x.regs.gpr[2].toNat := by omega
  have remainingD : d.regs.gpr[2].toNat = c.n - (i + 1) := by
    rw [counterD, Schedule.counter_pred _ positive, remaining]
    omega
  obtain ⟨y, run5, env6, memory5, gpr5, sp5, frame5, ev5⟩ :=
    fwd_branch_step c fwd catalogue entry real nodup i room d env5 remainingD
  have advance (base : BitVec 64) : base + BitVec.ofNat 64 i + 1#64 = base + BitVec.ofNat 64 (i + 1) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  have gpr : y.regs.gpr = ((x.regs.gpr.set 1 (c.s + BitVec.ofNat 64 (i + 1))).set 3
      (c.d + BitVec.ofNat 64 (i + 1))).set 2 (x.regs.gpr[2] - 1#64) := by
    rw [gpr5, gpr4, gpr3, gpr2]
    simp [sourceCursor, destCursor, advance]
  rw [show 5 + 6 * i + 6 = 5 + 6 * (i + 1) by omega] at env6
  have runY : Uget.Chain.modelRun real 4 x = .ok () y := by simp only [Uget.Chain.modelRun, run2, run3, run4, run5]
  refine ⟨y, runY, env6, gpr, ?_, memory5.trans (memory4.trans (memory3.trans memory2)),
    sp5.trans (sp4.trans (sp3.trans sp2)), ((frame2.trans frame3).trans frame4).trans frame5, ?_, ?_⟩
  · rw [gpr5]
    exact remainingD
  · -- coverage (loops)
    intro m hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with hm | hm | hm | hm | hm <;> subst hm
    · exact ⟨x, rfl, pcOk_of_env_m c catalogue entry _ x env⟩
    · exact ⟨a, by simp only [Uget.Chain.modelRun, run2], pcOk_of_env_m c catalogue entry _ a env3⟩
    · exact ⟨b, by simp only [Uget.Chain.modelRun, run2, run3], pcOk_of_env_m c catalogue entry _ b env4⟩
    · exact ⟨d, by simp only [Uget.Chain.modelRun, run2, run3, run4], pcOk_of_env_m c catalogue entry _ d env5⟩
    · exact ⟨y, runY, pcOk_of_env_m c catalogue entry _ y env6⟩
  · -- trace (loops CT0): ADD / ADD / SUB / CBNZ, no data records
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with hj | hj | hj | hj <;> subst hj
    · refine ⟨x, a, rfl, run2, ?_, ?_⟩
      · rw [show 5 + 6 * i + 2 + 0 = 5 + 6 * i + 2 by omega]; exact pcAt_of_env_m c catalogue entry _ x env
      · rw [recs_fwd_nil c fwd (5 + 6 * i + 2 + 0) (by omega) (by omega)]; exact ⟨ev2, frame2⟩
    · refine ⟨a, b, by simp only [Uget.Chain.modelRun, run2], run3, ?_, ?_⟩
      · rw [show 5 + 6 * i + 2 + 1 = 5 + 6 * i + 3 by omega]; exact pcAt_of_env_m c catalogue entry _ a env3
      · rw [recs_fwd_nil c fwd (5 + 6 * i + 2 + 1) (by omega) (by omega)]; exact ⟨ev3, frame3⟩
    · refine ⟨b, d, by simp only [Uget.Chain.modelRun, run2, run3], run4, ?_, ?_⟩
      · rw [show 5 + 6 * i + 2 + 2 = 5 + 6 * i + 4 by omega]; exact pcAt_of_env_m c catalogue entry _ b env4
      · rw [recs_fwd_nil c fwd (5 + 6 * i + 2 + 2) (by omega) (by omega)]; exact ⟨ev4, frame4⟩
    · refine ⟨d, y, by simp only [Uget.Chain.modelRun, run2, run3, run4], run5, ?_, ?_⟩
      · rw [show 5 + 6 * i + 2 + 3 = 5 + 6 * i + 5 by omega]; exact pcAt_of_env_m c catalogue entry _ d env5
      · rw [recs_fwd_nil c fwd (5 + 6 * i + 2 + 3) (by omega) (by omega)]; exact ⟨ev5, frame5⟩

/-! ## Forward iteration and exit -/

/-- Forward loop header at iteration i (k = 5 + 6i): loops' Header shape over EnvM. -/
structure HeaderF (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (i : Nat) (x : NativeState) : Prop where
  positive : 0 < c.n
  bound : i ≤ c.n
  environment : EnvM c catalogue entry (5 + 6 * i) x
  dest : x.regs.gpr[0] = c.d
  sourceCursor : x.regs.gpr[1] = c.s + BitVec.ofNat 64 i
  destCursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i
  remaining : x.regs.gpr[2].toNat = c.n - i
  link : x.regs.gpr[30] = c.returnPC
  saved : ∀ r : Fin 31, 6 ≤ r.val → x.regs.gpr[r.val] = entry.regs.gpr[r.val]
  sp : x.regs.SP_EL0 = entry.regs.SP_EL0
  protectedRegs : NativeEntry.Effects.Frame {} entry.regs x.regs
  bytes : Bytes.CopyPrefix c.srcPA c.dstPA (Aux.memoryView entry) (Aux.memoryView x) c.n i

theorem fwd_body (real : Type) [Sail.SailReal real] (c : Context) (fwd : c.path = .forward)
    (lt : c.d.toNat < c.s.toNat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry x : NativeState)
    (i : Nat) (room : i < c.n) (byte : BitVec 8) (header : HeaderF c catalogue entry i x)
    (value : Aux.memoryView x (c.srcPA i) = some byte) :
    ∃ y, Uget.Chain.modelRun real 6 x = .ok () y ∧
      Bytes.SingleWrite (Aux.memoryView x) (Aux.memoryView y) (c.dstPA i) byte ∧ HeaderF c catalogue entry (i + 1) y ∧
      Route7Copy.Covered real (PcOkM c) 6 x ∧ Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) 6 (5 + 6 * i) x := by
  obtain ⟨a, pairRun, env2, written, gprPair, spPair, framePair, pairCov, pairTr⟩ :=
    memory_pair_m real c fwd catalogue entry nodup i room x byte header.environment header.sourceCursor header.destCursor value
  have sourceA : a.regs.gpr[1] = c.s + BitVec.ofNat 64 i := by
    rw [gprPair]
    simpa using header.sourceCursor
  have destA : a.regs.gpr[3] = c.d + BitVec.ofNat 64 i := by
    rw [gprPair]
    simpa using header.destCursor
  have remainingA : a.regs.gpr[2].toNat = c.n - i := by
    rw [gprPair]
    simpa using header.remaining
  obtain ⟨y, restRun, env6, gprRest, remaining, memory, spRest, frameRest, restCov, restTr⟩ :=
    fwd_tail real c fwd catalogue entry nodup i room a env2 sourceA destA remainingA
  have finalWritten := NativeBytes.write_after_memory_frames
    (before := x) (load := x) (store := a) (after := y) rfl written memory
  -- overlap: memcpy's disjointness is replaced by `forward_future` (d <u s ⇒ later source bytes ≠ dest byte i)
  have copied := Bytes.copyPrefix_succ header.bytes room value finalWritten
    (fun j prior => dest_distinct c i j room (by omega) (by omega))
    (fun j later bounded => forward_future c lt i j room later bounded)
  refine ⟨y, Aux.modelRun_append real 2 4 x a y pairRun restRun, finalWritten,
    ⟨header.positive, by omega, env6, ?_, ?_, ?_, remaining, ?_, ?_,
    spRest.trans (spPair.trans header.sp), (header.protectedRegs.trans framePair).trans frameRest, copied⟩,
    Route7Copy.covered_append real (PcOkM c) 2 4 x a pairRun pairCov restCov,
    Route7Trace.traced_append real c.spec c.mapping (recsOfM c) (pcOfM c) 2 4 (5 + 6 * i) x a pairRun pairTr restTr⟩
  · rw [gprRest, gprPair]
    simpa using header.dest
  · rw [gprRest]
    simp
  · rw [gprRest]
    simp
  · rw [gprRest, gprPair]
    simpa using header.link
  · intro r saved
    have n1 : 1 ≠ r.val := by omega
    have n2 : 2 ≠ r.val := by omega
    have n3 : 3 ≠ r.val := by omega
    have n4 : 4 ≠ r.val := by omega
    rw [gprRest, gprPair]
    simpa [Vector.getElem_set, n1, n2, n3, n4] using header.saved r saved

/-- Final RET of the forward path (k = 5 + 6n, word 564) with the complete MovePost. -/
theorem fwd_exit (real : Type) [Sail.SailReal real] (c : Context) (fwd : c.path = .forward)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry x : NativeState)
    (header : HeaderF c catalogue entry c.n x) :
    ∃ y, Uget.Chain.modelRun real 1 x = .ok () y ∧ y.regs._PC = c.returnPC ∧
      y.mem = x.mem ∧ MovePost c.mapping c.d c.s c.returnPC c.n entry y ∧ Route7Copy.Covered real (PcOkM c) 1 x ∧
      Route7Trace.Traced real c.spec c.mapping (recsOfM c) (pcOfM c) 1 (5 + 6 * c.n) x := by
  have fetch : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) x := by
    exact fetch_index_m c catalogue entry (5 + 6 * c.n) 36 x header.environment (by decide) (by
      rw [header.environment.core.v1.pc, fwd_offset_exit c fwd]
      rfl)
  obtain ⟨y, run, pc, holds, memory, _, _, _, kept, _, ev⟩ :=
    Route7Steps.retE real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) c.budget (5 + 6 * c.n) catalogue
      (by rw [fwd_budget c fwd]; omega) c.page
      (by rw [fwd_offset_exit c fwd]; decide) 30#5 (by decide) x header.environment.core nodup
      (by change x.regs.gpr[30].toNat < 2 ^ 55; rw [header.link]; have := c.returnLow; omega) fetch
  have gpr := ValueFacts.nil_gpr x y holds
  have sp := ValueFacts.nil_sp x y holds
  have abi := header.protectedRegs.trans kept
  have runY : Uget.Chain.modelRun real 1 x = .ok () y := by simp only [Uget.Chain.modelRun, run]
  refine ⟨y, runY, pc.trans header.link, memory, ⟨pc.trans header.link, ?_, ?_, ?_, ?_,
    sp.trans header.sp, LoopNative.MemoryFrame.vector abi rfl,
    LoopNative.MemoryFrame.fpcr abi rfl, LoopNative.MemoryFrame.fpsr abi rfl⟩,
    Route7Copy.covered_one real (PcOkM c) x y runY (pcOk_of_env_m c catalogue entry _ x header.environment)
      ⟨Or.inl (pc.trans header.link), CT1.Route7Word.imageWords_of_mem memory (pcOk_of_env_m c catalogue entry _ x header.environment).2⟩,
    Route7Trace.traced_one real c.spec c.mapping (recsOfM c) (pcOfM c) _ x y run (pcAt_of_env_m c catalogue entry _ x header.environment)
      (by rw [recs_fwd_nil c fwd (5 + 6 * c.n) (by omega) (by omega)]; exact ev) kept⟩
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
    exact final_frame_m c entry x header.bytes pa outside
  · intro r saved
    change y.regs.gpr[r.val] = entry.regs.gpr[r.val]
    rw [gpr]
    exact header.saved r saved

end Route7Move

#print axioms Route7Move.fwd_movePast_body
#print axioms Route7Move.memory_pair_m
#print axioms Route7Move.fwd_branch_step
#print axioms Route7Move.fwd_tail
#print axioms Route7Move.fwd_body
#print axioms Route7Move.fwd_exit
