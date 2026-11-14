-- Route 7 unit 3: copy iteration (body) and final RET (exit) over EnvR, ported from loops CopyBody/CopyExit.
import Route7Copy.Rest
import Route7Copy.Body
import ArmCertLoop.CopyExit
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 1024
set_option Elab.async false
namespace Route7Copy.CT2
open ArmCertLoop ArmCertLoop.CopyNative ArmCertLoop.ContractDraft

/-- CT2: memcpy register values at return beyond CopyPost (x1..x3 cursors; x3, x4 on the empty path; r >= 5 untouched). -/
def ExtraR (c : Context) (entry fin : NativeState) : Prop :=
  fin.regs.gpr[1] = c.s + BitVec.ofNat 64 c.n ∧ fin.regs.gpr[2].toNat = 0 ∧
  (0 < c.n → fin.regs.gpr[3] = c.d + BitVec.ofNat 64 c.n) ∧
  (c.n = 0 → fin.regs.gpr[3] = entry.regs.gpr[3] ∧ fin.regs.gpr[4] = entry.regs.gpr[4]) ∧
  (∀ r : Fin 31, 5 ≤ r.val → fin.regs.gpr[r.val] = entry.regs.gpr[r.val])

/-- loops' Header with the environment over EnvR (entry = the run entry, also the tag-status oracle entry). -/
structure HeaderR (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (i : Nat) (x : NativeState) : Prop where
  positive : 0 < c.n
  bound : i ≤ c.n
  environment : EnvR c catalogue entry (2 + 6 * i) x
  dest : x.regs.gpr[0] = c.d
  sourceCursor : x.regs.gpr[1] = c.s + BitVec.ofNat 64 i
  destCursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i
  remaining : x.regs.gpr[2].toNat = c.n - i
  link : x.regs.gpr[30] = c.returnPC
  saved : ∀ r : Fin 31, 5 ≤ r.val → x.regs.gpr[r.val] = entry.regs.gpr[r.val]
  sp : x.regs.SP_EL0 = entry.regs.SP_EL0
  protectedRegs : NativeEntry.Effects.Frame {} entry.regs x.regs
  bytes : Bytes.CopyPrefix c.srcPA c.dstPA (Aux.memoryView entry) (Aux.memoryView x) c.n i

theorem body_r (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry x : NativeState)
    (i : Nat) (room : i < c.n) (byte : BitVec 8) (header : HeaderR c catalogue entry i x)
    (value : Aux.memoryView x (c.srcPA i) = some byte) :
    ∃ y, Uget.Chain.modelRun real 6 x = .ok () y ∧
      Bytes.SingleWrite (Aux.memoryView x) (Aux.memoryView y) (c.dstPA i) byte ∧ HeaderR c catalogue entry (i + 1) y ∧
      Covered real (PcOk c) 6 x ∧ Route7Trace.Traced real c.spec c.mapping (recsOf c) (pcOf c) 6 (2 + 6 * i) x := by
  obtain ⟨a, pairRun, env2, written, gprPair, spPair, framePair, pairCov, pairTr⟩ :=
    memory_pair_r real c catalogue entry nodup i room x byte header.environment header.sourceCursor header.destCursor value
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
    arithmetic_tail_r real c catalogue entry nodup i room a env2 sourceA destA remainingA
  have finalWritten := NativeBytes.write_after_memory_frames
    (before := x) (load := x) (store := a) (after := y) rfl written memory
  have copied := Bytes.copyPrefix_succ header.bytes room value finalWritten
    (fun j prior => dest_distinct c i j room (by omega) (by omega))
    (fun j _ bounded => source_dest_distinct c i j room bounded)
  refine ⟨y, Aux.modelRun_append real 2 4 x a y pairRun restRun, finalWritten,
    ⟨header.positive, by omega, env6, ?_, ?_, ?_, remaining, ?_, ?_,
    spRest.trans (spPair.trans header.sp), (header.protectedRegs.trans framePair).trans frameRest, copied⟩,
    covered_append real (PcOk c) 2 4 x a pairRun pairCov restCov,
    Route7Trace.traced_append real c.spec c.mapping (recsOf c) (pcOf c) 2 4 (2 + 6 * i) x a pairRun pairTr restTr⟩
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

/-- Final RET over EnvR: return to returnPC with the complete memcpy functional/ABI postcondition. The exit route
lands outside the image, so no invariant is claimed after it (coverage only needs PC = returnPC there). -/
theorem exit_r (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (nodup : (c.spec.logicalRows.map (·.logical)).Nodup) (entry x : NativeState)
    (header : HeaderR c catalogue entry c.n x) :
    ∃ y, Uget.Chain.modelRun real 1 x = .ok () y ∧ y.regs._PC = c.returnPC ∧
      y.mem = x.mem ∧ (CopyPost c.mapping c.d c.s c.returnPC c.n entry y ∧ ExtraR c entry y) ∧ Route7Trace.Traced real c.spec c.mapping (recsOf c) (pcOf c) 1 (2 + 6 * c.n) x := by
  have nz : c.n ≠ 0 := by have := header.positive; omega
  have fetch : FetchObligations c.spec c.config c.rows c.mapping
      (ArmBridge.CruxGenGuarded.EntryBodyRet.W 30#5) x := by
    exact fetch_index_r c catalogue entry (2 + 6 * c.n) 8 x header.environment (by decide) (by
      rw [header.environment.core.v1.pc, offset_exit c header.positive]
      rfl)
  obtain ⟨y, run, pc, holds, memory, _, _, _, kept, _, ev⟩ :=
    Route7Steps.retE real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget (2 + 6 * c.n) catalogue
      (by simp only [Context.budget, Schedule.copySteps, if_neg nz]; omega) c.page
      (by rw [offset_exit c header.positive]; decide) 30#5 (by decide) x header.environment.core nodup
      (by change x.regs.gpr[30].toNat < 2 ^ 55; rw [header.link]; have := c.returnLow; omega) fetch
  have gpr := ValueFacts.nil_gpr x y holds
  have sp := ValueFacts.nil_sp x y holds
  have abi := header.protectedRegs.trans kept
  refine ⟨y, by simp only [Uget.Chain.modelRun, run], pc.trans header.link, memory, ⟨⟨pc.trans header.link, ?_, ?_, ?_, ?_,
    sp.trans header.sp, LoopNative.MemoryFrame.vector abi rfl,
    LoopNative.MemoryFrame.fpcr abi rfl, LoopNative.MemoryFrame.fpsr abi rfl⟩, ?_⟩,
    Route7Trace.traced_one real c.spec c.mapping (recsOf c) (pcOf c) _ x y run
      (pcAt_of_env c catalogue entry _ x header.environment) (by rw [recs_exit]; exact ev) kept⟩
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
    exact final_frame c entry x header.bytes pa outside
  · intro r saved
    change y.regs.gpr[r.val] = entry.regs.gpr[r.val]
    rw [gpr]
    exact header.saved r (by omega)
  · refine ⟨?_, ?_, fun _ => ?_, fun h => absurd h (by have := header.positive; omega), fun r hr => ?_⟩
    · change y.regs.gpr[1] = _; rw [gpr]; exact header.sourceCursor
    · change y.regs.gpr[2].toNat = 0; rw [gpr]; rw [header.remaining]; omega
    · change y.regs.gpr[3] = _; rw [gpr]; exact header.destCursor
    · change y.regs.gpr[r.val] = _; rw [gpr]; exact header.saved r hr

end Route7Copy.CT2
#print axioms Route7Copy.CT2.body_r
#print axioms Route7Copy.CT2.exit_r
