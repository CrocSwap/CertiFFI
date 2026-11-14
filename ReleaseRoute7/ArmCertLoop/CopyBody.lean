import ArmCertLoop.CopyPair
import ArmCertLoop.CopyRest
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.CopyNative

/-- One complete six-instruction memcpy iteration, from the original snapshot
invariant. Native execution, branch outcome, byte write, ABI and next header
are all derived internally. -/
theorem body (real : Type) [Sail.SailReal real] (c : Context) (entry x : NativeState)
    (i : Nat) (room : i < c.n) (byte : BitVec 8) (header : Header c entry i x)
    (value : Aux.memoryView x (c.srcPA i) = some byte) :
    ∃ y, Uget.Chain.modelRun real 6 x = .ok () y ∧
      Bytes.SingleWrite (Aux.memoryView x) (Aux.memoryView y) (c.dstPA i) byte ∧ Header c entry (i + 1) y := by
  obtain ⟨a, pairRun, env2, written, gprPair, spPair, framePair⟩ :=
    memory_pair real c i room x byte header.environment header.sourceCursor header.destCursor value
  have sourceA : a.regs.gpr[1] = c.s + BitVec.ofNat 64 i := by
    rw [gprPair]
    simpa using header.sourceCursor
  have destA : a.regs.gpr[3] = c.d + BitVec.ofNat 64 i := by
    rw [gprPair]
    simpa using header.destCursor
  have remainingA : a.regs.gpr[2].toNat = c.n - i := by
    rw [gprPair]
    simpa using header.remaining
  obtain ⟨y, restRun, env6, gprRest, remaining, memory, spRest, frameRest⟩ :=
    arithmetic_tail real c i room a env2 sourceA destA remainingA
  have finalWritten := NativeBytes.write_after_memory_frames
    (before := x) (load := x) (store := a) (after := y) rfl written memory
  have copied := Bytes.copyPrefix_succ header.bytes room value finalWritten
    (fun j prior => dest_distinct c i j room (by omega) (by omega))
    (fun j _ bounded => source_dest_distinct c i j room bounded)
  refine ⟨y, Aux.modelRun_append real 2 4 x a y pairRun restRun, finalWritten,
    header.positive, by omega, env6, ?_, ?_, ?_, remaining, ?_, ?_,
    spRest.trans (spPair.trans header.sp), (header.protectedRegs.trans framePair).trans frameRest, copied⟩
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

#print axioms body
end ArmCertLoop.CopyNative
