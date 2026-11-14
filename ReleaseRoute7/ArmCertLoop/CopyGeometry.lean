import ArmCertLoop.CopyFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.CopyNative
open ContractDraft

theorem dest_distinct (c : Context) (i j : Nat) (ir : i < c.n) (jr : j < c.n) (different : j ≠ i) :
    c.dstPA j ≠ c.dstPA i := by
  obtain ⟨pa, ma, _, _⟩ := dest_mapped c j jr
  obtain ⟨pb, mb, _, _⟩ := dest_mapped c i ir
  apply SpanMap.mapped_different c.mapping (spans c.d c.s c.n) c.injective _ _
    ⟨destSpan c.d c.n, by simp [spans], j, jr, rfl⟩
    ⟨destSpan c.d c.n, by simp [spans], i, ir, rfl⟩ ⟨pa.toNat, ma⟩ ⟨pb.toNat, mb⟩
  intro same
  have equal := congrArg BitVec.toNat same
  rw [SpanMap.byteVA_toNat (destSpan c.d c.n) c.destObject j jr,
    SpanMap.byteVA_toNat (destSpan c.d c.n) c.destObject i ir] at equal
  exact different (by omega)

theorem source_dest_distinct (c : Context) (i j : Nat) (ir : i < c.n) (jr : j < c.n) :
    c.srcPA j ≠ c.dstPA i := by
  obtain ⟨pa, ma, _, _⟩ := source_mapped c j jr
  obtain ⟨pb, mb, _, _⟩ := dest_mapped c i ir
  apply SpanMap.mapped_different c.mapping (spans c.d c.s c.n) c.injective _ _
    ⟨sourceSpan c.s c.n, by simp [spans], j, jr, rfl⟩
    ⟨destSpan c.d c.n, by simp [spans], i, ir, rfl⟩ ⟨pa.toNat, ma⟩ ⟨pb.toNat, mb⟩
  intro same
  have equal := congrArg BitVec.toNat same
  rw [SpanMap.byteVA_toNat (sourceSpan c.s c.n) c.sourceObject j jr,
    SpanMap.byteVA_toNat (destSpan c.d c.n) c.destObject i ir] at equal
  have disjoint := c.disjoint
  simp only [sourceSpan, destSpan] at equal
  omega

theorem final_frame (c : Context) (entry fin : NativeState)
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

theorem body_cost_room (c : Context) (i j : Nat) (room : i < c.n) (slot : j < 6) :
    2 + 6 * i + j < Schedule.copySteps c.n := by
  have nz : c.n ≠ 0 := by omega
  simp only [Schedule.copySteps, if_neg nz]
  omega

theorem budget_enough (c : Context) : Schedule.copySteps c.n ≤ c.budget := Nat.le_add_right _ _

theorem body_room (c : Context) (i j : Nat) (room : i < c.n) (slot : j < 6) :
    2 + 6 * i + j < c.budget := Nat.lt_of_lt_of_le (body_cost_room c i j room slot) (budget_enough c)

theorem offset_body (c : Context) (i j : Nat) (room : i < c.n) (slot : j < 6) :
    offset c.base c.returnPC c.n (2 + 6 * i + j) =
      BitVec.ofNat 64 (Generated.armcert_memcpy_entry + 8 + 4 * j) := by
  have index : 2 + 6 * i + j ≠ Schedule.copySteps c.n := by have := body_cost_room c i j room slot; omega
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg index, Schedule.copy_loop_offset c.n i j room slot]
  congr 1
  omega

theorem body_aligned (c : Context) (i j : Nat) (room : i < c.n) (slot : j < 6) :
    (offset c.base c.returnPC c.n (2 + 6 * i + j)).toNat % 4 = 0 := by
  rw [offset_body c i j room slot]
  have bound : Generated.armcert_memcpy_entry + 8 + 4 * j < 2 ^ 64 := by
    simp only [Generated.armcert_memcpy_entry]; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Generated.armcert_memcpy_entry]
  omega

theorem body_next_placed (c : Context) (i j : Nat) (room : i < c.n) (slot : j < 5)
    (x : NativeState) (env : Env c (2 + 6 * i + j) x) :
    x.regs._PC + 4#64 = c.base + offset c.base c.returnPC c.n (2 + 6 * i + j + 1) := by
  rw [pc_body c i j room (by omega) x env]
  have index : 2 + 6 * i + j + 1 = 2 + 6 * i + (j + 1) := by omega
  rw [index, offset_body c i (j + 1) room (by omega)]
  unfold MemReloc.imageAddress
  have indexWord : Generated.armcert_memcpy_entry + 8 + 4 * (j + 1) =
      (Generated.armcert_memcpy_entry + 8 + 4 * j) + 4 := by omega
  rw [indexWord]
  simp only [BitVec.ofNat_add, BitVec.add_assoc]

def backImmediate : BitVec 19 := BitVec.ofInt 19 (-5)

theorem back_delta : sign_extend (backImmediate +++ 0#2) 64 = BitVec.ofInt 64 (-20) := by decide

theorem branch_target (c : Context) (i : Nat) (room : i < c.n) (x : NativeState)
    (env : Env c (2 + 6 * i + 5) x) :
    LoopNative.Cbnz64.target backImmediate x = c.base + 428#64 := by
  rw [LoopNative.Cbnz64.target, back_delta, pc_body c i 5 room (by decide) x env]
  unfold MemReloc.imageAddress
  change c.base + 448#64 + BitVec.ofInt 64 (-20) = c.base + 428#64
  bv_omega

theorem branch_low (c : Context) (i : Nat) (room : i < c.n) (x : NativeState)
    (env : Env c (2 + 6 * i + 5) x) :
    (LoopNative.Cbnz64.target backImmediate x).toNat < 2 ^ 55 := by
  rw [branch_target c i room x env]
  have low := c.low
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem offset_after_body (c : Context) (i : Nat) (room : i < c.n) :
    offset c.base c.returnPC c.n (2 + 6 * i + 5 + 1) =
      BitVec.ofNat 64 (Generated.armcert_memcpy_entry + (if i + 1 < c.n then 8 else 32)) := by
  have nz : c.n ≠ 0 := by omega
  have index : 2 + 6 * i + 5 + 1 ≠ Schedule.copySteps c.n := by
    simp only [Schedule.copySteps, if_neg nz]
    omega
  simp only [offset, Schedule.nativeOffset]
  rw [if_neg index]
  by_cases again : i + 1 < c.n
  · rw [if_pos again, Schedule.copy_backedge_offset c.n i again]
  · rw [if_neg again, Schedule.copy_last_branch_exit c.n i (by omega) (by omega)]

theorem branch_taken_placed (c : Context) (i : Nat) (again : i + 1 < c.n) (x : NativeState)
    (env : Env c (2 + 6 * i + 5) x) :
    LoopNative.Cbnz64.target backImmediate x = c.base + offset c.base c.returnPC c.n (2 + 6 * i + 5 + 1) := by
  rw [branch_target c i (by omega) x env, offset_after_body c i (by omega), if_pos again]
  rfl

theorem branch_not_placed (c : Context) (i : Nat) (last : i + 1 = c.n) (room : i < c.n) (x : NativeState)
    (env : Env c (2 + 6 * i + 5) x) :
    x.regs._PC + 4#64 = c.base + offset c.base c.returnPC c.n (2 + 6 * i + 5 + 1) := by
  rw [pc_body c i 5 room (by decide) x env, offset_after_body c i room, if_neg (by omega : ¬ i + 1 < c.n)]
  unfold MemReloc.imageAddress
  change c.base + 448#64 + 4#64 = c.base + 452#64
  bv_omega

#print axioms back_delta
#print axioms branch_target
#print axioms branch_low
#print axioms offset_after_body
#print axioms branch_taken_placed
#print axioms branch_not_placed
#print axioms dest_distinct
#print axioms source_dest_distinct
#print axioms final_frame
#print axioms body_cost_room
#print axioms budget_enough
#print axioms body_room
#print axioms offset_body
#print axioms body_aligned
#print axioms body_next_placed
end ArmCertLoop.CopyNative
