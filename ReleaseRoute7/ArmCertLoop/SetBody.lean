import ArmCertLoop.SetContext
import ArmCertLoop.ValueFacts
import LoopNative.ArithmeticABI
import LoopNative.NextABI
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.SetNative
open ContractDraft

theorem dest_distinct (c : Context) (i j : Nat) (ir : i < c.n) (jr : j < c.n) (different : j ≠ i) :
    c.dstPA j ≠ c.dstPA i := by
  obtain ⟨pa, ma, _, _⟩ := c.data j jr
  obtain ⟨pb, mb, _, _⟩ := c.data i ir
  apply SpanMap.mapped_different c.mapping c.spans c.injective _ _
    ⟨destSpan c.d c.n, by simp [Context.spans], j, jr, rfl⟩
    ⟨destSpan c.d c.n, by simp [Context.spans], i, ir, rfl⟩ ⟨pa.toNat, ma⟩ ⟨pb.toNat, mb⟩
  intro same
  have equal := congrArg BitVec.toNat same
  rw [SpanMap.byteVA_toNat (destSpan c.d c.n) c.destObject j jr,
    SpanMap.byteVA_toNat (destSpan c.d c.n) c.destObject i ir] at equal
  exact different (by omega)

theorem offset_exit (c : Context) (positive : 0 < c.n) : offset c (2 + 4 * c.n) = 480#64 := by
  have nz : c.n ≠ 0 := by omega
  have final : 2 + 4 * c.n ≠ Schedule.setSteps c.n := by
    simp only [Schedule.setSteps, ite_eq_right nz]; omega
  have one : 2 + 4 * c.n ≠ 1 := by omega
  have bound : ¬2 + 4 * c.n < 4 * c.n + 2 := by omega
  simp [offset, Schedule.nativeOffset, Schedule.setWordOffset, final, nz, one, bound,
    Generated.armcert_memset_entry]

def backImmediate : BitVec 19 := BitVec.ofInt 19 (-3)
theorem back_delta : sign_extend (backImmediate +++ 0#2) 64 = BitVec.ofInt 64 (-12) := by decide

theorem branch_step (real : Type) [Sail.SailReal real] (c : Context) (i : Nat) (room : i < c.n)
    (x : NativeState) (env : Env c (2 + 4 * i + 3) x)
    (remaining : x.regs.gpr[2].toNat = c.n - (i + 1)) :
    ∃ y, modelStep real x = .ok () y ∧ Env c (2 + 4 * (i + 1)) y ∧ y.mem = x.mem ∧
      y.regs.gpr = x.regs.gpr ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧ NativeEntry.Effects.Frame {} x.regs y.regs := by
  have fetch : FetchObligations c.spec c.config c.rows c.mapping
      (LoopNative.Cbnz64.Dispatch.selected 2#5 backImmediate) x :=
    fetch_index c (2 + 4 * i + 3) 14 x env (by decide) (pc_body c i 3 room (by decide) x env)
  have branchPC := pc_body c i 3 room (by decide) x env
  have target : LoopNative.Cbnz64.target backImmediate x = c.base + 464#64 := by
    rw [LoopNative.Cbnz64.target, back_delta, branchPC]
    change c.base + 476#64 + BitVec.ofInt 64 (-12) = c.base + 464#64
    bv_omega
  have index : 2 + 4 * i + 3 + 1 = 2 + 4 * (i + 1) := by omega
  by_cases again : i + 1 < c.n
  · have nonzero : x.regs.gpr[2] ≠ 0#64 := by
      intro same
      have zero := congrArg BitVec.toNat same
      simp only [BitVec.toNat_ofNat] at zero
      omega
    have placed : LoopNative.Cbnz64.target backImmediate x = c.base + offset c (2 + 4 * i + 3 + 1) := by
      rw [target, index]
      exact congrArg (c.base + ·) (offset_body c (i+1) 0 again (by decide)).symm
    have low : (LoopNative.Cbnz64.target backImmediate x).toNat < 2 ^ 55 := by
      rw [target]
      have := c.low
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    obtain ⟨y, run, envNext, holds, mem, _, _, kept⟩ :=
      LoopNative.Cbnz64.next_taken_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
        c.base (offset c) (Schedule.setSteps c.n) (2 + 4 * i + 3)
        (body_room c i 3 room (by decide)) c.page (body_aligned c i 3 room (by decide))
        2#5 backImmediate (by decide) x env ((LoopNative.Cbnz64.condition_iff 2#5 x).2 nonzero) low placed fetch
    rw [index] at envNext
    exact ⟨y, run, envNext, mem, ValueFacts.nil_gpr x y holds, ValueFacts.nil_sp x y holds, kept⟩
  · have zero : x.regs.gpr[2] = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      change x.regs.gpr[2].toNat = 0
      omega
    have condition : ¬ LoopNative.Cbnz64.condition 2#5 x := fun h => ((LoopNative.Cbnz64.condition_iff 2#5 x).1 h) zero
    have placed : x.regs._PC + 4#64 = c.base + offset c (2 + 4 * i + 3 + 1) := by
      have last : i + 1 = c.n := by omega
      rw [branchPC, index, last, offset_exit c (by omega)]
      change c.base + 476#64 + 4#64 = c.base + 480#64
      bv_omega
    obtain ⟨y, run, envNext, holds, mem, _, _, kept⟩ :=
      LoopNative.Cbnz64.next_not_taken_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
        c.base (offset c) (Schedule.setSteps c.n) (2 + 4 * i + 3)
        (body_room c i 3 room (by decide)) c.page (body_aligned c i 3 room (by decide))
        2#5 backImmediate (by decide) x env condition placed fetch
    rw [index] at envNext
    exact ⟨y, run, envNext, mem, ValueFacts.nil_gpr x y holds, ValueFacts.nil_sp x y holds, kept⟩

/-- One four-instruction fill iteration. All memory and control obligations
are derived at the actually reached state, including the exact low byte. -/
theorem body (real : Type) [Sail.SailReal real] (c : Context) (entry x : NativeState)
    (i : Nat) (room : i < c.n) (header : Header c entry i x) :
    ∃ y, Uget.Chain.modelRun real 4 x = .ok () y ∧
      Bytes.SingleWrite (Aux.memoryView x) (Aux.memoryView y) (c.dstPA i) (c.fill.setWidth 8) ∧
      Header c entry (i + 1) y := by
  let k := 2 + 4 * i
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.StrbUoff.selected 1#5 3#5 0#12) x :=
    fetch_index c k 11 x header.environment (by decide) (pc_body c i 0 room (by decide) x header.environment)
  have codeD : ImageTableSeparated codeScope c.base c.mapping (DestinationPA c.mapping c.d c.n) :=
    fun off pa inside mapped => c.codeWrite off inside pa mapped
  obtain ⟨a, run0, env1, _, _, pay, _, frame0⟩ :=
    LoopNative.StrbU.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) k
      (body_room c i 0 room (by decide)) c.page (body_aligned c i 0 room (by decide))
      0#12 3#5 1#5 (by decide) (by decide) (DestinationPA c.mapping c.d c.n) codeD x header.environment
      (store_facts c i room x header.cursor) (body_next_placed c i 0 room (by decide) x header.environment) fetch0
  obtain ⟨pa, mapped, write, gpr0, sp0⟩ := NativeBytes.store_payload c.mapping 0#12 3#5 1#5 x a pay
  have addr : MemClass.StrbU.addr x 3#5 0#12 = c.d + BitVec.ofNat 64 i := by
    rw [CopyNative.store_addr_zero]; exact header.cursor
  have physical : c.dstPA i = pa.toNat := by simp only [Context.dstPA, ← addr, mapped, Option.getD_some]
  change Bytes.SingleWrite (Aux.memoryView x) (Aux.memoryView a) pa.toNat (x.regs.gpr[1].setWidth 8) at write
  rw [← physical, header.fill] at write
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.AddImm64.selected 3#5 3#5 1#12) a :=
    fetch_index c (k + 1) 12 a env1 (by decide) (pc_body c i 1 room (by decide) a env1)
  obtain ⟨b, run1, env2, values1, mem1, _, frame1⟩ :=
    LoopNative.AddImm64.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) (k+1)
      (body_room c i 1 room (by decide)) c.page (body_aligned c i 1 room (by decide))
      3#5 3#5 1#12 (by decide) (by decide) a env1 (body_next_placed c i 1 room (by decide) a env1) fetch1
  obtain ⟨gpr1, sp1⟩ := ValueFacts.add 3#5 3#5 1#12 a b values1
  change b.regs.gpr = a.regs.gpr.set 3 (a.regs.gpr[3] + 1#64) at gpr1
  have fetch2 : FetchObligations c.spec c.config c.rows c.mapping
      (LoopNative.SubImm64.Dispatch.selected 2#5 2#5 1#12) b :=
    fetch_index c (k + 2) 13 b env2 (by decide) (pc_body c i 2 room (by decide) b env2)
  obtain ⟨t, run2, env3, values2, mem2, _, frame2⟩ :=
    LoopNative.SubImm64.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c) (Schedule.setSteps c.n) (k+2)
      (body_room c i 2 room (by decide)) c.page (body_aligned c i 2 room (by decide))
      2#5 2#5 1#12 (by decide) (by decide) b env2 (body_next_placed c i 2 room (by decide) b env2) fetch2
  obtain ⟨gpr2, sp2⟩ := ValueFacts.sub 2#5 2#5 1#12 b t values2
  change t.regs.gpr = b.regs.gpr.set 2 (b.regs.gpr[2] - 1#64) at gpr2
  have counterB : b.regs.gpr[2] = x.regs.gpr[2] := by rw [gpr1, gpr0]; simp
  have counterT : t.regs.gpr[2] = x.regs.gpr[2] - 1#64 := by rw [gpr2, Vector.getElem_set_self, counterB]
  have counterPositive : 0 < x.regs.gpr[2].toNat := by have := header.remaining; omega
  have remaining : t.regs.gpr[2].toNat = c.n - (i+1) := by
    rw [counterT, Schedule.counter_pred _ counterPositive, header.remaining]; omega
  obtain ⟨y, run3, env4, mem3, gpr3, sp3, frame3⟩ := branch_step real c i room t env3 remaining
  have written := NativeBytes.write_after_memory_frames
    (before := x) (load := x) (store := a) (after := y) rfl write (mem3.trans (mem2.trans mem1))
  have filled := Bytes.fillPrefix_succ header.bytes room written
    (fun j prior => dest_distinct c i j room (by omega) (by omega))
  have advance : c.d + BitVec.ofNat 64 i + 1#64 = c.d + BitVec.ofNat 64 (i + 1) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  have gpr : y.regs.gpr = (x.regs.gpr.set 3 (c.d + BitVec.ofNat 64 (i+1))).set 2 (x.regs.gpr[2] - 1#64) := by
    rw [gpr3, gpr2, counterB, gpr1, gpr0, header.cursor, advance]
  refine ⟨y, ?_, written, header.positive, by omega, env4, ?_, ?_, ?_, ?_, ?_, ?_,
    sp3.trans (sp2.trans (sp1.trans (sp0.trans header.sp))),
    (((header.protectedRegs.trans frame0).trans frame1).trans frame2).trans frame3, filled⟩
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

#print axioms dest_distinct
#print axioms offset_exit
#print axioms back_delta
#print axioms branch_step
#print axioms body
end ArmCertLoop.SetNative
