import ArmCertLoop.CopyControl
import LoopNative.ArithmeticABI
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.CopyNative
open ContractDraft

/-- The remaining four actual instructions in a forward-copy iteration.
The full64 counter determines the back-edge internally. -/
theorem arithmetic_tail (real : Type) [Sail.SailReal real] (c : Context) (i : Nat) (room : i < c.n)
    (x : NativeState) (env : Env c (2 + 6 * i + 2) x)
    (sourceCursor : x.regs.gpr[1] = c.s + BitVec.ofNat 64 i)
    (destCursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i)
    (remaining : x.regs.gpr[2].toNat = c.n - i) :
    ∃ y, Uget.Chain.modelRun real 4 x = .ok () y ∧ Env c (2 + 6 * (i + 1)) y ∧
      y.regs.gpr = ((x.regs.gpr.set 1 (c.s + BitVec.ofNat 64 (i + 1))).set 3
        (c.d + BitVec.ofNat 64 (i + 1))).set 2 (x.regs.gpr[2] - 1#64) ∧
      y.regs.gpr[2].toNat = c.n - (i + 1) ∧ y.mem = x.mem ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧
      NativeEntry.Effects.Frame {} x.regs y.regs := by
  let k := 2 + 6 * i
  have fetch2 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.AddImm64.selected 1#5 1#5 1#12) x := by
    exact fetch_index c (k + 2) 4 x env (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry] using
        pc_body c i 2 room (by decide) x env)
  obtain ⟨a, run2, env3, values2, memory2, _, frame2⟩ :=
    LoopNative.AddImm64.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget (k + 2)
      (body_room c i 2 room (by decide)) c.page (body_aligned c i 2 room (by decide))
      1#5 1#5 1#12 (by decide) (by decide) x env (body_next_placed c i 2 room (by decide) x env) fetch2
  obtain ⟨gpr2, sp2⟩ := ValueFacts.add 1#5 1#5 1#12 x a values2
  change a.regs.gpr = x.regs.gpr.set 1 (x.regs.gpr[1] + 1#64) at gpr2
  have fetch3 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.AddImm64.selected 3#5 3#5 1#12) a := by
    exact fetch_index c (k + 3) 5 a env3 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry] using
        pc_body c i 3 room (by decide) a env3)
  obtain ⟨b, run3, env4, values3, memory3, _, frame3⟩ :=
    LoopNative.AddImm64.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget (k + 3)
      (body_room c i 3 room (by decide)) c.page (body_aligned c i 3 room (by decide))
      3#5 3#5 1#12 (by decide) (by decide) a env3 (body_next_placed c i 3 room (by decide) a env3) fetch3
  obtain ⟨gpr3, sp3⟩ := ValueFacts.add 3#5 3#5 1#12 a b values3
  change b.regs.gpr = a.regs.gpr.set 3 (a.regs.gpr[3] + 1#64) at gpr3
  have fetch4 : FetchObligations c.spec c.config c.rows c.mapping
      (LoopNative.SubImm64.Dispatch.selected 2#5 2#5 1#12) b := by
    exact fetch_index c (k + 4) 6 b env4 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry] using
        pc_body c i 4 room (by decide) b env4)
  obtain ⟨d, run4, env5, values4, memory4, _, frame4⟩ :=
    LoopNative.SubImm64.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget (k + 4)
      (body_room c i 4 room (by decide)) c.page (body_aligned c i 4 room (by decide))
      2#5 2#5 1#12 (by decide) (by decide) b env4 (body_next_placed c i 4 room (by decide) b env4) fetch4
  obtain ⟨gpr4, sp4⟩ := ValueFacts.sub 2#5 2#5 1#12 b d values4
  change d.regs.gpr = b.regs.gpr.set 2 (b.regs.gpr[2] - 1#64) at gpr4
  have counterB : b.regs.gpr[2] = x.regs.gpr[2] := by rw [gpr3, gpr2]; simp
  have counterD : d.regs.gpr[2] = x.regs.gpr[2] - 1#64 := by rw [gpr4, Vector.getElem_set_self, counterB]
  have positive : 0 < x.regs.gpr[2].toNat := by omega
  have remainingD : d.regs.gpr[2].toNat = c.n - (i + 1) := by
    rw [counterD, Schedule.counter_pred _ positive, remaining]
    omega
  obtain ⟨y, run5, env6, memory5, gpr5, sp5, frame5⟩ := branch_step real c i room d env5 remainingD
  have advance (base : BitVec 64) : base + BitVec.ofNat 64 i + 1#64 = base + BitVec.ofNat 64 (i + 1) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  have gpr : y.regs.gpr = ((x.regs.gpr.set 1 (c.s + BitVec.ofNat 64 (i + 1))).set 3
      (c.d + BitVec.ofNat 64 (i + 1))).set 2 (x.regs.gpr[2] - 1#64) := by
    rw [gpr5, gpr4, gpr3, gpr2]
    simp [sourceCursor, destCursor, advance]
  have elapsed : 2 + 6 * i + 6 = 2 + 6 * (i + 1) := by omega
  rw [elapsed] at env6
  refine ⟨y, ?_, env6, gpr, ?_, memory5.trans (memory4.trans (memory3.trans memory2)),
    sp5.trans (sp4.trans (sp3.trans sp2)), ((frame2.trans frame3).trans frame4).trans frame5⟩
  · simp only [Uget.Chain.modelRun, run2, run3, run4, run5]
  · rw [gpr5]
    exact remainingD

#print axioms arithmetic_tail
end ArmCertLoop.CopyNative
