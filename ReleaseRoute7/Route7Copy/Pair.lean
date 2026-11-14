-- Route 7 unit 3: the copy body's LDRB/STRB pair over EnvR (Runtime InvG), ported from loops CopyPair.memory_pair.
import Route7Copy.Past
import Route7Copy.Cover
import Route7Trace.Copy
import Route7Steps.Mem
import ArmCertLoop.CopyGeometry
import ArmCertLoop.NativeBytes
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

theorem body_next_placed_r (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (i j : Nat) (room : i < c.n) (slot : j < 5)
    (x : NativeState) (env : EnvR c catalogue entry (2 + 6 * i + j) x) :
    x.regs._PC + 4#64 = c.base + offset c.base c.returnPC c.n (2 + 6 * i + j + 1) := by
  rw [pc_body_r c catalogue entry i j room (by omega) x env]
  have index : 2 + 6 * i + j + 1 = 2 + 6 * i + (j + 1) := by omega
  rw [index, offset_body c i (j + 1) room (by omega)]
  unfold MemReloc.imageAddress
  have indexWord : Generated.armcert_memcpy_entry + 8 + 4 * (j + 1) =
      (Generated.armcert_memcpy_entry + 8 + 4 * j) + 4 := by omega
  rw [indexWord]
  simp only [BitVec.ofNat_add, BitVec.add_assoc]

theorem memory_pair_r (real : Type) [Sail.SailReal real] (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (entry : NativeState) (nodup : (c.spec.logicalRows.map (·.logical)).Nodup)
    (i : Nat) (room : i < c.n)
    (x : NativeState) (byte : BitVec 8) (env : EnvR c catalogue entry (2 + 6 * i) x)
    (sourceCursor : x.regs.gpr[1] = c.s + BitVec.ofNat 64 i)
    (destCursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i)
    (value : x.mem[c.srcPA i]? = some byte) :
    ∃ y, Uget.Chain.modelRun real 2 x = .ok () y ∧ EnvR c catalogue entry (2 + 6 * i + 2) y ∧
      Bytes.SingleWrite (Aux.memoryView x) (Aux.memoryView y) (c.dstPA i) byte ∧
      y.regs.gpr = x.regs.gpr.set 4 (byte.setWidth 64) ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧
      NativeEntry.Effects.Frame {} x.regs y.regs ∧ Covered real (PcOk c) 2 x ∧
      Route7Trace.Traced real c.spec c.mapping (recsOf c) (pcOf c) 2 (2 + 6 * i) x := by
  let k := 2 + 6 * i
  have past0 : memPast c.n k = 2 * i := memPast_body c.n i (by omega)
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.LdrbUoff.selected 4#5 1#5 0#12) x := by
    exact fetch_index_r c catalogue entry k 2 x env (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry, Nat.add_zero] using
        pc_body_r c catalogue entry i 0 room (by decide) x env)
  have allowed0 := ReleaseProfile.DefaultRuntime.current_status env (by omega : memPast c.n k < 2 * c.n)
  obtain ⟨a, run0, ms0, frame0⟩ :=
    Route7Mem.DefaultLdrbU.routeF real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget k catalogue
      (by simpa only [Nat.add_zero] using body_room c i 0 room (by decide)) c.page
      (by simpa only [Nat.add_zero] using body_aligned c i 0 room (by decide))
      (NativeEntryBodyDispatch.LdrbUoff.selected 4#5 1#5 0#12) 633 (by decide) 0#12 1#5 4#5 (by decide) (by decide)
      (fun pc t see => NativeEntryBodyDispatch.LdrbUoff.dispatch_at real pc 4#5 1#5 0#12 t (by simpa using see))
      (LoopNative.Encoding.LdrbU_noEret 4#5 1#5 0#12) x env.core allowed0 (load_facts c i room x byte sourceCursor value)
      (by simpa only [Nat.add_zero] using body_next_placed_r c catalogue entry i 0 room (by decide) x env) fetch0 nodup
  have env1 : EnvR c catalogue entry (k + 1) a :=
    ReleaseProfile.DefaultRuntime.InvG.advance env ms0.current True.intro ms0.choice
      (by rw [show k + 1 = 2 + 6 * i + 0 + 1 by omega, memPast_step c.n i 0 room (by omega)]; simp [k])
  obtain ⟨sourcePA, loadedByte, mapped0, present0, gpr0, sp0, memory0⟩ :=
    NativeBytes.load_payload c.mapping 0#12 1#5 4#5 x a ms0.pay
  have addr0 : MemClass.LdrbU.addr x 1#5 0#12 = c.s + BitVec.ofNat 64 i := by
    rw [load_addr_zero]; exact sourceCursor
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
  have env1' : EnvR c catalogue entry (2 + 6 * i + 1) a := env1
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.StrbUoff.selected 4#5 3#5 0#12) a := by
    exact fetch_index_r c catalogue entry (k + 1) 3 a env1 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry] using
        pc_body_r c catalogue entry i 1 room (by decide) a env1')
  have codeD : ImageTableSeparated codeScope c.base c.mapping (DestinationPA c.mapping c.d c.n) := by
    intro off pa inside mapped target
    exact c.codeWrite off inside pa mapped target
  have past1 : memPast c.n (k + 1) = 2 * i + 1 := by
    rw [show k + 1 = 2 + 6 * i + 0 + 1 by omega, memPast_step c.n i 0 room (by omega)]; simp [past0, k]
  have allowed1 := ReleaseProfile.DefaultRuntime.current_status env1 (by omega : memPast c.n (k + 1) < 2 * c.n)
  obtain ⟨y, run1, ms1, frame1⟩ :=
    Route7Mem.DefaultStrbU.routeF real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget (k + 1) catalogue
      (body_room c i 1 room (by decide)) c.page (body_aligned c i 1 room (by decide))
      (NativeEntryBodyDispatch.StrbUoff.selected 4#5 3#5 0#12) 651 (by decide) 0#12 3#5 4#5 (by decide) (by decide)
      (fun pc t see => NativeEntryBodyDispatch.StrbUoff.dispatch_at real pc 4#5 3#5 0#12 t (by simpa using see))
      (LoopNative.Encoding.StrbU_noEret 4#5 3#5 0#12) (DestinationPA c.mapping c.d c.n) codeD a env1.core allowed1
      (store_facts c i room a dest1) (body_next_placed_r c catalogue entry i 1 room (by decide) a env1') fetch1 nodup
  have env2 : EnvR c catalogue entry (2 + 6 * i + 2) y := by
    have adv := ReleaseProfile.DefaultRuntime.InvG.advance env1 ms1.current True.intro ms1.choice
      (by rw [show k + 1 + 1 = 2 + 6 * i + 1 + 1 by omega, show k + 1 = 2 + 6 * i + 1 by omega,
            memPast_step c.n i 1 room (by omega)]; simp)
    simpa only [show k + 1 + 1 = 2 + 6 * i + 2 by omega] using adv
  obtain ⟨destPA, mapped1, written, gpr1, sp1⟩ := NativeBytes.store_payload c.mapping 0#12 3#5 4#5 a y ms1.pay
  have addr1 : MemClass.StrbU.addr a 3#5 0#12 = c.d + BitVec.ofNat 64 i := by
    rw [store_addr_zero]; exact dest1
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
  rotate_left
  · -- trace (loops CT0): LDRB records s + i, STRB records d + i, both public
    have ev0 := ms0.events
    rw [addr0, ← recs_ldrb c i room] at ev0
    have ev1 := ms1.events
    rw [addr1, ← recs_strb c i room] at ev1
    exact Route7Trace.traced_append real c.spec c.mapping (recsOf c) (pcOf c) 1 1 (2 + 6 * i) x a
      (Route7Trace.run_one real x a run0)
      (Route7Trace.traced_one real c.spec c.mapping (recsOf c) (pcOf c) _ x a run0 (pcAt_of_env c catalogue entry _ x env) ev0 frame0)
      (Route7Trace.traced_one real c.spec c.mapping (recsOf c) (pcOf c) _ a y run1 (pcAt_of_env c catalogue entry _ a env1') ev1 frame1)
  -- coverage (loops): the start, middle and end states all carry EnvR, hence a memcpy PC
  intro t ht
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with h | h | h <;> subst h
  · exact ⟨x, rfl, pcOk_of_env c catalogue entry _ x env⟩
  · exact ⟨a, by simp only [Uget.Chain.modelRun, run0], pcOk_of_env c catalogue entry _ a env1⟩
  · exact ⟨y, runY, pcOk_of_env c catalogue entry _ y env2⟩

end Route7Copy
#print axioms Route7Copy.memory_pair_r
