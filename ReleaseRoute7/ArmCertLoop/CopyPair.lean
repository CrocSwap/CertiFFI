import ArmCertLoop.CopyGeometry
import LoopNative.NextABI
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

/-- The actual first two instructions of the copy body. Exact source byte,
exact one-byte store and global RAM frame; no native-step callback inputs. -/
theorem memory_pair (real : Type) [Sail.SailReal real] (c : Context) (i : Nat) (room : i < c.n)
    (x : NativeState) (byte : BitVec 8) (env : Env c (2 + 6 * i) x)
    (sourceCursor : x.regs.gpr[1] = c.s + BitVec.ofNat 64 i)
    (destCursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i)
    (value : x.mem[c.srcPA i]? = some byte) :
    ∃ y, Uget.Chain.modelRun real 2 x = .ok () y ∧ Env c (2 + 6 * i + 2) y ∧
      Bytes.SingleWrite (Aux.memoryView x) (Aux.memoryView y) (c.dstPA i) byte ∧
      y.regs.gpr = x.regs.gpr.set 4 (byte.setWidth 64) ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧
      NativeEntry.Effects.Frame {} x.regs y.regs := by
  let k := 2 + 6 * i
  have fetch0 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.LdrbUoff.selected 4#5 1#5 0#12) x := by
    exact fetch_index c k 2 x env (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry, Nat.add_zero] using
        pc_body c i 0 room (by decide) x env)
  obtain ⟨a, run0, env1, _, _, loadPay, _, frame0⟩ :=
    LoopNative.LdrbU.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget k
      (by simpa only [Nat.add_zero] using body_room c i 0 room (by decide)) c.page
      (by simpa only [Nat.add_zero] using body_aligned c i 0 room (by decide))
      0#12 1#5 4#5 (by decide) (by decide) x env (load_facts c i room x byte sourceCursor value)
      (by simpa only [Nat.add_zero] using body_next_placed c i 0 room (by decide) x env) fetch0
  obtain ⟨sourcePA, loadedByte, mapped0, present0, gpr0, sp0, memory0⟩ :=
    NativeBytes.load_payload c.mapping 0#12 1#5 4#5 x a loadPay
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
  have fetch1 : FetchObligations c.spec c.config c.rows c.mapping
      (NativeEntryBodyDispatch.StrbUoff.selected 4#5 3#5 0#12) a := by
    exact fetch_index c (k + 1) 3 a env1 (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry] using
        pc_body c i 1 room (by decide) a env1)
  have codeD : ImageTableSeparated codeScope c.base c.mapping (DestinationPA c.mapping c.d c.n) := by
    intro off pa inside mapped target
    exact c.codeWrite off inside pa mapped target
  obtain ⟨y, run1, env2, _, _, storePay, _, frame1⟩ :=
    LoopNative.StrbU.next_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
      c.base (offset c.base c.returnPC c.n) c.budget (k + 1)
      (body_room c i 1 room (by decide)) c.page (body_aligned c i 1 room (by decide))
      0#12 3#5 4#5 (by decide) (by decide) (DestinationPA c.mapping c.d c.n) codeD a env1
      (store_facts c i room a dest1) (body_next_placed c i 1 room (by decide) a env1) fetch1
  obtain ⟨destPA, mapped1, written, gpr1, sp1⟩ := NativeBytes.store_payload c.mapping 0#12 3#5 4#5 a y storePay
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
  refine ⟨y, ?_, env2, written, gpr1.trans gpr0, sp1.trans sp0, frame0.trans frame1⟩
  simp only [Uget.Chain.modelRun, run0, run1]

#print axioms memory_pair
end ArmCertLoop.CopyNative
