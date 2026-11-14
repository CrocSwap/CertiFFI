import ArmCertMemPipe.TailLdrbU
import ArmCertMemPipe.TailStrbU
import ArmCertLoop.CopyLoop
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmBridge.Draft
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.NativeBytes
open ArmCertLoop.Bytes

theorem load_payload (mapping : BitVec 64 → Option Nat) (imm12 : BitVec 12)
    (Rn Rt : BitVec 5) (before after : NativeState)
    (pay : ArmCertMemPipe.LdrbU.Pay mapping imm12 Rn Rt before after) :
    ∃ (pa : BitVec 56) (byte : BitVec 8),
      mapping (MemClass.LdrbU.addr before Rn imm12) = some pa.toNat ∧
      before.mem[pa.toNat]? = some byte ∧
      after.regs.gpr = before.regs.gpr.set (GPRSummary.key Rt.toNat).val (byte.setWidth 64) ∧
      after.regs.SP_EL0 = before.regs.SP_EL0 ∧ after.mem = before.mem := by
  obtain ⟨pa, byte, mapped, present, gpr, sp, memory, _⟩ := pay
  refine ⟨pa, byte, mapped, ?_, ?_, sp, memory⟩
  · have h := present 0 (by decide)
    simpa using h
  · rw [gpr]
    simp only [MemClass.LdrbU.post, CryptoMem.MemCore.setGpr, MemClass.LdrbU.val_eq]

theorem store_payload (mapping : BitVec 64 → Option Nat) (imm12 : BitVec 12)
    (Rn Rt : BitVec 5) (before after : NativeState)
    (pay : ArmCertMemPipe.StrbU.Pay mapping imm12 Rn Rt before after) :
    ∃ pa : BitVec 56, mapping (MemClass.StrbU.addr before Rn imm12) = some pa.toNat ∧
      SingleWrite (Aux.memoryView before) (Aux.memoryView after) pa.toNat
        (before.regs.gpr[(GPRSummary.key Rt.toNat).val].setWidth 8) ∧
      after.regs.gpr = before.regs.gpr ∧ after.regs.SP_EL0 = before.regs.SP_EL0 := by
  obtain ⟨pa, mapped, memory, gpr, sp, _⟩ := pay
  refine ⟨pa, mapped, ⟨?_, ?_⟩, gpr, sp⟩
  · change after.mem[pa.toNat]? = _
    rw [memory, MemM1.MemWriteD1.wfold_get, if_pos (by omega), Nat.sub_self, MemClass.StrbU.stByte]
  · intro q different
    change after.mem[q]? = before.mem[q]?
    rw [memory, MemM1.MemWriteD1.wfold_get, if_neg (by omega)]

theorem zeroExtend_lowByte (byte : BitVec 8) :
    (byte.setWidth 64).setWidth 8 = byte := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_setWidth, hi, show i < 64 by omega]

theorem write_after_memory_frames {before load store after : NativeState} {pa : Nat} {byte : BitVec 8}
    (loadMemory : load.mem = before.mem)
    (written : SingleWrite (Aux.memoryView load) (Aux.memoryView store) pa byte)
    (afterMemory : after.mem = store.mem) :
    SingleWrite (Aux.memoryView before) (Aux.memoryView after) pa byte := by
  have b : Aux.memoryView load = Aux.memoryView before := by unfold Aux.memoryView; rw [loadMemory]
  have a : Aux.memoryView after = Aux.memoryView store := by unfold Aux.memoryView; rw [afterMemory]
  rw [b] at written
  rw [a]
  exact written

#print axioms load_payload
#print axioms store_payload
#print axioms zeroExtend_lowByte
#print axioms write_after_memory_frames
end ArmCertLoop.NativeBytes
