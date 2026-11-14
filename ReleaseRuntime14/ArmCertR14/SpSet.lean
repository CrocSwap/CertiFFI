-- Memory (runtime14): Sail SP_set at EL0 (restated from CryptoMem.PairCoreWb.sp_set_el0, whose module imports
-- the old-bridge CryptoMem.PairCore).
import CryptoMem.MemCore
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option autoImplicit false
namespace ArmCertR14.SpSet
open ArmBridge.Draft

theorem sp_set_el0 (st : NativeState) (v : BitVec 64) (h : st.regs.PSTATE.EL = 0#2) :
    (SP_set v : SailM Unit) st = .ok () { st with regs := { st.regs with SP_EL0 := v } } := by
  unfold SP_set
  have rdP : ∀ t : NativeState, (readReg PSTATE : SailM ProcState) t = .ok t.regs.PSTATE t := fun _ => rfl
  have wr : (writeReg SP_EL0 v : SailM Unit) st = .ok () { st with regs := { st.regs with SP_EL0 := v } } := rfl
  by_cases hs : (st.regs.PSTATE.SP == 0#1) = true
  · simp only [bind, EStateM.bind, rdP, hs, ite_true, wr]
  · have hE : (st.regs.PSTATE.EL == EL0) = true := by rw [h]; rfl
    simp only [bind, EStateM.bind, rdP, hs, Bool.false_eq_true, ite_false, hE, ite_true, wr]

#print axioms sp_set_el0
end ArmCertR14.SpSet
