-- EL and security state of EVERY actual IFETCH descriptor (any oracle draw) at EL0,
-- AArch64, EL3 AArch64-only, RME off, SCR_EL3.NS = 1 — from the SDK MemM1.AccIF.create and
-- determinism of CreateAccDescIFetch on the same state. With actual_ifetch_agree this makes any two
-- actual IFETCH descriptors AccAgree with no remaining hypothesis.
import ArmCertWalk.AccessTransfer
import MemM1.AccIF
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

theorem actual_ifetch_el_ss {s : State} {acc : AccessDescriptor} (h : ActualIFetchAcc s acc)
    (hNoRME : s.regs.FeatureImpl[232] = false) (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true) (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hEL : s.regs.PSTATE.EL = 0#2)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1) :
    acc.el = 0#2 ∧ acc.ss = .SS_NonSecure := by
  obtain ⟨t0, u0, regs, call⟩ := h
  obtain ⟨acc', t', call', fields, _⟩ := MemM1.AccIF.create t0 (by rw [regs]; exact hNoRME)
    (by rw [regs]; exact hA64) (by rw [regs]; exact hEL3A64) (by rw [regs]; exact hNoEL3A32)
    (by rw [regs]; exact hEL) (by rw [regs]; exact hNS)
  have same := call.symm.trans call'
  simp only [EStateM.Result.ok.injEq] at same
  obtain ⟨rfl, _⟩ := same
  exact ⟨fields.el, fields.ss⟩

/-- Two actual IFETCH descriptors on states satisfying the EL0/NS facts always AccAgree. -/
theorem actual_ifetch_agree_el0 {s s' : State} {a b : AccessDescriptor}
    (ha : ActualIFetchAcc s a) (hb : ActualIFetchAcc s' b)
    (hNoRME : s.regs.FeatureImpl[232] = false) (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true) (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hEL : s.regs.PSTATE.EL = 0#2)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hNoRME' : s'.regs.FeatureImpl[232] = false) (hA64' : s'.regs.PSTATE.nRW = 0#1)
    (hEL3A64' : s'.regs.FeatureImpl[7] = true) (hNoEL3A32' : s'.regs.FeatureImpl[3] = false)
    (hEL' : s'.regs.PSTATE.EL = 0#2)
    (hNS' : Sail.BitVec.extractLsb (s'.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1) :
    AccAgree a b := by
  obtain ⟨elA, ssA⟩ := actual_ifetch_el_ss ha hNoRME hA64 hEL3A64 hNoEL3A32 hEL hNS
  obtain ⟨elB, ssB⟩ := actual_ifetch_el_ss hb hNoRME' hA64' hEL3A64' hNoEL3A32' hEL' hNS'
  exact actual_ifetch_agree ha hb (elA.trans elB.symm) (ssA.trans ssB.symm)

#print axioms actual_ifetch_el_ss
#print axioms actual_ifetch_agree_el0
end ArmCertWalk
