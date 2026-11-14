-- Oracle source and tag-status occurrence transport through access prefixes.
import NativeMteTagCheck.Transport
import MemM1.MemReadDBE
import MemM1.MemWriteD6
import HeapV2StepCerts.AccShape

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultPrefix
open NativeMteTagCheck NativeMteTagCheck.StatusTrace
abbrev State := NativeMteTagCheck.State

#check "CURRENT_DECL prefix bool"
theorem bool_total (label : ChoiceLabel) (s : State) :
    ∃ value, undefined_bool_at label () s = .ok value s := ⟨_, rfl⟩

#check "CURRENT_DECL prefix constraint"
theorem constraint_total (label : ChoiceLabel) (s : State) :
    ∃ value, undefined_Constraint label () s = .ok value s := ⟨_, rfl⟩

#check "CURRENT_DECL prefix tme"
theorem tme_total (s : State) : ∃ value, HaveTME () s = .ok value s := ⟨_, rfl⟩

#check "CURRENT_DECL prefix endian"
theorem be_false (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2) (hnRW : s.regs.PSTATE.nRW = 0#1)
    (hR : s.regs.FeatureImpl[232] = false) (hVHE : s.regs.FeatureImpl[54] = true)
    (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hE2H : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1)
    (hTGE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1)
    (hE0E : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCTLR_EL2) 24 24 = 0#1) :
    ∃ t, BigEndian .AccessType_GPR s = .ok false t ∧ TraceFrame s t := by
  rw [MemM1.MemReadDBE.be_eq s hEL hnRW hR hVHE hAA hNS hE2H hTGE]
  observe_simp [TraceFrame, S1Normality.Frame, ChoiceDelta, Std.ExtHashMap.getD_insert,
    MemM1.MemReadDBE.be_native]
  all_goals simp [Mk_SCTLRType, Mk_SCRType, hNS, hAA, hE0E, Std.ExtHashMap.getD_insert]

#print axioms bool_total
#print axioms constraint_total
#print axioms tme_total
#print axioms be_false
end ReleaseProfile.DefaultPrefix
