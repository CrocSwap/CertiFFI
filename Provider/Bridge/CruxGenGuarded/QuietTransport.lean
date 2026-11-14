import Bridge.CruxCore
import ArmCert.HookQuiet.V0.Predicate

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Draft ArmBridge.CruxCore
open ArmCert.HookQuiet.V0 (HookQuiet feature reg64 TimersQuiet TimerQuiet Deadline
  physical physicalOffset el2Enabled realm effectiveNS)

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED transport stage from the BookkeepingGuard private generator port.
The native common step itself is still a separate proof obligation. The Q-v0
predicate is development-only; no concrete hook law or SAT instance is inferred.
The exceptional MDCCSR field is actually changed by native preFetchRegs. -/

structure GuardFieldsEq (s t : NativeState) : Prop where
  features : t.regs.FeatureImpl = s.regs.FeatureImpl
  el : t.regs.PSTATE.EL = s.regs.PSTATE.EL
  nrw : t.regs.PSTATE.nRW = s.regs.PSTATE.nRW
  spe : t.regs.bank_Bool .SPESampleInFlight = s.regs.bank_Bool .SPESampleInFlight
  pmuCount : t.regs.bank_Int .NUM_PMU_COUNTERS = s.regs.bank_Int .NUM_PMU_COUNTERS
  cntcr : t.regs.bank_BitVec_32 .CNTCR = s.regs.bank_BitVec_32 .CNTCR
  physicalCount : t.regs.PhysicalCount = s.regs.PhysicalCount
  bank64 : ∀ k : ArmFull.Bank_BitVec_64, k ≠ .MDCCSR_EL0 →
    t.regs.bank_BitVec_64 k = s.regs.bank_BitVec_64 k

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.quiet_of_fields"
  (← IO.getStderr).flush

theorem quiet_of_fields (ticks : Nat) (s t : NativeState)
    (hq : HookQuiet ticks s) (h : GuardFieldsEq s t) : HookQuiet ticks t := by
  constructor
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.a64
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.el0
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.nrw
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.scrRW
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.hcrRW
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.validSecurity
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.spe
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.pmuIrqMask
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.brbePaused
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.pmuCountLower
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.pmuCountUpper
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.ordinary
  · simpa (disch := decide) [BitVec.le_def, feature, reg64, TimersQuiet, TimerQuiet, Deadline, physical, physicalOffset, el2Enabled, realm, effectiveNS, h.features, h.el, h.nrw, h.spe, h.pmuCount, h.cntcr, h.physicalCount, h.bank64] using hq.timers

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.quiet_preFetch"
  (← IO.getStderr).flush

theorem quiet_preFetch (ticks : Nat) (s : NativeState) (hq : HookQuiet ticks s) :
    HookQuiet ticks { s with regs := preFetchRegs s.regs } := by
  apply quiet_of_fields ticks s _ hq
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · simp (disch := decide) only [preFetchRegs, RegMap.set_ne]
  · simp (disch := decide) only [preFetchRegs, RegMap.set_ne]
  · rfl
  · intro k hk
    simp (disch := first | assumption | exact Ne.symm hk | decide) only [preFetchRegs, RegMap.set_ne]

run_cmd do
  IO.eprintln "CURRENT_DECL CruxGenGuarded.quiet_fetchRegs"
  (← IO.getStderr).flush

theorem quiet_fetchRegs (ticks : Nat) (s : NativeState) (hq : HookQuiet ticks s) :
    HookQuiet ticks { s with regs := clrGP (fetchRegs s.regs) } := by
  apply quiet_of_fields ticks s _ hq
  constructor
  all_goals first
    | rfl
    | (intro k hk; rfl)
    | (simp (disch := decide) only [fetchRegs, clrGP, Register.__InstructionStep,
        Register.BTypeCompatible, Regs.ref_Bool, RegMap.set_ne])

#print axioms quiet_of_fields
#print axioms quiet_preFetch
#print axioms quiet_fetchRegs
end ArmBridge.CruxGenGuarded
