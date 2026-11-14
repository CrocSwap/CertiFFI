import ArmCertWalk.OuterModeSource
import ArmCertWalk.OuterFaultSource
import Walk.S1EL2Enabled
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk
/-- Current scalar subset of the existing caller controls. These are internal
producer links, not additional public admission or future query answers. -/
structure HostEL0ModeAt (regs : Regs) : Prop where
  noEL2A32 : regs.FeatureImpl[2] = false
  el2A64 : regs.FeatureImpl[6] = true
  vhe : regs.FeatureImpl[54] = true
  el : regs.PSTATE.EL = 0#2
  ns : _get_SCR_EL3_Type_NS (regs.bank_BitVec_64 .SCR_EL3) = 1#1
  tge : _get_HCR_EL2_Type_TGE (regs.bank_BitVec_64 .HCR_EL2) = 1#1

theorem outer_regime_total (state : State) (host : HostRegimeAt state)
    (mode : HostEL0ModeAt state.regs) :
    ∃ other, TranslationRegime EL0 state = .ok .Regime_EL20 other ∧ S1Normality.Frame state other := by
  rw [OuterModeSource.complete state host.noRME host.noEl3a32 host.el3a64 mode.noEL2A32
    mode.el2A64 mode.vhe mode.el mode.ns host.e2h mode.tge]
  have ns : Sail.BitVec.extractLsb (Mk_SCRType (state.regs.bank_BitVec_64 .SCR_EL3)) 0 0 = 1#1 := mode.ns
  delta OuterModeSource.native
  simp only [ns, true_or, ↓reduceIte, host.el3a64, mode.el,
    Bool.true_eq_false, and_false, show (0#2 : BitVec 2) ≠ 2#2 by decide]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem outer_no_fault_total (acc : AccessDescriptor) (state : State) :
    ∃ fault other, NoFault__1 acc state = .ok fault other ∧
      fault.statuscode = .Fault_None ∧ S1Normality.Frame state other := by
  rw [OuterFaultSource.complete]
  delta OuterFaultSource.native
  exact ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

/-- Actual EL2 query on current existing Non-secure host controls. -/
theorem outer_el2_enabled (state : State) (host : HostRegimeAt state)
    (mode : HostEL0ModeAt state.regs) :
    ∃ other, EL2Enabled () state = .ok true other ∧ S1Normality.Frame state other := by
  rw [S1EL2Enabled.complete]
  have ns : Sail.BitVec.extractLsb (Mk_SCRType (state.regs.bank_BitVec_64 .SCR_EL3)) 0 0 = 1#1 := mode.ns
  simp only [S1EL2Enabled.native, host.el3a64, mode.el2A64, Bool.true_eq_false,
    and_false, ↓reduceIte, ns, true_or]
  exact ⟨_, rfl, rfl, rfl, rfl⟩
#print axioms outer_regime_total
#print axioms outer_no_fault_total
#print axioms outer_el2_enabled
end ArmCertWalk
