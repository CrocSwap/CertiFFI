import ArmCertWalk.NativeTranslateAddressIFPrefix
import MemM1.Debug
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk
/-- Exact two-bit CURRENT projection of already approved E11, a design decision.
Active v1.7.41 premises SHA cbc271c12a58e49acd8e2cec88d47b7dc90a857fd466e78268d1a4b738360b6e,
row E11. This is not derived from HookQuiet, MDSCR.SS or EDSCR.STATUS.
The actual consumer must bind its existing E11 premise to these fields. -/
structure ExistingE11DebugAt (regs : Regs) : Prop where
  mde : _get_MDSCR_EL1_Type_MDE (regs.bank_BitVec_64 .MDSCR_EL1) = 0#1
  hde : _get_EDSCR_Type_HDE (regs.bank_BitVec_32 ._EDSCR) = 0#1

theorem ExistingE11DebugAt.guarded_page (regs : Regs) (debug : ExistingE11DebugAt regs) (guarded : Bool) :
    ExistingE11DebugAt (gpRegs regs guarded) := ⟨debug.mde, debug.hde⟩

/-- Reuse the canonical debug component with EXISTING E11 and F4 fields on
this SAME actual state; no debug call or success is supplied by the caller. -/
theorem existing_e11_debug_total (va : BitVec 64) (acc : AccessDescriptor) (size : Int)
    (state : State) (host : HostRegimeAt state) (mode : HostEL0ModeAt state.regs)
    (aa64 : state.regs.FeatureImpl[4] = true) (debug : ExistingE11DebugAt state.regs) :
    ∃ fault other, AArch64_CheckDebug va acc size state = .ok fault other ∧
      fault.statuscode = .Fault_None ∧ S1Normality.Frame state other :=
  MemM1.Debug.no_fault va acc size state mode.el host.noRME aa64 mode.ns debug.mde debug.hde

/-- Execute the original remaining source action, including its actual final
fault record and translation-end event. -/
theorem translation_debug_finish_total (va : BitVec 64) (acc : AccessDescriptor) (size : Int)
    (address : AddressDescriptor) (state : State) (host : HostRegimeAt state)
    (mode : HostEL0ModeAt state.regs) (aa64 : state.regs.FeatureImpl[4] = true)
    (debug : ExistingE11DebugAt state.regs) :
    ∃ fault other,
      translation_debug_finish va acc size address state =
        .ok {address with fault := fault, vaddress := Sail.BitVec.zeroExtend va 64} other ∧
      fault.statuscode = .Fault_None ∧ other.regs = state.regs ∧ other.mem = state.mem := by
  obtain ⟨fault, afterDebug, debugCall, noFault, frame⟩ := existing_e11_debug_total va acc size state host mode aa64 debug
  let result := {address with fault := fault, vaddress := Sail.BitVec.zeroExtend va 64}
  refine ⟨fault, {afterDebug with events := afterDebug.events.push (.translationEnd result)}, ?_,
    noFault, frame.1, frame.2.1⟩
  unfold translation_debug_finish
  rw [sail_bind_call _ _ state afterDebug fault debugCall]
  simp [end_translation_eq, result, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
#print axioms ExistingE11DebugAt.guarded_page
#print axioms existing_e11_debug_total
#print axioms translation_debug_finish_total
end ArmCertWalk
