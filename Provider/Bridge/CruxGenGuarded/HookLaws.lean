import Bridge.CruxCore
import ArmCert.HookQuiet.V0.Predicate
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! INTERNAL target interface for the fixed native owner's constructed laws.
NO INSTANCE IS CONSTRUCTED HERE. Q is the owner's concrete state predicate;
success/frame/future quietness are conclusions of laws, never fields of Q.
The final public bridge must instantiate these laws internally. -/

structure HookPost (Frame : Regs → Regs → Prop) (budget : Nat) (s t : NativeState) : Prop where
  frame : Frame s.regs t.regs
  gic : t.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending
  mem : t.mem = s.mem
  events : t.events = s.events
  quiet : HookQuiet budget t

def EventLaw (event : BitVec 16) : Prop :=
  ∀ (b : Nat) (s : NativeState), HookQuiet b s →
    ∃ t, (PMUEvent event : SailM Unit) s = .ok () t ∧ HookPost E20Frame b s t

structure HookLaws : Prop where
  spec : EventLaw PMU_EVENT_INST_SPEC
  retired : EventLaw PMU_EVENT_INST_RETIRED
  counter : ∀ (b : Nat) (s : NativeState), HookQuiet (b + 1) s →
    ∃ t, (__UpdateSystemCounter () : SailM Unit) s = .ok () t ∧ HookPost E22Frame b s t
  cycle : ∀ (b : Nat) (s : NativeState), HookQuiet b s →
    ∃ t, (AArch64_PMUCycle () : SailM Unit) s = .ok () t ∧ HookPost E20Frame b s t

end ArmBridge.CruxGenGuarded
