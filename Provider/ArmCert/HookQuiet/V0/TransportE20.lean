import ArmCert.HookQuiet.V0.Predicate
import Bridge.CruxCore
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

open ArmBridge.CruxCore

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

namespace ArmCert.HookQuiet.V0

/- HookQuiet reads only registers; arbitrary other native-state fields may differ. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE20.hookQuiet_of_regs_eq"
  (← IO.getStderr).flush

theorem hookQuiet_of_regs_eq {ticks : Nat} {s t : NativeState}
    (hr : s.regs = t.regs) (h : HookQuiet ticks s) : HookQuiet ticks t := by
  constructor
  · simpa only [hr] using h.a64
  · simpa only [hr] using h.el0
  · simpa only [hr] using h.nrw
  · simpa only [hr] using h.scrRW
  · simpa only [hr] using h.hcrRW
  · simpa only [hr] using h.validSecurity
  · simpa only [hr] using h.spe
  · simpa only [hr] using h.pmuIrqMask
  · simpa only [hr] using h.brbePaused
  · simpa only [hr] using h.pmuCountLower
  · simpa only [hr] using h.pmuCountUpper
  · simpa only [hr] using h.ordinary
  · simpa only [hr] using h.timers

/- Exact E20 erasure removes no field read by the proposed quiet predicate.
This structural fact says nothing about the actual PMU hook returning a frame. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE20.hookQuiet_eraseE20_iff"
  (← IO.getStderr).flush

theorem hookQuiet_eraseE20_iff (ticks : Nat) (s : NativeState) :
    HookQuiet ticks {s with regs := eraseE20 s.regs} ↔ HookQuiet ticks s := by
  constructor
  · intro h
    cases h
    constructor <;> assumption
  · intro h
    cases h
    constructor <;> assumption

/- Internal transport from the exact formal frame; actual model hooks must
separately prove this frame and their successful full-state successor. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE20.hookQuiet_of_E20Frame"
  (← IO.getStderr).flush

theorem hookQuiet_of_E20Frame {ticks : Nat} {s t : NativeState}
    (hFrame : E20Frame s.regs t.regs) (h : HookQuiet ticks s) : HookQuiet ticks t := by
  apply (hookQuiet_eraseE20_iff ticks t).mp
  apply hookQuiet_of_regs_eq (s := {s with regs := eraseE20 s.regs})
    (t := {t with regs := eraseE20 t.regs}) hFrame.symm
  exact (hookQuiet_eraseE20_iff ticks s).mpr h

#print axioms hookQuiet_of_regs_eq
#print axioms hookQuiet_eraseE20_iff
#print axioms hookQuiet_of_E20Frame

end ArmCert.HookQuiet.V0
