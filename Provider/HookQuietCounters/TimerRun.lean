import HookQuietCounters.TimerCompose
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerRun.timer_banks_total"
  (← IO.getStderr).flush

theorem timer_banks_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (imask : BitVec 1) (status : Bool) :
    ∃ t, TimerFlow.banks (securityValue s) (ArmCert.HookQuiet.V0.physicalOffset s.regs)
      imask status s = .ok () t ∧ TimerFrame s t := by
  obtain ⟨p, s1, hp, fp⟩ := TimerBankFacts.totalP budget s q imask status
  obtain ⟨p1, s2, hhp, fhp⟩ := TimerBankFacts.totalHP budget s1 (fp.quiet q) p.2
  have f02 := fp.trans fhp
  obtain ⟨p2, s3, hhps, fhps⟩ := TimerBankFacts.totalHPS budget s2 (f02.quiet q) p1
  have f03 := f02.trans fhps
  obtain ⟨p3, s4, hps, fps⟩ := TimerBankFacts.totalPS budget s3 (f03.quiet q) p2
  rw [f03.offset_eq] at hps
  have f04 := f03.trans fps
  obtain ⟨p4, s5, hv, fv⟩ := TimerBankFacts.totalV budget s4 (f04.quiet q) p3
  rw [f04.security_eq] at hv
  have f05 := f04.trans fv
  obtain ⟨p5, s6, hhv, fhv⟩ := TimerBankFacts.totalHV budget s5 (f05.quiet q) p4
  have f06 := f05.trans fhv
  obtain ⟨u, s7, hhvs, fhvs⟩ := TimerBankFacts.totalHVS budget s6 (f06.quiet q)
  cases u
  refine ⟨s7, ?_, f06.trans fhvs⟩
  simp only [TimerFlow.banks, bind_app, hp, hhp, hhps, hps, hv, hhv, hhvs]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerRun.a64_timers_total"
  (← IO.getStderr).flush

theorem a64_timers_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (AArch64_CheckTimerConditions () : SailM Unit) s = .ok () t ∧
      TimerFrame s t ∧ ArmCert.HookQuiet.V0.HookQuiet budget t := by
  obtain ⟨mask, status, hp⟩ := timer_preamble budget s q
  have f0 := timer_prepare_frame s
  obtain ⟨t, hb, fb⟩ := timer_banks_total budget (timerPrepareState s) (f0.quiet q) mask status
  rw [f0.security_eq, f0.offset_eq] at hb
  refine ⟨t, ?_, f0.trans fb, (f0.trans fb).quiet q⟩
  rw [TimerFlow.preamble_equation]
  simp only [bind_app, hp, hb]

#print axioms timer_banks_total
#print axioms a64_timers_total

end HookQuietCounters
