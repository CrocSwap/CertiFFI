import ArmCert.HookQuiet.V0.Deadline
import Bridge.CruxCore
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

open ArmFull ArmFull.Functions ArmBridge.CruxCore

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

namespace ArmCert.HookQuiet.V0

/- Only concrete ENABLE/IMASK equalities, not a desired timer/hook outcome. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22.CtlLowBitsEq"
  (← IO.getStderr).flush

def CtlLowBitsEq (before after : BitVec 64) : Prop :=
  after.getLsbD 0 = before.getLsbD 0 ∧ after.getLsbD 1 = before.getLsbD 1

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22.TimerLowBitsEq"
  (← IO.getStderr).flush

structure TimerLowBitsEq (r next : ArmFull.Regs) : Prop where
  p : CtlLowBitsEq (reg64 r .CNTP_CTL_EL0) (reg64 next .CNTP_CTL_EL0)
  hp : CtlLowBitsEq (reg64 r .CNTHP_CTL_EL2) (reg64 next .CNTHP_CTL_EL2)
  hps : CtlLowBitsEq (reg64 r .CNTHPS_CTL_EL2) (reg64 next .CNTHPS_CTL_EL2)
  ps : CtlLowBitsEq (reg64 r .CNTPS_CTL_EL1) (reg64 next .CNTPS_CTL_EL1)
  v : CtlLowBitsEq (reg64 r .CNTV_CTL_EL0) (reg64 next .CNTV_CTL_EL0)
  hv : CtlLowBitsEq (reg64 r .CNTHV_CTL_EL2) (reg64 next .CNTHV_CTL_EL2)
  hvs : CtlLowBitsEq (reg64 r .CNTHVS_CTL_EL2) (reg64 next .CNTHVS_CTL_EL2)

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22.timerQuiet_after_guarded_count_and_bits"
  (← IO.getStderr).flush

theorem timerQuiet_after_guarded_count_and_bits {ticks : Nat} {r next : ArmFull.Regs}
    {active forced : Bool} {ctl nextCtl compare offset : BitVec 64}
    (h : TimerQuiet (ticks + 1) r active ctl compare offset forced)
    (hBits : CtlLowBitsEq ctl nextCtl)
    (hAdvance : physical r + (ticks + 1) < 2^64 →
      physical r ≤ physical next ∧ physical next ≤ physical r + 1) :
    TimerQuiet ticks next active nextCtl compare offset forced := by
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (hBits.1.trans h))
  · exact Or.inr (Or.inr (Or.inl (hBits.2.trans h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · obtain ⟨hLower,hUpper⟩ := hAdvance h.2.1
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (deadline_after_count_advance h hLower hUpper))))

/- Generic internal composition; all four stable selectors below are fixed
concrete functions at each use, and their erasure equalities are proved by rfl. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22.timerQuiet_after_E22"
  (← IO.getStderr).flush

private theorem timerQuiet_after_E22 {ticks : Nat} {r next : ArmFull.Regs}
    (active : ArmFull.Regs → Bool) (ctl compare offset : ArmFull.Regs → BitVec 64)
    (forced : ArmFull.Regs → Bool)
    (ha : ∀ x, active (eraseE22 x) = active x)
    (hc : ∀ x, compare (eraseE22 x) = compare x)
    (ho : ∀ x, offset (eraseE22 x) = offset x)
    (hf : ∀ x, forced (eraseE22 x) = forced x)
    (hFrame : E22Frame r next)
    (hAdvance : physical r + (ticks + 1) < 2^64 →
      physical r ≤ physical next ∧ physical next ≤ physical r + 1)
    (hBits : CtlLowBitsEq (ctl r) (ctl next))
    (h : TimerQuiet (ticks + 1) r (active r) (ctl r) (compare r) (offset r) (forced r)) :
    TimerQuiet ticks next (active next) (ctl next) (compare next) (offset next) (forced next) := by
  rw [frame_pres_E22 active ha hFrame, frame_pres_E22 compare hc hFrame,
    frame_pres_E22 offset ho hFrame, frame_pres_E22 forced hf hFrame]
  exact timerQuiet_after_guarded_count_and_bits h hBits hAdvance

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22.timersQuiet_after_E22_guarded_advance"
  (← IO.getStderr).flush

theorem timersQuiet_after_E22_guarded_advance {ticks : Nat} {r next : ArmFull.Regs}
    (hFrame : E22Frame r next) (hBits : TimerLowBitsEq r next)
    (hAdvance : physical r + (ticks + 1) < 2^64 →
      physical r ≤ physical next ∧ physical next ≤ physical r + 1)
    (h : TimersQuiet (ticks + 1) r) : TimersQuiet ticks next := by
  rcases h with ⟨hp,hhp,hhps,hps,hv,hhv,hhvs⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact timerQuiet_after_E22 (fun _ => true) (fun x => reg64 x .CNTP_CTL_EL0)
      (fun x => reg64 x .CNTP_CVAL_EL0) physicalOffset
      (fun x => realm x && (_get_CNTHCTL_EL2_Type_CNTPMASK (reg64 x .CNTHCTL_EL2) == 1#1))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hAdvance hBits.p hp
  · exact timerQuiet_after_E22 (fun _ => true) (fun x => reg64 x .CNTHP_CTL_EL2)
      (fun x => reg64 x .CNTHP_CVAL_EL2) (fun _ => 0#64) (fun _ => false)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hAdvance hBits.hp hhp
  · exact timerQuiet_after_E22 (fun x => feature x .FEAT_SEL2) (fun x => reg64 x .CNTHPS_CTL_EL2)
      (fun x => reg64 x .CNTHPS_CVAL_EL2) (fun _ => 0#64) (fun _ => false)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hAdvance hBits.hps hhps
  · exact timerQuiet_after_E22 (fun _ => true) (fun x => reg64 x .CNTPS_CTL_EL1)
      (fun x => reg64 x .CNTPS_CVAL_EL1) physicalOffset (fun _ => false)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hAdvance hBits.ps hps
  · exact timerQuiet_after_E22 (fun _ => true) (fun x => reg64 x .CNTV_CTL_EL0)
      (fun x => reg64 x .CNTV_CVAL_EL0) (fun x => reg64 x .CNTVOFF_EL2)
      (fun x => realm x && (_get_CNTHCTL_EL2_Type_CNTVMASK (reg64 x .CNTHCTL_EL2) == 1#1))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hAdvance hBits.v hv
  · exact timerQuiet_after_E22 (fun x => feature x .FEAT_VHE) (fun x => reg64 x .CNTHV_CTL_EL2)
      (fun x => reg64 x .CNTHV_CVAL_EL2) (fun _ => 0#64) (fun _ => false)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hAdvance hBits.hv hhv
  · exact timerQuiet_after_E22 (fun x => feature x .FEAT_SEL2 && feature x .FEAT_VHE)
      (fun x => reg64 x .CNTHVS_CTL_EL2) (fun x => reg64 x .CNTHVS_CVAL_EL2)
      (fun _ => 0#64) (fun _ => false)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hAdvance hBits.hvs hhvs

/- Predicate-only internal transport. The model owner must establish EVERY
input condition from the actual successful counter transition. This theorem
does not assert hook success, a BitVec progression law, GIC preservation, or SAT. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22.hookQuiet_after_E22_guarded_advance"
  (← IO.getStderr).flush

theorem hookQuiet_after_E22_guarded_advance {ticks : Nat} {s t : NativeState}
    (h : HookQuiet (ticks + 1) s) (hFrame : E22Frame s.regs t.regs)
    (hBits : TimerLowBitsEq s.regs t.regs)
    (hAdvance : physical s.regs + (ticks + 1) < 2^64 →
      physical s.regs ≤ physical t.regs ∧ physical t.regs ≤ physical s.regs + 1) :
    HookQuiet ticks t := by
  constructor
  · exact (frame_pres_E22 (fun x => feature x .FEAT_AA64EL0 = true) (fun _ => rfl) hFrame).mpr h.a64
  · exact (frame_pres_E22 (fun x => x.PSTATE.EL = 0#2) (fun _ => rfl) hFrame).mpr h.el0
  · exact (frame_pres_E22 (fun x => x.PSTATE.nRW = 0#1) (fun _ => rfl) hFrame).mpr h.nrw
  · exact (frame_pres_E22 (fun x => _get_SCR_EL3_Type_RW (reg64 x .SCR_EL3) = 1#1) (fun _ => rfl) hFrame).mpr h.scrRW
  · exact (frame_pres_E22 (fun x => _get_HCR_EL2_Type_RW (reg64 x .HCR_EL2) = 1#1) (fun _ => rfl) hFrame).mpr h.hcrRW
  · exact (frame_pres_E22 (fun x => feature x .FEAT_RME = false ∨
        _get_SCR_EL3_Type_NSE (reg64 x .SCR_EL3) = 0#1 ∨ effectiveNS x = 1#1)
      (fun _ => rfl) hFrame).mpr h.validSecurity
  · exact (frame_pres_E22 (fun x => x.bank_Bool .SPESampleInFlight = false) (fun _ => rfl) hFrame).mpr h.spe
  · exact (frame_pres_E22 (fun x => reg64 x .PMINTENCLR_EL1 = 0#64) (fun _ => rfl) hFrame).mpr h.pmuIrqMask
  · exact (frame_pres_E22 (fun x => _get_BRBFCR_EL1_Type_PAUSED (reg64 x .BRBFCR_EL1) = 1#1) (fun _ => rfl) hFrame).mpr h.brbePaused
  · exact (frame_pres_E22 (fun x => 0 ≤ x.bank_Int .NUM_PMU_COUNTERS) (fun _ => rfl) hFrame).mpr h.pmuCountLower
  · exact (frame_pres_E22 (fun x => x.bank_Int .NUM_PMU_COUNTERS ≤ 31) (fun _ => rfl) hFrame).mpr h.pmuCountUpper
  · exact (frame_pres_E22 (fun x => _get_CNTCR_Type_SCEN (x.bank_BitVec_32 .CNTCR) = 0#1) (fun _ => rfl) hFrame).mpr h.ordinary
  · exact timersQuiet_after_E22_guarded_advance hFrame hBits hAdvance h.timers

/- Strict non-wrapping specialization, retained as a convenient internal API. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22.timerQuiet_after_count_and_bits"
  (← IO.getStderr).flush

theorem timerQuiet_after_count_and_bits {ticks : Nat} {r next : ArmFull.Regs}
    {active forced : Bool} {ctl nextCtl compare offset : BitVec 64}
    (h : TimerQuiet (ticks + 1) r active ctl compare offset forced)
    (hBits : CtlLowBitsEq ctl nextCtl)
    (hLower : physical r ≤ physical next)
    (hUpper : physical next ≤ physical r + 1) :
    TimerQuiet ticks next active nextCtl compare offset forced :=
  timerQuiet_after_guarded_count_and_bits h hBits (fun _ => ⟨hLower,hUpper⟩)

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22.timersQuiet_after_E22"
  (← IO.getStderr).flush

theorem timersQuiet_after_E22 {ticks : Nat} {r next : ArmFull.Regs}
    (hFrame : E22Frame r next) (hBits : TimerLowBitsEq r next)
    (hLower : physical r ≤ physical next)
    (hUpper : physical next ≤ physical r + 1)
    (h : TimersQuiet (ticks + 1) r) : TimersQuiet ticks next :=
  timersQuiet_after_E22_guarded_advance hFrame hBits (fun _ => ⟨hLower,hUpper⟩) h

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22.hookQuiet_after_E22"
  (← IO.getStderr).flush

theorem hookQuiet_after_E22 {ticks : Nat} {s t : NativeState}
    (h : HookQuiet (ticks + 1) s) (hFrame : E22Frame s.regs t.regs)
    (hBits : TimerLowBitsEq s.regs t.regs)
    (hLower : physical s.regs ≤ physical t.regs)
    (hUpper : physical t.regs ≤ physical s.regs + 1) : HookQuiet ticks t :=
  hookQuiet_after_E22_guarded_advance h hFrame hBits (fun _ => ⟨hLower,hUpper⟩)

#print axioms timerQuiet_after_guarded_count_and_bits
#print axioms timerQuiet_after_E22
#print axioms timersQuiet_after_E22_guarded_advance
#print axioms hookQuiet_after_E22_guarded_advance
#print axioms timerQuiet_after_count_and_bits
#print axioms timersQuiet_after_E22
#print axioms hookQuiet_after_E22

end ArmCert.HookQuiet.V0
