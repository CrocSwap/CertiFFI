import ArmCert.HookQuiet.V0.TransportE22
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

/- Pure same-budget transport, including budget zero. Actual native timer
banks must separately prove the frame, bit equalities and unchanged count. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22Same.timerQuiet_same_count_and_bits"
  (← IO.getStderr).flush

theorem timerQuiet_same_count_and_bits {ticks : Nat} {r next : ArmFull.Regs}
    {active forced : Bool} {ctl nextCtl compare offset : BitVec 64}
    (h : TimerQuiet ticks r active ctl compare offset forced)
    (hBits : CtlLowBitsEq ctl nextCtl) (hCount : physical next = physical r) :
    TimerQuiet ticks next active nextCtl compare offset forced := by
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (hBits.1.trans h))
  · exact Or.inr (Or.inr (Or.inl (hBits.2.trans h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    simpa only [Deadline, hCount] using h

/- Generic internal composition; all four stable selectors below are fixed
concrete functions at each use, and their erasure equalities are proved by rfl. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22Same.timerQuiet_same_budget_E22_core"
  (← IO.getStderr).flush

private theorem timerQuiet_same_budget_E22_core {ticks : Nat} {r next : ArmFull.Regs}
    (active : ArmFull.Regs → Bool) (ctl compare offset : ArmFull.Regs → BitVec 64)
    (forced : ArmFull.Regs → Bool)
    (ha : ∀ x, active (eraseE22 x) = active x)
    (hc : ∀ x, compare (eraseE22 x) = compare x)
    (ho : ∀ x, offset (eraseE22 x) = offset x)
    (hf : ∀ x, forced (eraseE22 x) = forced x)
    (hFrame : E22Frame r next)
    (hCount : physical next = physical r)
    (hBits : CtlLowBitsEq (ctl r) (ctl next))
    (h : TimerQuiet ticks r (active r) (ctl r) (compare r) (offset r) (forced r)) :
    TimerQuiet ticks next (active next) (ctl next) (compare next) (offset next) (forced next) := by
  rw [frame_pres_E22 active ha hFrame, frame_pres_E22 compare hc hFrame,
    frame_pres_E22 offset ho hFrame, frame_pres_E22 forced hf hFrame]
  exact timerQuiet_same_count_and_bits h hBits hCount

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22Same.timersQuiet_same_budget_E22"
  (← IO.getStderr).flush

theorem timersQuiet_same_budget_E22 {ticks : Nat} {r next : ArmFull.Regs}
    (hFrame : E22Frame r next) (hBits : TimerLowBitsEq r next)
    (hCount : physical next = physical r)
    (h : TimersQuiet ticks r) : TimersQuiet ticks next := by
  rcases h with ⟨hp,hhp,hhps,hps,hv,hhv,hhvs⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact timerQuiet_same_budget_E22_core (fun _ => true) (fun x => reg64 x .CNTP_CTL_EL0)
      (fun x => reg64 x .CNTP_CVAL_EL0) physicalOffset
      (fun x => realm x && (_get_CNTHCTL_EL2_Type_CNTPMASK (reg64 x .CNTHCTL_EL2) == 1#1))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hCount hBits.p hp
  · exact timerQuiet_same_budget_E22_core (fun _ => true) (fun x => reg64 x .CNTHP_CTL_EL2)
      (fun x => reg64 x .CNTHP_CVAL_EL2) (fun _ => 0#64) (fun _ => false)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hCount hBits.hp hhp
  · exact timerQuiet_same_budget_E22_core (fun x => feature x .FEAT_SEL2) (fun x => reg64 x .CNTHPS_CTL_EL2)
      (fun x => reg64 x .CNTHPS_CVAL_EL2) (fun _ => 0#64) (fun _ => false)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hCount hBits.hps hhps
  · exact timerQuiet_same_budget_E22_core (fun _ => true) (fun x => reg64 x .CNTPS_CTL_EL1)
      (fun x => reg64 x .CNTPS_CVAL_EL1) physicalOffset (fun _ => false)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hCount hBits.ps hps
  · exact timerQuiet_same_budget_E22_core (fun _ => true) (fun x => reg64 x .CNTV_CTL_EL0)
      (fun x => reg64 x .CNTV_CVAL_EL0) (fun x => reg64 x .CNTVOFF_EL2)
      (fun x => realm x && (_get_CNTHCTL_EL2_Type_CNTVMASK (reg64 x .CNTHCTL_EL2) == 1#1))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hCount hBits.v hv
  · exact timerQuiet_same_budget_E22_core (fun x => feature x .FEAT_VHE) (fun x => reg64 x .CNTHV_CTL_EL2)
      (fun x => reg64 x .CNTHV_CVAL_EL2) (fun _ => 0#64) (fun _ => false)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hCount hBits.hv hhv
  · exact timerQuiet_same_budget_E22_core (fun x => feature x .FEAT_SEL2 && feature x .FEAT_VHE)
      (fun x => reg64 x .CNTHVS_CTL_EL2) (fun x => reg64 x .CNTHVS_CVAL_EL2)
      (fun _ => 0#64) (fun _ => false)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hFrame hCount hBits.hvs hhvs

/- Predicate-only internal transport. The model owner must establish EVERY
input condition from the actual successful counter transition. This theorem
does not assert hook success, a BitVec progression law, GIC preservation, or SAT. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22Same.hookQuiet_same_budget_E22"
  (← IO.getStderr).flush

theorem hookQuiet_same_budget_E22 {ticks : Nat} {s t : NativeState}
    (h : HookQuiet ticks s) (hFrame : E22Frame s.regs t.regs)
    (hBits : TimerLowBitsEq s.regs t.regs)
    (hCount : physical t.regs = physical s.regs) :
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
  · exact timersQuiet_same_budget_E22 hFrame hBits hCount h.timers


/- Requested raw-register equality API; not a statement about an actual hook. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.TransportE22Same.hookQuiet_same_budget_E22_of_physicalCount_eq"
  (← IO.getStderr).flush

theorem hookQuiet_same_budget_E22_of_physicalCount_eq {ticks : Nat} {s t : NativeState}
    (h : HookQuiet ticks s) (hFrame : E22Frame s.regs t.regs)
    (hBits : TimerLowBitsEq s.regs t.regs)
    (hCount : t.regs.PhysicalCount = s.regs.PhysicalCount) : HookQuiet ticks t := by
  apply hookQuiet_same_budget_E22 h hFrame hBits
  exact congrArg (fun p : BitVec 88 => (Sail.BitVec.extractLsb p 87 24).toNat) hCount

#print axioms timerQuiet_same_count_and_bits
#print axioms timerQuiet_same_budget_E22_core
#print axioms timersQuiet_same_budget_E22
#print axioms hookQuiet_same_budget_E22
#print axioms hookQuiet_same_budget_E22_of_physicalCount_eq

end ArmCert.HookQuiet.V0
