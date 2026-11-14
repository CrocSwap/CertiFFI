import ArmFull.Fn.M0198
import ArmFull.Fn.M0202
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

namespace ArmCert.HookQuiet.V0

abbrev NativeState := SequentialState ArmFull.Regs oracleChoiceSource

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.feature"
  (← IO.getStderr).flush

def feature (r : ArmFull.Regs) (f : ArmFull.Feature) : Bool :=
  r.FeatureImpl[(num_of_Feature f).toNat]!

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.reg64"
  (← IO.getStderr).flush

def reg64 (r : ArmFull.Regs) (k : ArmFull.Bank_BitVec_64) : BitVec 64 :=
  r.bank_BitVec_64 k

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.physical"
  (← IO.getStderr).flush

def physical (r : ArmFull.Regs) : Nat :=
  (Sail.BitVec.extractLsb r.PhysicalCount 87 24).toNat

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.el2Enabled"
  (← IO.getStderr).flush

def el2Enabled (r : ArmFull.Regs) : Bool :=
  (_get_SCR_EL3_Type_NS (reg64 r .SCR_EL3) == 1#1) ||
  (feature r .FEAT_SEL2 && (_get_SCR_EL3_Type_EEL2 (reg64 r .SCR_EL3) == 1#1))

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.effectiveNS"
  (← IO.getStderr).flush

def effectiveNS (r : ArmFull.Regs) : BitVec 1 :=
  if feature r .FEAT_RME && !feature r .FEAT_SEL2 then 1#1
  else _get_SCR_EL3_Type_NS (reg64 r .SCR_EL3)

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.realm"
  (← IO.getStderr).flush

def realm (r : ArmFull.Regs) : Bool :=
  feature r .FEAT_RME &&
  (_get_SCR_EL3_Type_NSE (reg64 r .SCR_EL3) == 1#1) && (effectiveNS r == 1#1)

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.physicalOffset"
  (← IO.getStderr).flush

def physicalOffset (r : ArmFull.Regs) : BitVec 64 :=
  if feature r .FEAT_ECV &&
      (_get_CNTHCTL_EL2_Type_ECV (reg64 r .CNTHCTL_EL2) == 1#1) &&
      (_get_SCR_EL3_Type_ECVEn (reg64 r .SCR_EL3) == 1#1) && el2Enabled r
  then reg64 r .CNTPOFF_EL2 else 0#64

/- A concrete arithmetic deadline, with no modular count or offset wrap.
The budget counts future counter-update calls; each ordinary enabled update
advances the upper 64 bits of PhysicalCount by one. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.Deadline"
  (← IO.getStderr).flush

def Deadline (ticks : Nat) (r : ArmFull.Regs) (offset compare : BitVec 64) : Prop :=
  offset.toNat ≤ physical r ∧
  physical r + ticks < 2^64 ∧
  physical r + ticks - offset.toNat < compare.toNat

/- CTL low bits are ENABLE and IMASK in each listed A64 timer bank.
Inactive banks impose no condition. ISTATUS changes are allowed by E22. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.TimerQuiet"
  (← IO.getStderr).flush

def TimerQuiet (ticks : Nat) (r : ArmFull.Regs) (active : Bool)
    (ctl compare offset : BitVec 64) (forcedMask : Bool := false) : Prop :=
  active = false ∨ ctl.getLsbD 0 = false ∨ ctl.getLsbD 1 = true ∨
  forcedMask = true ∨ Deadline ticks r offset compare

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.TimersQuiet"
  (← IO.getStderr).flush

def TimersQuiet (ticks : Nat) (r : ArmFull.Regs) : Prop :=
  TimerQuiet ticks r true (reg64 r .CNTP_CTL_EL0) (reg64 r .CNTP_CVAL_EL0)
    (physicalOffset r)
    (realm r && (_get_CNTHCTL_EL2_Type_CNTPMASK (reg64 r .CNTHCTL_EL2) == 1#1)) ∧
  TimerQuiet ticks r true (reg64 r .CNTHP_CTL_EL2) (reg64 r .CNTHP_CVAL_EL2) 0#64 ∧
  TimerQuiet ticks r (feature r .FEAT_SEL2)
    (reg64 r .CNTHPS_CTL_EL2) (reg64 r .CNTHPS_CVAL_EL2) 0#64 ∧
  TimerQuiet ticks r true (reg64 r .CNTPS_CTL_EL1) (reg64 r .CNTPS_CVAL_EL1)
    (physicalOffset r) ∧
  TimerQuiet ticks r true (reg64 r .CNTV_CTL_EL0) (reg64 r .CNTV_CVAL_EL0)
    (reg64 r .CNTVOFF_EL2)
    (realm r && (_get_CNTHCTL_EL2_Type_CNTVMASK (reg64 r .CNTHCTL_EL2) == 1#1)) ∧
  TimerQuiet ticks r (feature r .FEAT_VHE)
    (reg64 r .CNTHV_CTL_EL2) (reg64 r .CNTHV_CVAL_EL2) 0#64 ∧
  TimerQuiet ticks r (feature r .FEAT_SEL2 && feature r .FEAT_VHE)
    (reg64 r .CNTHVS_CTL_EL2) (reg64 r .CNTHVS_CVAL_EL2) 0#64

/- PROPOSED development domain, not a ratified release premise.
All conditions are concrete input fields/arithmetic. No hook success, frame,
no-IRQ conclusion, future execution, or old global Hooks value occurs here.
This version explicitly supports ordinary SCEN=0 A64 EL0 executions, permits
enabled PMU/counters and enabled non-firing timers, and leaves oracle/GIC free.
Actual hook laws, prefix preservation and joint initial SAT are separate work. -/
run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.HookQuiet"
  (← IO.getStderr).flush

structure HookQuiet (ticks : Nat) (s : NativeState) : Prop where
  a64 : feature s.regs .FEAT_AA64EL0 = true
  el0 : s.regs.PSTATE.EL = 0#2
  nrw : s.regs.PSTATE.nRW = 0#1
  scrRW : _get_SCR_EL3_Type_RW (reg64 s.regs .SCR_EL3) = 1#1
  hcrRW : _get_HCR_EL2_Type_RW (reg64 s.regs .HCR_EL2) = 1#1
  validSecurity : feature s.regs .FEAT_RME = false ∨
    _get_SCR_EL3_Type_NSE (reg64 s.regs .SCR_EL3) = 0#1 ∨ effectiveNS s.regs = 1#1
  spe : s.regs.bank_Bool .SPESampleInFlight = false
  pmuIrqMask : reg64 s.regs .PMINTENCLR_EL1 = 0#64
  brbePaused : _get_BRBFCR_EL1_Type_PAUSED (reg64 s.regs .BRBFCR_EL1) = 1#1
  pmuCountLower : 0 ≤ s.regs.bank_Int .NUM_PMU_COUNTERS
  pmuCountUpper : s.regs.bank_Int .NUM_PMU_COUNTERS ≤ 31
  ordinary : _get_CNTCR_Type_SCEN (s.regs.bank_BitVec_32 .CNTCR) = 0#1
  timers : TimersQuiet ticks s.regs

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.deadline_mono"
  (← IO.getStderr).flush

theorem deadline_mono {a b : Nat} {r : ArmFull.Regs} {offset compare : BitVec 64}
    (hab : a ≤ b) (h : Deadline b r offset compare) : Deadline a r offset compare := by
  exact ⟨h.1, Nat.lt_of_le_of_lt (Nat.add_le_add_left hab _) h.2.1,
    Nat.lt_of_le_of_lt (Nat.sub_le_sub_right (Nat.add_le_add_left hab _) _) h.2.2⟩

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.timerQuiet_mono"
  (← IO.getStderr).flush

theorem timerQuiet_mono {a b : Nat} {r : ArmFull.Regs} {active forcedMask : Bool}
    {ctl compare offset : BitVec 64} (hab : a ≤ b)
    (h : TimerQuiet b r active ctl compare offset forcedMask) :
    TimerQuiet a r active ctl compare offset forcedMask := by
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (deadline_mono hab h))))

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.timersQuiet_mono"
  (← IO.getStderr).flush

theorem timersQuiet_mono {a b : Nat} {r : ArmFull.Regs} (hab : a ≤ b)
    (h : TimersQuiet b r) : TimersQuiet a r := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  exact ⟨timerQuiet_mono hab h0, timerQuiet_mono hab h1, timerQuiet_mono hab h2,
    timerQuiet_mono hab h3, timerQuiet_mono hab h4, timerQuiet_mono hab h5,
    timerQuiet_mono hab h6⟩

run_cmd do
  IO.eprintln "CURRENT_DECL ArmCert.HookQuiet.V0.Predicate.hookQuiet_mono"
  (← IO.getStderr).flush

theorem hookQuiet_mono {a b : Nat} {s : NativeState} (hab : a ≤ b)
    (h : HookQuiet b s) : HookQuiet a s :=
  { h with timers := timersQuiet_mono hab h.timers }

#print axioms deadline_mono
#print axioms timerQuiet_mono
#print axioms timersQuiet_mono
#print axioms hookQuiet_mono

end ArmCert.HookQuiet.V0
