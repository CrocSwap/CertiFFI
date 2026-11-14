import HookQuietCounters.TimerParts
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCore.bit_is_one"
  (← IO.getStderr).flush

theorem bit_is_one {w : Nat} (x : BitVec w) (i : Nat) :
    x.extractLsb' i 1 = 1#1 ↔ x.getLsbD i = true := by
  rw [BitVec.getLsbD_eq_extractLsb']
  simp

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCore.timer_quiet_success"
  (← IO.getStderr).flush

theorem timer_quiet_success (ticks : Nat) (s : NativeState)
    (active forced : Bool) (ctl compare offset : BitVec 64) (irq : InterruptID)
    (ha : active = true) (he : ctl.getLsbD 0 = true)
    (hq : ArmCert.HookQuiet.V0.TimerQuiet ticks s.regs active ctl compare offset forced) :
    (IsTimerConditionMet offset compare
      (if forced then 1#1 else ctl.extractLsb' 1 1) irq : SailM Bool) s =
      .ok (timerStatus s offset compare) s := by
  rcases hq with hi | hd | hm | hf | ht
  · simp [ha] at hi
  · have bad : (true : Bool) = false := he.symm.trans hd
    cases bad
  · have hm' := (bit_is_one ctl 1).mpr hm
    cases forced <;> simpa only [Bool.false_eq_true, ↓reduceIte, hm'] using timer_masked offset compare irq s
  · simpa only [hf, ↓reduceIte] using timer_masked offset compare irq s
  · have hle : offset ≤ physicalValue s := ht.1
    have hc : (physicalValue s - offset).toNat < compare.toNat := by
      rw [BitVec.toNat_sub_of_le hle]
      exact ArmCert.HookQuiet.V0.deadline_current ht
    have hs := timer_status_future offset compare s hc
    simpa only [hs] using timer_deadline ticks s offset compare _ irq ht

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCore.TimerKey"
  (← IO.getStderr).flush

def TimerKey (k : Bank_BitVec_64) : Prop :=
  k = .CNTP_CTL_EL0 ∨ k = .CNTHP_CTL_EL2 ∨ k = .CNTHPS_CTL_EL2 ∨
  k = .CNTPS_CTL_EL1 ∨ k = .CNTV_CTL_EL0 ∨ k = .CNTHV_CTL_EL2 ∨ k = .CNTHVS_CTL_EL2

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCore.TimerFrame"
  (← IO.getStderr).flush

structure TimerFrame (s t : NativeState) : Prop where
  frame : E22Frame s.regs t.regs
  bits : ArmCert.HookQuiet.V0.TimerLowBitsEq s.regs t.regs
  count : t.regs.PhysicalCount = s.regs.PhysicalCount
  gic : t.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending
  mem : t.mem = s.mem
  events : t.events = s.events
  choiceState : t.choiceState = s.choiceState
  tags : t.tags = s.tags
  cycleCount : t.cycleCount = s.cycleCount
  sailOutput : t.sailOutput = s.sailOutput

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCore.TimerFrame.refl"
  (← IO.getStderr).flush

theorem TimerFrame.refl (s : NativeState) : TimerFrame s s := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  constructor <;> exact ⟨rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCore.updateTimer"
  (← IO.getStderr).flush

def updateTimer (s : NativeState) (k : Bank_BitVec_64) (status : Bool) : NativeState :=
  let value := Sail.BitVec.updateSubrange (s.regs.bank_BitVec_64 k) 2 2
    (if status then 1#1 else 0#1)
  let r : Regs := {s.regs with bank_BitVec_64 := RegMap.set s.regs.bank_BitVec_64 k value}
  {s with regs := r}

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCore.update_timer_frame"
  (← IO.getStderr).flush

theorem update_timer_frame (s : NativeState) (k : Bank_BitVec_64) (status : Bool)
    (hk : TimerKey k) : TimerFrame s (updateTimer s k status) := by
  have hb (j : Bank_BitVec_64) :
      (eraseE22 (updateTimer s k status).regs).bank_BitVec_64 j = (eraseE22 s.regs).bank_BitVec_64 j := by
    by_cases hj : j = k
    · subst j
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · simp [eraseE22, updateTimer, RegMap.set, hj]
  have hbank := funext hb
  have hframe : E22Frame s.regs (updateTimer s k status).regs := by
    change eraseE22 (updateTimer s k status).regs = eraseE22 s.regs
    calc
      _ = {eraseE22 s.regs with bank_BitVec_64 := (eraseE22 (updateTimer s k status).regs).bank_BitVec_64} := rfl
      _ = _ := by rw [hbank]
  have hbit (j : Bank_BitVec_64) (i : Nat) (hi : i < 2) :
      ((updateTimer s k status).regs.bank_BitVec_64 j).getLsbD i =
        (s.regs.bank_BitVec_64 j).getLsbD i := by
    by_cases hj : j = k
    · subst j
      simp only [updateTimer, RegMap.set_same]
      exact update_low_bit _ _ (by omega) hi
    · simp [updateTimer, RegMap.set, hj]
  refine ⟨hframe, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  constructor <;> exact ⟨hbit _ 0 (by decide), hbit _ 1 (by decide)⟩

#print axioms bit_is_one
#print axioms timer_quiet_success
#print axioms update_timer_frame

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCore.write_apply"
  (← IO.getStderr).flush

theorem write_apply {α : Type} (r : ArmFull.RegisterRef α) (v : α) (s : NativeState) :
    (ArmFull.writeReg r v : SailM Unit) s = .ok () {s with regs := r.set v s.regs} := rfl

/- The real timer call remains in this normal form. `done` formats a pure
return value; it does not supply execution, frame, or guard answers. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCore.bankCheck"
  (← IO.getStderr).flush

def bankCheck {β : Type} (ctlKey compareKey : Bank_BitVec_64) (irq : InterruptID)
    (active forced : Bool) (offset : BitVec 64) (fallback : β)
    (done : BitVec 1 → Bool → β) : SailM β := fun s =>
  let ctl := s.regs.bank_BitVec_64 ctlKey
  let mask := if forced then 1#1 else ctl.extractLsb' 1 1
  if active && ctl.getLsbD 0 then
    (do
      let status ← IsTimerConditionMet offset (s.regs.bank_BitVec_64 compareKey) mask irq
      let current ← readReg (Regs.ref_BitVec_64 ctlKey)
      writeReg (Regs.ref_BitVec_64 ctlKey) (Sail.BitVec.updateSubrange current 2 2
        (if status then 1#1 else 0#1))
      pure (done mask status)) s
  else .ok fallback s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerCore.bank_check_total"
  (← IO.getStderr).flush

theorem bank_check_total {β : Type} (ticks : Nat) (s : NativeState)
    (ctlKey compareKey : Bank_BitVec_64) (irq : InterruptID)
    (active forced : Bool) (offset : BitVec 64) (fallback : β)
    (done : BitVec 1 → Bool → β) (hk : TimerKey ctlKey)
    (hq : ArmCert.HookQuiet.V0.TimerQuiet ticks s.regs active
      (s.regs.bank_BitVec_64 ctlKey) (s.regs.bank_BitVec_64 compareKey) offset forced) :
    ∃ v t, bankCheck ctlKey compareKey irq active forced offset fallback done s = .ok v t ∧
      TimerFrame s t := by
  unfold bankCheck
  by_cases hguard : (active && (s.regs.bank_BitVec_64 ctlKey).getLsbD 0) = true
  · have hand : active = true ∧ (s.regs.bank_BitVec_64 ctlKey).getLsbD 0 = true := by
      simpa using hguard
    obtain ⟨ha, he⟩ := hand
    have ht := timer_quiet_success ticks s active forced _ _ offset irq ha he hq
    let status := timerStatus s offset (s.regs.bank_BitVec_64 compareKey)
    let mask := if forced then 1#1 else (s.regs.bank_BitVec_64 ctlKey).extractLsb' 1 1
    refine ⟨done mask status, updateTimer s ctlKey status, ?_, update_timer_frame s ctlKey status hk⟩
    simp only [hguard, ↓reduceIte, bind_app, ht, read_apply, write_apply, pure_apply]
    rfl
  · exact ⟨fallback, s, by simp only [hguard, Bool.false_eq_true, ↓reduceIte], TimerFrame.refl s⟩

#print axioms bank_check_total

end HookQuietCounters
