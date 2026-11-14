import ArmCert.HookQuiet.V0.Deadline
import ArmCert.HookQuiet.V0.Predicate
import ArmCert.HookQuiet.V0.TransportE20
import ArmCert.HookQuiet.V0.TransportE22
import ArmCert.HookQuiet.V0.TransportE22Same
import Bridge.CruxCore
import Lean.Elab.Command
import NativeMteTagCheck.Primitive
import Sail.Common
import Sail.IntRange
import Sail.Sail

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeTagCheck.Hooks
def choiceView (s : ArmBridge.Draft.NativeState) := (s.choiceState, s.choiceOcc.getD 1354 0)
end NativeTagCheck.Hooks

-- Source proof structure: PMUOff.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUOff.pure_apply"
  (← IO.getStderr).flush

theorem pure_apply {α : Type} (a : α) (s : NativeState) :
    (pure a : SailM α) s = .ok a s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUOff.map_apply"
  (← IO.getStderr).flush

theorem map_apply {α β : Type} (f : α → β) (x : SailM α) (s : NativeState) :
    (f <$> x) s = match x s with
      | .ok a t => .ok (f a) t
      | .error e t => .error e t := by
  change EStateM.map f x s = _
  unfold EStateM.map
  cases x s <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUOff.read_spe"
  (← IO.getStderr).flush

theorem read_spe (s : NativeState) :
    (readReg SPESampleInFlight : SailM Bool) s =
      .ok (s.regs.bank_Bool .SPESampleInFlight) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUOff.read_pmcr"
  (← IO.getStderr).flush

theorem read_pmcr (s : NativeState) :
    (readReg PMCR_EL0 : SailM (BitVec 64)) s =
      .ok (s.regs.bank_BitVec_64 .PMCR_EL0) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUOff.read_mdcr"
  (← IO.getStderr).flush

theorem read_mdcr (s : NativeState) :
    (readReg MDCR_EL2 : SailM (BitVec 64)) s =
      .ok (s.regs.bank_BitVec_64 .MDCR_EL2) s := rfl

/- A semantic subcase of the proposed guard, proved over the real hook.
This is not the full HookQuiet predicate or its enabled-PMU contract. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUOff.pmu_event_off"
  (← IO.getStderr).flush

theorem pmu_event_off (e : BitVec 16) (s : NativeState)
    (hSpe : s.regs.bank_Bool .SPESampleInFlight = false)
    (hE : _get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0) = 0#1)
    (hH : _get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2) = 0#1) :
    (PMUEvent e : SailM Unit) s = .ok () s := by
  simp [PMUEvent, PMUEvent__1, bind_app, pure_apply, map_apply, read_spe, read_pmcr,
    read_mdcr, hSpe, hE, hH]

#print axioms pmu_event_off

end NativeTagCheck.Hooks

-- Source proof structure: Range.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

set_option autoImplicit false
set_option maxHeartbeats 100000


namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Range.stepValue"
  (← IO.getStderr).flush

def stepValue {β : Type} : ForInStep β → β
  | .done b => b
  | .yield b => b

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Range.estate_bind_apply"
  (← IO.getStderr).flush

theorem estate_bind_apply {ε σ α β : Type} (x : EStateM ε σ α)
    (f : α → EStateM ε σ β) (s : σ) :
    (x >>= f) s = match x s with
      | .ok a t => f a t
      | .error e t => .error e t := rfl

/- A total-state invariant for the actual Sail integer-range iterator. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Range.range_loop"
  (← IO.getStderr).flush

theorem range_loop {ε σ β : Type} (range : IntRange)
    (f : (i : Int) → i ∈ range → β → EStateM ε σ (ForInStep β))
    (I : β → σ → Prop)
    (step : ∀ i hi b s, I b s → ∃ v t, f i hi b s = .ok v t ∧ I (stepValue v) t)
    (b : β) (i : Int) (hs : (i - range.start) % range.step = 0) (s : σ)
    (hI : I b s) :
    ∃ c t, IntRange.forIn'.loop range f b i hs s = .ok c t ∧ I c t := by
  rw [IntRange.forIn'.loop]
  split
  · rename_i hi
    obtain ⟨v, t, hv, ht⟩ := step i hi b s hI
    cases v with
    | done c =>
      exact ⟨c, t, by simp only [estate_bind_apply, hv]; rfl, ht⟩
    | yield c =>
      obtain ⟨d, u, hd, hu⟩ := range_loop range f I step c (i + range.step) (by
        rw [Int.add_comm, Int.add_sub_assoc]
        simpa using hs) t ht
      exact ⟨d, u, by simpa only [estate_bind_apply, hv] using hd, hu⟩
  · exact ⟨b, s, rfl, hI⟩
termination_by if range.step > 0 then (range.stop - i + 1).toNat else (i - range.stop + 1).toNat
decreasing_by
  have hne := range.step_pos
  have hr : (if range.step > 0 then range.start ≤ i ∧ i ≤ range.stop
      else range.stop ≤ i ∧ i ≤ range.start) ∧ (i - range.start) % range.step = 0 :=
    by assumption
  split
  · rw [IntRange.toNat_lt_toNat]
    · simp_all [Membership.mem]; omega
    · simp_all [Membership.mem]; omega
  · rw [IntRange.toNat_lt_toNat]
    · simp_all [Membership.mem]; omega
    · simp_all [Membership.mem]; omega

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Range.range_preserves"
  (← IO.getStderr).flush

theorem range_preserves {ε σ β : Type} (range : IntRange)
    (f : (i : Int) → i ∈ range → β → EStateM ε σ (ForInStep β))
    (I : β → σ → Prop)
    (step : ∀ i hi b s, I b s → ∃ v t, f i hi b s = .ok v t ∧ I (stepValue v) t)
    (b : β) (s : σ) (hI : I b s) :
    ∃ c t, IntRange.forIn' range b f s = .ok c t ∧ I c t := by
  exact range_loop range f I step b range.start (by simp) s hI

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Range.range_forIn_preserves"
  (← IO.getStderr).flush

theorem range_forIn_preserves {ε σ β : Type} (range : IntRange)
    (f : Int → β → EStateM ε σ (ForInStep β))
    (I : β → σ → Prop)
    (step : ∀ i, i ∈ range → ∀ b s,
      I b s → ∃ v t, f i b s = .ok v t ∧ I (stepValue v) t)
    (b : β) (s : σ) (hI : I b s) :
    ∃ c t, forIn range b f s = .ok c t ∧ I c t := by
  exact range_preserves range (fun i _ b => f i b) I step b s hI

#print axioms range_loop
#print axioms range_preserves
#print axioms range_forIn_preserves

end NativeTagCheck.Hooks

-- Source proof structure: PMUBody.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUBody.featureValue"
  (← IO.getStderr).flush

def featureValue (s : NativeState) (f : Feature) : Bool :=
  s.regs.FeatureImpl[Sail.Int.toNatChecked (num_of_Feature f)]!

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUBody.feature_apply"
  (← IO.getStderr).flush

theorem feature_apply (f : Feature) (s : NativeState) :
    (IsFeatureImplemented f : SailM Bool) s = .ok (featureValue s f) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUBody.have_a64"
  (← IO.getStderr).flush

theorem have_a64 (s : NativeState) (h : featureValue s .FEAT_AA64EL0 = true) :
    (HaveAArch64 () : SailM Bool) s = .ok true s := by
  simp [HaveAArch64, bind_app, pure_apply, feature_apply, h]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUBody.using_a64"
  (← IO.getStderr).flush

theorem using_a64 (s : NativeState) (h : featureValue s .FEAT_AA64EL0 = true)
    (hn : s.regs.PSTATE.nRW = 0#1) :
    (UsingAArch32 () : SailM Bool) s = .ok false s := by
  have hr : (readReg PSTATE : SailM ProcState) s = .ok s.regs.PSTATE s := rfl
  simp [UsingAArch32, bind_app, pure_apply, hr, HaveAArch32, have_a64 s h, hn]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUBody.assert_true"
  (← IO.getStderr).flush

theorem assert_true (msg : String) (s : NativeState) :
    (ArmFull.assert true msg : SailM Unit) s = .ok () s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUBody.pmu_event2_acc"
  (← IO.getStderr).flush

theorem pmu_event2_acc (e : BitVec 16) (inc idx : Int) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (hn : s.regs.PSTATE.nRW = 0#1)
    (hl : 0 ≤ idx) (hu : idx < 31) :
    ∃ acc, (PMUEvent__2 e inc idx : SailM Unit) s =
      .ok () {s with regs := {s.regs with PMUEventAccumulator := acc}} := by
  have hp : (HavePMUv3 () : SailM Bool) s = .ok (featureValue s .FEAT_PMUv3) s := rfl
  have ht : (readReg PMEVTYPER_EL0 : SailM (Vector (BitVec 64) 32)) s =
    .ok (s.regs.bank_Vector_BitVec_64_32 .PMEVTYPER_EL0) s := rfl
  have hr : (readReg PMUEventAccumulator : SailM (Vector Int 31)) s =
    .ok s.regs.PMUEventAccumulator s := rfl
  have hb32 : ((0 ≤b idx) && (idx <b 32)) = true := by simp; omega
  have hb31 : ((0 ≤b idx) && (idx <b 31)) = true := by simp; omega
  cases hpv : featureValue s .FEAT_PMUv3 with
  | false =>
    simp only [PMUEvent__2, bind_app, hp, hpv, Bool.not_false,
      ↓reduceIte, pure_apply]
    exact ⟨s.regs.PMUEventAccumulator, rfl⟩
  | true =>
    simp only [PMUEvent__2, bind_app, hp, hpv, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, using_a64 s ha hn, hb32, hb31,
      assert_true, pure_apply, ht]
    split
    · simp only [bind_app, hr]
      exact ⟨_, rfl⟩
    · exact ⟨s.regs.PMUEventAccumulator, rfl⟩

#print axioms have_a64
#print axioms using_a64
#print axioms pmu_event2_acc

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUBody.eventLoop"
  (← IO.getStderr).flush

def eventLoop (e : BitVec 16) (inc counters : Int) : SailM Unit := do
  let mut loop_vars := ()
  for idx in [0:counters-1:1]i do
    let () := loop_vars
    loop_vars ← do PMUEvent__2 e inc idx
  pure loop_vars

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUBody.event_loop_acc"
  (← IO.getStderr).flush

theorem event_loop_acc (e : BitVec 16) (inc counters : Int) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (hn : s.regs.PSTATE.nRW = 0#1)
    (hu : counters ≤ 31) :
    ∃ acc, eventLoop e inc counters s =
      .ok () {s with regs := {s.regs with PMUEventAccumulator := acc}} := by
  let range : IntRange := [0:counters-1:1]i
  let I : Unit → NativeState → Prop := fun _ t =>
    ∃ acc, t = {s with regs := {s.regs with PMUEventAccumulator := acc}}
  let body : Int → Unit → SailM (ForInStep Unit) := fun i _ => do
    PMUEvent__2 e inc i
    pure (.yield ())
  have hs : I () s := ⟨s.regs.PMUEventAccumulator, rfl⟩
  have hstep : ∀ i, i ∈ range → ∀ b t, I b t →
      ∃ v u, body i b t = .ok v u ∧ I (stepValue v) u := by
    intro i hi b t ht
    obtain ⟨acc, rfl⟩ := ht
    have bounds : 0 ≤ i ∧ i ≤ counters - 1 := by
      simpa [range, Membership.mem] using hi
    obtain ⟨next, hnext⟩ := pmu_event2_acc e inc i
      {s with regs := {s.regs with PMUEventAccumulator := acc}} ha hn bounds.1 (by omega)
    refine ⟨.yield (), {s with regs := {s.regs with PMUEventAccumulator := next}}, ?_, ?_⟩
    · simp only [body, bind_app, hnext, pure_apply]
    · exact ⟨next, rfl⟩
  obtain ⟨b, t, ht, hI⟩ := range_forIn_preserves range body I hstep () s hs
  obtain ⟨acc, rfl⟩ := hI
  cases b
  refine ⟨acc, ?_⟩
  change ((forIn range () body) >>= fun b => pure b) s = _
  simp only [bind_app, ht, pure_apply]

#print axioms event_loop_acc

end NativeTagCheck.Hooks

-- Source proof structure: Queries.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.if_apply"
  (← IO.getStderr).flush

theorem if_apply {α β : Type} (p : Prop) [Decidable p] (f g : α → β) (a : α) :
    (if p then f else g) a = if p then f a else g a := by split <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.afterOcc"
  (← IO.getStderr).flush

def afterOcc (site : Nat) (s : NativeState) : NativeState :=
  {s with choiceOcc := s.choiceOcc.insert site (s.choiceOcc.getD site 0 + 1)}

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.occ_apply"
  (← IO.getStderr).flush

theorem occ_apply (site : Nat) (s : NativeState) :
    (occLabel site : SailM ChoiceLabel) s =
      .ok (.occ site (s.choiceOcc.getD site 0)) (afterOcc site s) := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.read_apply"
  (← IO.getStderr).flush

theorem read_apply {α : Type} (r : RegisterRef Regs α) (s : NativeState) :
    (readReg r : SailM α) s = .ok (r.get s.regs) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.unknown_bool"
  (← IO.getStderr).flush

theorem unknown_bool (s : NativeState) :
    (__UNKNOWN_boolean () : SailM Bool) s =
      .ok (oracleChoiceSource.chooseAt .bool (.occ 8 (s.choiceOcc.getD 8 0)) s.choiceState)
        (afterOcc 8 s) := rfl

@[simp] theorem afterOcc_regs (site : Nat) (s : NativeState) :
    (afterOcc site s).regs = s.regs := rfl

@[simp] theorem afterOcc_feature (site : Nat) (s : NativeState) (f : Feature) :
    featureValue (afterOcc site s) f = featureValue s f := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.scr_gen"
  (← IO.getStderr).flush

theorem scr_gen (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    (SCR_GEN_read () : SailM (BitVec 64)) s =
      .ok (s.regs.bank_BitVec_64 .SCR_EL3) (afterOcc 490 s) := by
  have ha' : featureValue (afterOcc 490 s) .FEAT_AA64EL0 = true := ha
  simp only [SCR_GEN_read, HaveEL, bind_app, assert_true, occ_apply, ubv,
    have_a64 _ ha', Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    read_apply, pure_apply]
  rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.secure_below"
  (← IO.getStderr).flush

theorem secure_below (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    (IsSecureBelowEL3 () : SailM Bool) s =
      .ok (_get_SCRType_NS (s.regs.bank_BitVec_64 .SCR_EL3) == 0#1) (afterOcc 490 s) := by
  simp only [IsSecureBelowEL3, HaveEL, ↓reduceIte, bind_app, scr_gen s ha, pure_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.el_state_k0"
  (← IO.getStderr).flush

theorem el_state_k0 (secure : Bool) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true)
    (he : s.regs.PSTATE.EL = 0#2) (hn : s.regs.PSTATE.nRW = 0#1)
    (hscr : _get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
    (hhcr : _get_HCR_EL2_Type_RW (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1) :
    (ELStateUsingAArch32K 0#2 secure : SailM (Bool × Bool)) s =
      .ok (true, false) (afterOcc 8 s) := by
  cases secure <;>
    cases hsel : featureValue s .FEAT_SEL2 <;>
    cases hvhe : featureValue s .FEAT_VHE <;>
    by_cases hhost : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) +++
      _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 3#2 <;>
    by_cases heel0 : _get_SCR_EL3_Type_EEL2 (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1 <;>
    by_cases heel1 : _get_SCR_EL3_Type_EEL2 (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1 <;>
    simp [ELStateUsingAArch32K, HaveAArch32EL, HaveEL, EL0, EL1, EL2, EL3,
      bind_app, pure_apply, map_apply, if_apply, read_apply, have_a64 _ ha, unknown_bool,
      HaveSecureEL2Ext, HaveVirtHostExt, feature_apply, hscr, hhcr, he, hn, hsel, hvhe,
      hhost, heel0, heel1]
  all_goals split <;> simp_all [bind_app, pure_apply, map_apply, if_apply,
    read_apply, feature_apply]

#print axioms scr_gen
#print axioms secure_below
#print axioms el_state_k0

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.el_state0"
  (← IO.getStderr).flush

theorem el_state0 (secure : Bool) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true)
    (he : s.regs.PSTATE.EL = 0#2) (hn : s.regs.PSTATE.nRW = 0#1)
    (hscr : _get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
    (hhcr : _get_HCR_EL2_Type_RW (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1) :
    (ELStateUsingAArch32 0#2 secure : SailM Bool) s =
      .ok false (afterOcc 8 (afterOcc 488 (afterOcc 487 s))) := by
  have hk := el_state_k0 secure (afterOcc 488 (afterOcc 487 s)) ha he hn hscr hhcr
  simp only [ELStateUsingAArch32, bind_app, occ_apply, ubool, hk, assert_true, pure_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.el_state_nonzero"
  (← IO.getStderr).flush

theorem el_state_nonzero (el : BitVec 2) (secure : Bool) (s : NativeState)
    (he : el ≠ 0#2) :
    (ELStateUsingAArch32 el secure : SailM Bool) s =
      .ok false (afterOcc 488 (afterOcc 487 s)) := by
  have hk (t : NativeState) : (ELStateUsingAArch32K el secure : SailM (Bool × Bool)) t =
      .ok (true, false) t := by
    simp [ELStateUsingAArch32K, HaveAArch32EL, EL0, he, pure_apply]
  simp only [ELStateUsingAArch32, bind_app, occ_apply, ubool, hk, assert_true, pure_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.el0QueryState"
  (← IO.getStderr).flush

def el0QueryState (s : NativeState) : NativeState :=
  afterOcc 8 (afterOcc 488 (afterOcc 487 (afterOcc 490 s)))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.el_using0"
  (← IO.getStderr).flush

theorem el_using0 (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true)
    (he : s.regs.PSTATE.EL = 0#2) (hn : s.regs.PSTATE.nRW = 0#1)
    (hscr : _get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
    (hhcr : _get_HCR_EL2_Type_RW (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1) :
    (ELUsingAArch32 0#2 : SailM Bool) s = .ok false (el0QueryState s) := by
  simp only [ELUsingAArch32, bind_app, secure_below s ha,
    el_state0 _ (afterOcc 490 s) ha he hn hscr hhcr, el0QueryState]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.el_using_nonzero"
  (← IO.getStderr).flush

theorem el_using_nonzero (el : BitVec 2) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (he : el ≠ 0#2) :
    (ELUsingAArch32 el : SailM Bool) s =
      .ok false (afterOcc 488 (afterOcc 487 (afterOcc 490 s))) := by
  simp only [ELUsingAArch32, bind_app, secure_below s ha, el_state_nonzero _ _ _ he]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.branch_record_paused0"
  (← IO.getStderr).flush

theorem branch_record_paused0 (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true)
    (he : s.regs.PSTATE.EL = 0#2) (hn : s.regs.PSTATE.nRW = 0#1)
    (hscr : _get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
    (hhcr : _get_HCR_EL2_Type_RW (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
    (hp : _get_BRBFCR_EL1_Type_PAUSED (s.regs.bank_BitVec_64 .BRBFCR_EL1) = 1#1) :
    (BranchRecordAllowed 0#2 : SailM Bool) s = .ok false (el0QueryState s) := by
  simp [BranchRecordAllowed, bind_app, el_using0 s ha he hn hscr hhcr,
    pure_apply, read_apply, el0QueryState, afterOcc, hp]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Queries.should_brbe_paused"
  (← IO.getStderr).flush

theorem should_brbe_paused (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true)
    (he : s.regs.PSTATE.EL = 0#2) (hn : s.regs.PSTATE.nRW = 0#1)
    (hscr : _get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
    (hhcr : _get_HCR_EL2_Type_RW (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
    (hp : _get_BRBFCR_EL1_Type_PAUSED (s.regs.bank_BitVec_64 .BRBFCR_EL1) = 1#1) :
    (ShouldBRBEFreeze () : SailM Bool) s = .ok false (el0QueryState s) := by
  simp [ShouldBRBEFreeze, bind_app, read_apply, he,
    branch_record_paused0 s ha he hn hscr hhcr hp, pure_apply]

#print axioms el_state0
#print axioms el_state_nonzero
#print axioms el_using0
#print axioms el_using_nonzero
#print axioms branch_record_paused0
#print axioms should_brbe_paused

end NativeTagCheck.Hooks

-- Source proof structure: CycleOff.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CycleOff.pmu_cycle_off"
  (← IO.getStderr).flush

theorem pmu_cycle_off (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true)
    (he : s.regs.PSTATE.EL = 0#2) (hn : s.regs.PSTATE.nRW = 0#1)
    (hscr : _get_SCR_EL3_Type_RW (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
    (hhcr : _get_HCR_EL2_Type_RW (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
    (hp : _get_BRBFCR_EL1_Type_PAUSED (s.regs.bank_BitVec_64 .BRBFCR_EL1) = 1#1)
    (hE : _get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0) = 0#1)
    (hH : _get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2) = 0#1) :
    (AArch64_PMUCycle () : SailM Unit) s = .ok () (el0QueryState s) := by
  simp [AArch64_PMUCycle, bind_app, pure_apply, map_apply, read_pmcr, read_mdcr,
    hE, hH, should_brbe_paused s ha he hn hscr hhcr hp]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CycleOff.pmu_cycle_off_quiet"
  (← IO.getStderr).flush

theorem pmu_cycle_off_quiet (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s)
    (hE : _get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0) = 0#1)
    (hH : _get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2) = 0#1) :
    ∃ t, (AArch64_PMUCycle () : SailM Unit) s = .ok () t ∧
      E20Frame s.regs t.regs ∧
      t.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending ∧
      t.mem = s.mem ∧ t.events = s.events ∧
      ArmCert.HookQuiet.V0.HookQuiet budget t := by
  refine ⟨el0QueryState s,
    pmu_cycle_off s q.a64 q.el0 q.nrw q.scrRW q.hcrRW q.brbePaused hE hH,
    rfl, rfl, rfl, rfl, ?_⟩
  exact ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq (s := s) (t := el0QueryState s) rfl q

#print axioms pmu_cycle_off
#print axioms pmu_cycle_off_quiet

end NativeTagCheck.Hooks

-- Source proof structure: Security.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.me_bind_apply"
  (← IO.getStderr).flush

theorem me_bind_apply {ρ α β : Type} (x : SailME ρ α) (f : α → SailME ρ β)
    (s : NativeState) :
    (@ExceptT.run (Sail.Error exception ⊕ ρ) SailM β ((x >>= f) : SailME ρ β)) s = match (@ExceptT.run (Sail.Error exception ⊕ ρ) SailM α x) s with
      | .ok (.ok a) t => (@ExceptT.run (Sail.Error exception ⊕ ρ) SailM β (f a)) t
      | .ok (.error e) t => .ok (.error e) t
      | .error e t => .error e t := by
  change EStateM.bind x (ExceptT.bindCont f) s = _
  unfold EStateM.bind ExceptT.run
  cases x s with
  | error e t => rfl
  | ok v t => cases v <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.me_lift_apply"
  (← IO.getStderr).flush

theorem me_lift_apply {ρ α : Type} (x : SailM α) (s : NativeState) :
    (@ExceptT.run (Sail.Error exception ⊕ ρ) SailM α (monadLift x : SailME ρ α)) s = match x s with
      | .ok a t => .ok (.ok a) t
      | .error e t => .error e t := by
  change EStateM.map Except.ok x s = _
  unfold EStateM.map
  cases x s <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.me_pure_apply"
  (← IO.getStderr).flush

theorem me_pure_apply {ρ α : Type} (a : α) (s : NativeState) :
    (@ExceptT.run (Sail.Error exception ⊕ ρ) SailM α (pure a : SailME ρ α)) s = .ok (.ok a) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.me_map_apply"
  (← IO.getStderr).flush

theorem me_map_apply {ρ α β : Type} (f : α → β) (x : SailME ρ α) (s : NativeState) :
    (@ExceptT.run (Sail.Error exception ⊕ ρ) SailM β (f <$> x)) s =
      match (@ExceptT.run (Sail.Error exception ⊕ ρ) SailM α x) s with
      | .ok (.ok a) t => .ok (.ok (f a)) t
      | .ok (.error e) t => .ok (.error e) t
      | .error e t => .error e t := by
  change EStateM.bind x _ s = _
  unfold EStateM.bind ExceptT.run
  cases x s with
  | error e t => rfl
  | ok v t => cases v <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.me_run_apply"
  (← IO.getStderr).flush

theorem me_run_apply {α : Type} (x : SailME α α) (s : NativeState) :
    ArmFull.SailME.run x s = match (@ExceptT.run (Sail.Error exception ⊕ α) SailM α x) s with
      | .ok (.ok a) t => .ok a t
      | .ok (.error (.inr a)) t => .ok a t
      | .ok (.error (.inl e)) t => .error e t
      | .error e t => .error e t := by
  unfold ArmFull.SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  rw [bind_app]
  cases (@ExceptT.run (Sail.Error exception ⊕ α) SailM α x) s with
  | error e t => rfl
  | ok v t => cases v with
    | ok a => rfl
    | error e => cases e <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.securityNoRMEState"
  (← IO.getStderr).flush

def securityNoRMEState (s : NativeState) : NativeState :=
  afterOcc 488 (afterOcc 487 (afterOcc 490 (afterOcc 503 s)))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.security_no_rme"
  (← IO.getStderr).flush

theorem security_no_rme (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true)
    (hr : featureValue s .FEAT_RME = false) :
    (SecurityStateAtEL 0#2 : SailM SecurityState) s =
      .ok (if _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1
        then .SS_NonSecure else .SS_Secure) (securityNoRMEState s) := by
  have hEL3 := el_using_nonzero 3#2 (afterOcc 503 s) ha (by decide)
  simp [SecurityStateAtEL, liftM, me_run_apply, me_bind_apply, me_lift_apply, me_pure_apply, me_map_apply,
    bind_app, pure_apply, map_apply, occ_apply, ubv, HaveRME,
    feature_apply, hr, HaveEL, EL0, EL2, EL3, hEL3, assert_true,
    read_apply, securityNoRMEState]

#print axioms security_no_rme

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.bit_cases"
  (← IO.getStderr).flush

theorem bit_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  have h : x.toNat = 0 ∨ x.toNat = 1 := by have := x.isLt; omega
  rcases h with h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (BitVec.eq_of_toNat_eq h)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.effectiveNSValue"
  (← IO.getStderr).flush

def effectiveNSValue (s : NativeState) : BitVec 1 :=
  if featureValue s .FEAT_RME && !featureValue s .FEAT_SEL2 then 1#1
  else _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.effective_ns"
  (← IO.getStderr).flush

theorem effective_ns (s : NativeState) :
    (EffectiveSCR_EL3_NS () : SailM (BitVec 1)) s = .ok (effectiveNSValue s) s := by
  cases hr : featureValue s .FEAT_RME <;>
    cases hs : featureValue s .FEAT_SEL2 <;>
    simp [EffectiveSCR_EL3_NS, HaveSecureState, HaveEL, HaveRME, HaveSecureEL2Ext,
      bind_app, pure_apply, map_apply, feature_apply, read_apply, effectiveNSValue, hr, hs]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.me_throw_apply"
  (← IO.getStderr).flush

theorem me_throw_apply {ρ α : Type} (a : ρ) (s : NativeState) :
    (@ExceptT.run (Sail.Error exception ⊕ ρ) SailM α (ArmFull.SailME.throw a)) s =
      .ok (.error (.inr a)) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.securityRMEValue"
  (← IO.getStderr).flush

def securityRMEValue (s : NativeState) : SecurityState :=
  if _get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3) == 0#1 then
    if effectiveNSValue s == 0#1 then .SS_Secure else .SS_NonSecure
  else .SS_Realm

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.security_rme"
  (← IO.getStderr).flush

theorem security_rme (s : NativeState)
    (hr : featureValue s .FEAT_RME = true)
    (hv : _get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1 ∨
      effectiveNSValue s = 1#1) :
    (SecurityStateAtEL 0#2 : SailM SecurityState) s =
      .ok (securityRMEValue s) (afterOcc 503 s) := by
  cases hs : featureValue s .FEAT_SEL2 <;>
    rcases bit_cases (_get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3)) with hnse | hnse <;>
    rcases bit_cases (_get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3)) with hns | hns <;>
    simp_all [SecurityStateAtEL, liftM, me_run_apply, me_bind_apply, me_lift_apply,
      me_pure_apply, me_map_apply, me_throw_apply, occ_apply, ubv, HaveRME,
      HaveSecureEL2Ext, feature_apply, read_apply, effective_ns, effectiveNSValue,
      securityRMEValue, EL0, EL3]

#print axioms bit_cases
#print axioms effective_ns
#print axioms security_rme

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.securityValue"
  (← IO.getStderr).flush

def securityValue (s : NativeState) : SecurityState :=
  if featureValue s .FEAT_RME then securityRMEValue s
  else if _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1
    then .SS_NonSecure else .SS_Secure

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.securityQueryState"
  (← IO.getStderr).flush

def securityQueryState (s : NativeState) : NativeState :=
  if featureValue s .FEAT_RME then afterOcc 503 s else securityNoRMEState s

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.security0_quiet"
  (← IO.getStderr).flush

theorem security0_quiet (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    (SecurityStateAtEL 0#2 : SailM SecurityState) s =
      .ok (securityValue s) (securityQueryState s) := by
  cases hr : featureValue s .FEAT_RME with
  | false =>
    simpa only [securityValue, securityQueryState, hr, Bool.false_eq_true, ↓reduceIte]
      using security_no_rme s q.a64 hr
  | true =>
    have hv : _get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1 ∨
        effectiveNSValue s = 1#1 := by
      rcases q.validSecurity with hf | hnse | hns
      · have hf' : featureValue s .FEAT_RME = false := hf
        simp [hr] at hf'
      · exact Or.inl hnse
      · exact Or.inr hns
    simpa only [securityValue, securityQueryState, hr, ↓reduceIte]
      using security_rme s hr hv

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Security.current_security_quiet"
  (← IO.getStderr).flush

theorem current_security_quiet (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    (CurrentSecurityState () : SailM SecurityState) s =
      .ok (securityValue s) (securityQueryState s) := by
  simp only [CurrentSecurityState, bind_app, read_apply]
  change SecurityStateAtEL s.regs.PSTATE.EL s = _
  rw [q.el0]
  exact security0_quiet budget s q

#print axioms security0_quiet
#print axioms current_security_quiet

end NativeTagCheck.Hooks

-- Source proof structure: PMUEventNonRetired.lean
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
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventNonRetired.get_num_counters"
  (← IO.getStderr).flush

theorem get_num_counters (s : NativeState) :
    (GetNumEventCounters () : SailM Int) s = .ok (s.regs.bank_Int .NUM_PMU_COUNTERS) s := rfl

/- Full enabled/disabled PMU paths for events that do not increment ICNTR. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventNonRetired.pmu_event_nonretired_acc"
  (← IO.getStderr).flush

theorem pmu_event_nonretired_acc (e : BitVec 16) (inc : Int) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (hn : s.regs.PSTATE.nRW = 0#1)
    (hs : s.regs.bank_Bool .SPESampleInFlight = false)
    (hu : s.regs.bank_Int .NUM_PMU_COUNTERS ≤ 31)
    (he : e ≠ PMU_EVENT_INST_RETIRED) :
    ∃ acc, (PMUEvent__1 e inc : SailM Unit) s =
      .ok () {s with regs := {s.regs with PMUEventAccumulator := acc}} := by
  obtain ⟨acc, hacc⟩ := event_loop_acc e inc (s.regs.bank_Int .NUM_PMU_COUNTERS) s ha hn hu
  simp [eventLoop] at hacc
  let t := {s with regs := {s.regs with PMUEventAccumulator := acc}}
  have hat (a : Vector Int 31) : (HaveAArch64 () : SailM Bool)
      {s with regs := {s.regs with PMUEventAccumulator := a}} =
      .ok true {s with regs := {s.regs with PMUEventAccumulator := a}} := have_a64 _ ha
  have hit (a : Vector Int 31) : (HavePMUv3ICNTR () : SailM Bool)
      {s with regs := {s.regs with PMUEventAccumulator := a}} =
      .ok (featureValue s .FEAT_PMUv3_ICNTR) {s with regs := {s.regs with PMUEventAccumulator := a}} := rfl
  rcases bit_cases (_get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0)) with hE | hE <;>
    rcases bit_cases (_get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2)) with hH | hH <;>
    by_cases hN : s.regs.bank_Int .NUM_PMU_COUNTERS = 0 <;>
    cases hI : featureValue s .FEAT_PMUv3_ICNTR <;>
    simp [PMUEvent__1, bind_app, pure_apply, map_apply, read_spe, hs,
      read_pmcr, read_mdcr, hE, hH, get_num_counters, hN, hacc, hat, hit,
      HavePMUv3ICNTR, have_a64, ha, feature_apply, hI, he] <;>
    first | exact ⟨s.regs.PMUEventAccumulator, rfl⟩ | exact ⟨acc, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventNonRetired.PMUPost"
  (← IO.getStderr).flush

structure PMUPost (budget : Nat) (s t : NativeState) : Prop where
  frame : E20Frame s.regs t.regs
  gic : t.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending
  mem : t.mem = s.mem
  events : t.events = s.events
  choiceState : choiceView t = choiceView s
  tags : t.tags = s.tags
  cycleCount : t.cycleCount = s.cycleCount
  sailOutput : t.sailOutput = s.sailOutput
  quiet : ArmCert.HookQuiet.V0.HookQuiet budget t

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventNonRetired.pmu_event_nonretired_total"
  (← IO.getStderr).flush

theorem pmu_event_nonretired_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (e : BitVec 16)
    (he : e ≠ PMU_EVENT_INST_RETIRED) :
    ∃ t, (PMUEvent e : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨acc, hacc⟩ := pmu_event_nonretired_acc e 1 s q.a64 q.nrw q.spe q.pmuCountUpper he
  let t := {s with regs := {s.regs with PMUEventAccumulator := acc}}
  have hf : E20Frame s.regs t.regs := rfl
  refine ⟨t, hacc, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact ArmCert.HookQuiet.V0.hookQuiet_of_E20Frame hf q

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventNonRetired.pmu_spec_total"
  (← IO.getStderr).flush

theorem pmu_spec_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  exact pmu_event_nonretired_total budget s q PMU_EVENT_INST_SPEC (by decide)
#print axioms get_num_counters
#print axioms pmu_event_nonretired_acc
#print axioms pmu_event_nonretired_total
#print axioms pmu_spec_total
end NativeTagCheck.Hooks

-- Source proof structure: Timer.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Timer.physicalValue"
  (← IO.getStderr).flush

def physicalValue (s : NativeState) : BitVec 64 :=
  Sail.BitVec.extractLsb s.regs.PhysicalCount 87 24

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Timer.timerStatus"
  (← IO.getStderr).flush

def timerStatus (s : NativeState) (offset deadline : BitVec 64) : Bool :=
  (((BitVec.toNat (physicalValue s - offset)) -i (BitVec.toNat deadline)) ≥b 0)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Timer.physical_count_apply"
  (← IO.getStderr).flush

theorem physical_count_apply (s : NativeState) :
    (PhysicalCountInt () : SailM (BitVec 64)) s = .ok (physicalValue s) s := rfl

/- The model does not clear an existing pending interrupt on a low signal. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Timer.irq_low"
  (← IO.getStderr).flush

theorem irq_low (irq : InterruptID) (s : NativeState) :
    (SetInterruptRequestLevel irq Signal.Signal_Low : SailM Unit) s = .ok () s := by
  have h : (Signal.Signal_Low == Signal.Signal_High) = false := by decide
  simp only [SetInterruptRequestLevel, bind_app, pure_apply, map_apply, h,
    Bool.false_eq_true, ↓reduceIte]

/- Masking suppresses the interrupt write, but does not force ISTATUS false. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Timer.timer_masked"
  (← IO.getStderr).flush

theorem timer_masked (offset deadline : BitVec 64) (irq : InterruptID) (s : NativeState) :
    (IsTimerConditionMet offset deadline 1#1 irq : SailM Bool) s =
      .ok (timerStatus s offset deadline) s := by
  simp [IsTimerConditionMet, bind_app, pure_apply, map_apply,
    physical_count_apply, timerStatus, irq_low]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Timer.timer_status_future"
  (← IO.getStderr).flush

theorem timer_status_future (offset deadline : BitVec 64) (s : NativeState)
    (h : (physicalValue s - offset).toNat < deadline.toNat) :
    timerStatus s offset deadline = false := by
  change decide (((physicalValue s - offset).toNat : Int) - (deadline.toNat : Int) ≥ 0) = false
  simp only [decide_eq_false_iff_not]
  omega

/- The input is a concrete unsigned comparison after the model's modular subtraction.
No-wrap propagation for a future horizon is a separate arithmetic obligation. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.Timer.timer_future"
  (← IO.getStderr).flush

theorem timer_future (offset deadline : BitVec 64) (mask : BitVec 1)
    (irq : InterruptID) (s : NativeState)
    (h : (physicalValue s - offset).toNat < deadline.toNat) :
    (IsTimerConditionMet offset deadline mask irq : SailM Bool) s = .ok false s := by
  have hs := timer_status_future offset deadline s h
  simp only [timerStatus] at hs
  simp only [IsTimerConditionMet, bind_app, pure_apply, map_apply, physical_count_apply]
  simp only [hs, Bool.false_and, Bool.false_eq_true, ↓reduceIte, irq_low, pure_apply]

#print axioms irq_low
#print axioms timer_masked
#print axioms timer_status_future
#print axioms timer_future

end NativeTagCheck.Hooks

-- Source proof structure: CounterArithmetic.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterArithmetic.extract_updated"
  (← IO.getStderr).flush

theorem extract_updated {w hi lo : Nat} (x : BitVec w) (y : BitVec (hi-lo+1))
    (hfit : hi < w) (horder : lo ≤ hi) :
    Sail.BitVec.extractLsb (Sail.BitVec.updateSubrange x hi lo y) hi lo = y := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi'
  have hw : lo + i < w := by omega
  have hl : ¬lo + i < lo := by omega
  have hy : lo + i - lo < hi - lo + 1 := by omega
  simp [Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    BitVec.zeroExtend, hw, hl, hy, hi']

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterArithmetic.update_low_bit"
  (← IO.getStderr).flush

theorem update_low_bit {w hi lo i : Nat} (x : BitVec w) (y : BitVec (hi-lo+1))
    (hfit : i < w) (hlow : i < lo) :
    (Sail.BitVec.updateSubrange x hi lo y).getLsbD i = x.getLsbD i := by
  simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend,
    hfit, hlow]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterArithmetic.advanceCount"
  (← IO.getStderr).flush

def advanceCount (s : NativeState) : NativeState :=
  let counterValue := Sail.BitVec.updateSubrange s.regs.PhysicalCount 87 24
    (BitVec.addInt (Sail.BitVec.extractLsb s.regs.PhysicalCount 87 24) 1)
  let r : Regs := {s.regs with PhysicalCount := counterValue}
  {s with regs := r}

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterArithmetic.physical_advance"
  (← IO.getStderr).flush

theorem physical_advance (s : NativeState) :
    physicalValue (advanceCount s) = BitVec.addInt (physicalValue s) 1 := by
  exact extract_updated (w := 88) (hi := 87) (lo := 24) s.regs.PhysicalCount
    (BitVec.addInt (physicalValue s) 1) (by decide) (by decide)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterArithmetic.advance_no_wrap"
  (← IO.getStderr).flush

theorem advance_no_wrap (budget : Nat) (s : NativeState)
    (h : ArmCert.HookQuiet.V0.physical s.regs + (budget+1) < 2^64) :
    ArmCert.HookQuiet.V0.physical s.regs ≤ ArmCert.HookQuiet.V0.physical (advanceCount s).regs ∧
    ArmCert.HookQuiet.V0.physical (advanceCount s).regs ≤ ArmCert.HookQuiet.V0.physical s.regs + 1 := by
  change (physicalValue s).toNat ≤ (physicalValue (advanceCount s)).toNat ∧
    (physicalValue (advanceCount s)).toNat ≤ (physicalValue s).toNat + 1
  rw [physical_advance]
  have hsmall : (physicalValue s).toNat + 1 < 2^64 := by
    change (physicalValue s).toNat + (budget+1) < 2^64 at h
    omega
  simp [BitVec.addInt, BitVec.toNat_add, Nat.mod_eq_of_lt hsmall]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterArithmetic.timer_deadline"
  (← IO.getStderr).flush

theorem timer_deadline (ticks : Nat) (s : NativeState) (offset compare : BitVec 64)
    (mask : BitVec 1) (irq : InterruptID)
    (h : ArmCert.HookQuiet.V0.Deadline ticks s.regs offset compare) :
    (IsTimerConditionMet offset compare mask irq : SailM Bool) s = .ok false s := by
  apply timer_future
  have hle : offset ≤ physicalValue s := h.1
  rw [BitVec.toNat_sub_of_le hle]
  exact ArmCert.HookQuiet.V0.deadline_current h

#print axioms extract_updated
#print axioms update_low_bit
#print axioms physical_advance
#print axioms advance_no_wrap
#print axioms timer_deadline

end NativeTagCheck.Hooks

-- Source proof structure: TimerQueries.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerQueries.el3QueryState"
  (← IO.getStderr).flush

def el3QueryState (s : NativeState) : NativeState :=
  afterOcc 488 (afterOcc 487 (afterOcc 490 s))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerQueries.secureEL2QueryState"
  (← IO.getStderr).flush

def secureEL2QueryState (s : NativeState) : NativeState :=
  if featureValue s .FEAT_SEL2 then el3QueryState s else s

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerQueries.secure_el2"
  (← IO.getStderr).flush

theorem secure_el2 (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    (IsSecureEL2Enabled () : SailM Bool) s =
      .ok (featureValue s .FEAT_SEL2 &&
        (_get_SCR_EL3_Type_EEL2 (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1))
        (secureEL2QueryState s) := by
  have he := el_using_nonzero 3#2 s ha (by decide)
  cases hs : featureValue s .FEAT_SEL2 <;>
    simp [IsSecureEL2Enabled, HaveEL, HaveSecureEL2Ext, feature_apply, bind_app,
      map_apply, pure_apply, read_apply, hs, he, EL3, secureEL2QueryState,
      el3QueryState, afterOcc]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerQueries.el2QueryState"
  (← IO.getStderr).flush

def el2QueryState (s : NativeState) : NativeState :=
  if _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1 then
    afterOcc 490 s else secureEL2QueryState (afterOcc 490 s)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerQueries.el2_enabled"
  (← IO.getStderr).flush

theorem el2_enabled (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    (EL2Enabled () : SailM Bool) s =
      .ok (ArmCert.HookQuiet.V0.el2Enabled s.regs) (el2QueryState s) := by
  have hns_alias (v : BitVec 64) : _get_SCRType_NS v = _get_SCR_EL3_Type_NS v := rfl
  have hval : ArmCert.HookQuiet.V0.el2Enabled s.regs =
      ((_get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1) ||
       (featureValue s .FEAT_SEL2 &&
        (_get_SCR_EL3_Type_EEL2 (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1))) := rfl
  rw [hval]
  rcases bit_cases (_get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3)) with hns | hns <;>
    simp [EL2Enabled, HaveEL, scr_gen s ha, secure_el2 (afterOcc 490 s) ha,
      bind_app, map_apply, pure_apply, el2QueryState, hns, hns_alias]

#print axioms secure_el2
#print axioms el2_enabled

end NativeTagCheck.Hooks

-- Source proof structure: CounterPrefix.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterPrefix.bind_if"
  (← IO.getStderr).flush

theorem bind_if {m : Type → Type} [Monad m] {α β : Type}
    (p : Prop) [Decidable p] (x y : m α) (f : α → m β) :
    ((if p then x else y) >>= f) = (if p then x >>= f else y >>= f) := by
  split <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterPrefix.advance_quiet"
  (← IO.getStderr).flush

theorem advance_quiet (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet (budget+1) s) :
    ArmCert.HookQuiet.V0.HookQuiet budget (advanceCount s) := by
  apply ArmCert.HookQuiet.V0.hookQuiet_after_E22_guarded_advance q
  · rfl
  · constructor <;> exact ⟨rfl, rfl⟩
  · exact advance_no_wrap budget s

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterPrefix.ordinaryIncrement"
  (← IO.getStderr).flush

def ordinaryIncrement : SailM Unit := do
  let enabled ← do
    if ← HaveCNTSCExt () then
      let ctl ← readReg CNTCR
      pure (_get_CNTCR_Type_SCEN ctl == 1#1)
    else pure false
  if enabled then
    let counterValue ← readReg PhysicalCount
    let scale ← readReg CNTSCR
    writeReg PhysicalCount (counterValue + Sail.BitVec.castWidth (m := 88) (Sail.BitVec.zeroExtend scale 88))
  else
    let counterValue ← readReg PhysicalCount
    let prior ← readReg PhysicalCount
    writeReg PhysicalCount (Sail.BitVec.updateSubrange counterValue 87 24
      (BitVec.addInt (Sail.BitVec.extractLsb prior 87 24) 1))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterPrefix.ordinary_increment"
  (← IO.getStderr).flush

theorem ordinary_increment (s : NativeState)
    (h : _get_CNTCR_Type_SCEN (s.regs.bank_BitVec_32 .CNTCR) = 0#1) :
    ordinaryIncrement s = .ok () (advanceCount s) := by
  cases hf : featureValue s .FEAT_CNTSC <;>
    simp [ordinaryIncrement, HaveCNTSCExt, feature_apply, bind_app, pure_apply,
      map_apply, read_apply, hf, h]
  all_goals rfl

#print axioms advance_quiet
#print axioms ordinary_increment

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterPrefix.afterIncrement"
  (← IO.getStderr).flush

def afterIncrement (prior : BitVec 64) : SailM Unit := do
  let a64 ← HaveAArch64 ()
  if !a64 then AArch32_CheckTimerConditions () else AArch64_CheckTimerConditions ()
  let current ← PhysicalCountInt ()
  TestEventCNTP prior current
  let current ← PhysicalCountInt ()
  TestEventCNTV prior current

/- Kernel equality exposes the real counter prefix, before any totality claim
about the remaining timer/event tail. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterPrefix.counter_factor"
  (← IO.getStderr).flush

theorem counter_factor (s : NativeState) :
    (GenericCounterTick () : SailM Unit) s =
      (do
        let ctl ← readReg CNTCR
        if _get_CNTCR_Type_EN ctl == 0#1 then
          let a64 ← HaveAArch64 ()
          if !a64 then AArch32_CheckTimerConditions () else AArch64_CheckTimerConditions ()
        else
          let prior ← PhysicalCountInt ()
          ordinaryIncrement
          afterIncrement prior : SailM Unit) s := by
  simp only [GenericCounterTick, ordinaryIncrement, afterIncrement, bind_assoc, bind_if, pure_bind]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterPrefix.counter_prefix_quiet"
  (← IO.getStderr).flush

theorem counter_prefix_quiet (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet (budget+1) s) :
    (GenericCounterTick () : SailM Unit) s =
      (if _get_CNTCR_Type_EN (s.regs.bank_BitVec_32 .CNTCR) == 0#1 then
        AArch64_CheckTimerConditions () s
      else afterIncrement (physicalValue s) (advanceCount s)) := by
  rw [counter_factor]
  rcases bit_cases (_get_CNTCR_Type_EN (s.regs.bank_BitVec_32 .CNTCR)) with hEN | hEN <;>
    simp [bind_app, read_apply, hEN, have_a64 s q.a64,
      physical_count_apply, ordinary_increment s q.ordinary]

#print axioms counter_factor
#print axioms counter_prefix_quiet

end NativeTagCheck.Hooks

-- Source proof structure: TimerParts.lean
-- GENERATED by gen/gen_timer_parts.py from the selected actual model source.
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
open ArmFull.SecurityState ArmFull.InterruptID
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks.TimerParts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerParts.checkP"
  (← IO.getStderr).flush

def checkP (ss : SecurityState) (offset : BitVec 64) (imask : BitVec 1) (status : Bool) : SailM ((BitVec 1) × Bool) := do
  let w__7 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
  let (imask, status) ← (( do
    if (((_get_CNTP_CTL_EL0_Type_ENABLE w__7) == 1#1) : Bool)
    then
      (do
        let w__8 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
        let imask := ((_get_CNTP_CTL_EL0_Type_IMASK w__8) : (BitVec 1))
        let w__12 ← (( do
          if ((← do
               (pure ((← do
                     (HaveRME ())) && (((BEq.beq ss SS_Root) || (BEq.beq ss SS_Realm)) : Bool)))) : Bool)
          then
            (do
              let w__11 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_CNTHCTL_EL2_Type_CNTPMASK w__11) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let imask : (BitVec 1) :=
          if (w__12 : Bool)
          then 1#1
          else imask
        let w__13 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
        let w__14 ← (( do (IsTimerConditionMet offset w__13 imask InterruptID_CNTP) ) : SailM Bool
          )
        let status := (w__14 : Bool)
        let w__15 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
        writeReg CNTP_CTL_EL0 (Sail.BitVec.updateSubrange w__15 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure ((imask, status))))
    else (pure ((imask, status))) ) : SailM ((BitVec 1) × Bool) )
  pure (imask, status)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerParts.checkHP"
  (← IO.getStderr).flush

def checkHP (status : Bool) : SailM (Bool) := do
  let w__20 ← (( do
    if ((← do
         if (((HaveEL EL3) : Bool) : Bool)
         then (pure true)
         else
           (do
             if (((HaveEL EL2) : Bool) : Bool)
             then
               (do
                 let w__16 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                 (pure (((! w__16) : Bool))))
             else (pure false))) : Bool)
    then
      (do
        let w__19 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHP_CTL_EL2_Type_ENABLE w__19) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let status ← (( do
    if (w__20 : Bool)
    then
      (do
        let w__21 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
        let w__22 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
        let w__23 ← (( do
          (IsTimerConditionMet (Zeros (n := 64)) w__21 (_get_CNTHP_CTL_EL2_Type_IMASK w__22)
            InterruptID_CNTHP) ) : SailM Bool )
        let status := (w__23 : Bool)
        let w__24 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
        writeReg CNTHP_CTL_EL2 (Sail.BitVec.updateSubrange w__24 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  pure status

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerParts.checkHPS"
  (← IO.getStderr).flush

def checkHPS (status : Bool) : SailM (Bool) := do
  let w__28 ← (( do
    if ((← do
         if (((HaveEL EL2) : Bool) : Bool)
         then
           (do
             (HaveSecureEL2Ext ()))
         else (pure false)) : Bool)
    then
      (do
        let w__27 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHPS_CTL_EL2_Type_ENABLE w__27) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let status ← (( do
    if (w__28 : Bool)
    then
      (do
        let w__29 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64) )
        let w__30 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
        let w__31 ← (( do
          (IsTimerConditionMet (Zeros (n := 64)) w__29 (_get_CNTHPS_CTL_EL2_Type_IMASK w__30)
            InterruptID_CNTHPS) ) : SailM Bool )
        let status := (w__31 : Bool)
        let w__32 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
        writeReg CNTHPS_CTL_EL2 (Sail.BitVec.updateSubrange w__32 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  pure status

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerParts.checkPS"
  (← IO.getStderr).flush

def checkPS (offset : BitVec 64) (status : Bool) : SailM (Bool) := do
  let w__33 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
  let status ← (( do
    if (((_get_CNTPS_CTL_EL1_Type_ENABLE w__33) == 1#1) : Bool)
    then
      (do
        let w__34 ← (( do readReg CNTPS_CVAL_EL1 ) : SailM (BitVec 64) )
        let w__35 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
        let w__36 ← (( do
          (IsTimerConditionMet offset w__34 (_get_CNTPS_CTL_EL1_Type_IMASK w__35) InterruptID_CNTPS)
          ) : SailM Bool )
        let status := (w__36 : Bool)
        let w__37 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
        writeReg CNTPS_CTL_EL1 (Sail.BitVec.updateSubrange w__37 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  pure status

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerParts.checkV"
  (← IO.getStderr).flush

def checkV (ss : SecurityState) (status : Bool) : SailM (Bool) := do
  let w__38 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  let status ← (( do
    if (((_get_CNTV_CTL_EL0_Type_ENABLE w__38) == 1#1) : Bool)
    then
      (do
        let w__39 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
        let imask : (BitVec 1) := ((_get_CNTV_CTL_EL0_Type_IMASK w__39) : (BitVec 1))
        let w__43 ← (( do
          if ((← do
               (pure ((← do
                     (HaveRME ())) && (((BEq.beq ss SS_Root) || (BEq.beq ss SS_Realm)) : Bool)))) : Bool)
          then
            (do
              let w__42 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_CNTHCTL_EL2_Type_CNTVMASK w__42) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let imask : (BitVec 1) :=
          if (w__43 : Bool)
          then 1#1
          else imask
        let w__44 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
        let w__45 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
        let w__46 ← (( do (IsTimerConditionMet w__44 w__45 imask InterruptID_CNTV) ) : SailM Bool
          )
        let status := (w__46 : Bool)
        let w__47 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
        writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange w__47 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  pure status

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerParts.checkHV"
  (← IO.getStderr).flush

def checkHV (status : Bool) : SailM (Bool) := do
  let w__53 ← (( do
    if ((← do
         if ((← do
              (HaveVirtHostExt ())) : Bool)
         then
           (do
             if (((HaveEL EL3) : Bool) : Bool)
             then (pure true)
             else
               (do
                 let w__49 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                 (pure (((! w__49) : Bool)))))
         else (pure false)) : Bool)
    then
      (do
        let w__52 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHV_CTL_EL2_Type_ENABLE w__52) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let status ← (( do
    if (w__53 : Bool)
    then
      (do
        let w__54 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
        let w__55 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
        let w__56 ← (( do
          (IsTimerConditionMet (Zeros (n := 64)) w__54 (_get_CNTHV_CTL_EL2_Type_IMASK w__55)
            InterruptID_CNTHV) ) : SailM Bool )
        let status := (w__56 : Bool)
        let w__57 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
        writeReg CNTHV_CTL_EL2 (Sail.BitVec.updateSubrange w__57 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  pure status

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerParts.checkHVS"
  (← IO.getStderr).flush

def checkHVS  : SailM (Unit) := do
  let w__62 ← (( do
    if ((← do
         if ((← do
              (HaveSecureEL2Ext ())) : Bool)
         then
           (do
             (HaveVirtHostExt ()))
         else (pure false)) : Bool)
    then
      (do
        let w__61 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHVS_CTL_EL2_Type_ENABLE w__61) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__62 : Bool)
  then
    (do
      let w__63 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
      let w__64 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
      let status ← (( do
        (IsTimerConditionMet (Zeros (n := 64)) w__63 (_get_CNTHVS_CTL_EL2_Type_IMASK w__64)
          InterruptID_CNTHVS) ) : SailM Bool )
      let w__65 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
      writeReg CNTHVS_CTL_EL2 (Sail.BitVec.updateSubrange w__65 2 2
        (if (status : Bool)
        then 1#1
        else 0#1)))
  else (pure (()))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerParts.combined"
  (← IO.getStderr).flush

def combined : SailM Unit := do
  let status ← (( do (undefined_bool_at (.site 1174) ()) ) : SailM Bool )
  let offset ← (( do (undefined_bitvector_at (.site 1175) 64) ) : SailM (BitVec 64) )
  let imask ← (( do (undefined_bitvector_at (.site 1176) 1) ) : SailM (BitVec 1) )
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let ecv : Bool := false
  let w__0 ← (( do (HaveECVExt ()) ) : SailM Bool )
  let ecv ← (( do
    if (w__0 : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__1 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_CNTHCTL_EL2_Type_ECV w__1) == 1#1) : Bool)))) : Bool)
             then
               (do
                 let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                 (pure ((((_get_SCR_EL3_Type_ECVEn w__2) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false))
    else (pure (ecv)) ) : SailM Bool )
  let offset ← (( do
    if (ecv : Bool)
    then
      (do
        readReg CNTPOFF_EL2)
    else
      (let offset : (BitVec 64) := (Zeros (n := 64))
      (pure (offset))) ) : SailM (BitVec 64) )
  let (imask, status) ← checkP ss offset imask status
  let status ← checkHP status
  let status ← checkHPS status
  let status ← checkPS offset status
  let status ← checkV ss status
  let _status ← checkHV status
  checkHVS

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerParts.actual_equation"
  (← IO.getStderr).flush

theorem actual_equation (s : NativeState) :
    (AArch64_CheckTimerConditions () : SailM Unit) s = combined s := by
  simp only [AArch64_CheckTimerConditions, combined, checkP, checkHP, checkHPS,
    checkPS, checkV, checkHV, checkHVS, bind_assoc, bind_pure, pure_bind]

#print axioms actual_equation
end NativeTagCheck.Hooks.TimerParts

-- Source proof structure: TimerCore.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCore.bit_is_one"
  (← IO.getStderr).flush

theorem bit_is_one {w : Nat} (x : BitVec w) (i : Nat) :
    x.extractLsb' i 1 = 1#1 ↔ x.getLsbD i = true := by
  rw [BitVec.getLsbD_eq_extractLsb']
  simp

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCore.timer_quiet_success"
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
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCore.TimerKey"
  (← IO.getStderr).flush

def TimerKey (k : Bank_BitVec_64) : Prop :=
  k = .CNTP_CTL_EL0 ∨ k = .CNTHP_CTL_EL2 ∨ k = .CNTHPS_CTL_EL2 ∨
  k = .CNTPS_CTL_EL1 ∨ k = .CNTV_CTL_EL0 ∨ k = .CNTHV_CTL_EL2 ∨ k = .CNTHVS_CTL_EL2

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCore.TimerFrame"
  (← IO.getStderr).flush

structure TimerFrame (s t : NativeState) : Prop where
  frame : E22Frame s.regs t.regs
  bits : ArmCert.HookQuiet.V0.TimerLowBitsEq s.regs t.regs
  counterValue : t.regs.PhysicalCount = s.regs.PhysicalCount
  gic : t.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending
  mem : t.mem = s.mem
  events : t.events = s.events
  choiceState : choiceView t = choiceView s
  tags : t.tags = s.tags
  cycleCount : t.cycleCount = s.cycleCount
  sailOutput : t.sailOutput = s.sailOutput

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCore.TimerFrame.refl"
  (← IO.getStderr).flush

theorem TimerFrame.refl (s : NativeState) : TimerFrame s s := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  constructor <;> exact ⟨rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCore.updateTimer"
  (← IO.getStderr).flush

def updateTimer (s : NativeState) (k : Bank_BitVec_64) (status : Bool) : NativeState :=
  let value := Sail.BitVec.updateSubrange (s.regs.bank_BitVec_64 k) 2 2
    (if status then 1#1 else 0#1)
  let r : Regs := {s.regs with bank_BitVec_64 := RegMap.set s.regs.bank_BitVec_64 k value}
  {s with regs := r}

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCore.update_timer_frame"
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
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCore.write_apply"
  (← IO.getStderr).flush

theorem write_apply {α : Type} (r : ArmFull.RegisterRef α) (v : α) (s : NativeState) :
    (ArmFull.writeReg r v : SailM Unit) s = .ok () {s with regs := r.set v s.regs} := rfl

/- The real timer call remains in this normal form. `done` formats a pure
return value; it does not supply execution, frame, or guard answers. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCore.bankCheck"
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
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCore.bank_check_total"
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

end NativeTagCheck.Hooks

-- Source proof structure: TimerBankEq.lean
-- GENERATED by gen/gen_timer_bank_eq.py; kernel equalities bind actual effects.
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmFull.SecurityState ArmFull.InterruptID
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks.TimerBankEq

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankEq.eqP"
  (← IO.getStderr).flush

theorem eqP (ss : SecurityState) (offset : BitVec 64) (imask : BitVec 1) (status : Bool) (s : NativeState) :
    TimerParts.checkP ss offset imask status s =
      bankCheck .CNTP_CTL_EL0 .CNTP_CVAL_EL0 .InterruptID_CNTP
        (true) (featureValue s .FEAT_RME && ((ss == SS_Root) || (ss == SS_Realm)) && (_get_CNTHCTL_EL2_Type_CNTPMASK (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1)) (offset) (imask, status) (fun m b => (m, b)) s := by
  by_cases hE : (s.regs.bank_BitVec_64 .CNTP_CTL_EL0)[0] = true <;>
    cases hRME : featureValue s .FEAT_RME <;>
    cases ss <;>
    rcases bit_cases (_get_CNTHCTL_EL2_Type_CNTPMASK (s.regs.bank_BitVec_64 .CNTHCTL_EL2)) with hMask | hMask <;>
    simp [TimerParts.checkP, bankCheck, HaveEL, HaveSecureEL2Ext, HaveVirtHostExt,
    HaveRME, feature_apply, bind_app, pure_apply, map_apply, read_apply, write_apply,
    _get_CNTP_CTL_EL0_Type_ENABLE, _get_CNTP_CTL_EL0_Type_IMASK,
    Sail.BitVec.extractLsb, BitVec.extractLsb, bit_is_one, BEq.beq,
    ArmFull.instBEqSecurityState.beq, SecurityState.ctorIdx, Zeros, hE, hRME, hMask]

#print axioms eqP

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankEq.eqHP"
  (← IO.getStderr).flush

theorem eqHP (status : Bool) (s : NativeState) :
    TimerParts.checkHP status s =
      bankCheck .CNTHP_CTL_EL2 .CNTHP_CVAL_EL2 .InterruptID_CNTHP
        (true) (false) (0#64) status (fun _ b => b) s := by
  by_cases hE : (s.regs.bank_BitVec_64 .CNTHP_CTL_EL2)[0] = true <;>
    simp [TimerParts.checkHP, bankCheck, HaveEL, HaveSecureEL2Ext, HaveVirtHostExt,
    HaveRME, feature_apply, bind_app, pure_apply, map_apply, read_apply, write_apply,
    _get_CNTHP_CTL_EL2_Type_ENABLE, _get_CNTHP_CTL_EL2_Type_IMASK,
    Sail.BitVec.extractLsb, BitVec.extractLsb, bit_is_one, BEq.beq,
    ArmFull.instBEqSecurityState.beq, SecurityState.ctorIdx, Zeros, hE]

#print axioms eqHP

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankEq.eqHPS"
  (← IO.getStderr).flush

theorem eqHPS (status : Bool) (s : NativeState) :
    TimerParts.checkHPS status s =
      bankCheck .CNTHPS_CTL_EL2 .CNTHPS_CVAL_EL2 .InterruptID_CNTHPS
        (featureValue s .FEAT_SEL2) (false) (0#64) status (fun _ b => b) s := by
  by_cases hE : (s.regs.bank_BitVec_64 .CNTHPS_CTL_EL2)[0] = true <;>
    cases hSEL2 : featureValue s .FEAT_SEL2 <;>
    simp [TimerParts.checkHPS, bankCheck, HaveEL, HaveSecureEL2Ext, HaveVirtHostExt,
    HaveRME, feature_apply, bind_app, pure_apply, map_apply, read_apply, write_apply,
    _get_CNTHPS_CTL_EL2_Type_ENABLE, _get_CNTHPS_CTL_EL2_Type_IMASK,
    Sail.BitVec.extractLsb, BitVec.extractLsb, bit_is_one, BEq.beq,
    ArmFull.instBEqSecurityState.beq, SecurityState.ctorIdx, Zeros, hE, hSEL2]

#print axioms eqHPS

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankEq.eqPS"
  (← IO.getStderr).flush

theorem eqPS (offset : BitVec 64) (status : Bool) (s : NativeState) :
    TimerParts.checkPS offset status s =
      bankCheck .CNTPS_CTL_EL1 .CNTPS_CVAL_EL1 .InterruptID_CNTPS
        (true) (false) (offset) status (fun _ b => b) s := by
  by_cases hE : (s.regs.bank_BitVec_64 .CNTPS_CTL_EL1)[0] = true <;>
    simp [TimerParts.checkPS, bankCheck, HaveEL, HaveSecureEL2Ext, HaveVirtHostExt,
    HaveRME, feature_apply, bind_app, pure_apply, map_apply, read_apply, write_apply,
    _get_CNTPS_CTL_EL1_Type_ENABLE, _get_CNTPS_CTL_EL1_Type_IMASK,
    Sail.BitVec.extractLsb, BitVec.extractLsb, bit_is_one, BEq.beq,
    ArmFull.instBEqSecurityState.beq, SecurityState.ctorIdx, Zeros, hE]

#print axioms eqPS

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankEq.eqV"
  (← IO.getStderr).flush

theorem eqV (ss : SecurityState) (status : Bool) (s : NativeState) :
    TimerParts.checkV ss status s =
      bankCheck .CNTV_CTL_EL0 .CNTV_CVAL_EL0 .InterruptID_CNTV
        (true) (featureValue s .FEAT_RME && ((ss == SS_Root) || (ss == SS_Realm)) && (_get_CNTHCTL_EL2_Type_CNTVMASK (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1)) (s.regs.bank_BitVec_64 .CNTVOFF_EL2) status (fun _ b => b) s := by
  by_cases hE : (s.regs.bank_BitVec_64 .CNTV_CTL_EL0)[0] = true <;>
    cases hRME : featureValue s .FEAT_RME <;>
    cases ss <;>
    rcases bit_cases (_get_CNTHCTL_EL2_Type_CNTVMASK (s.regs.bank_BitVec_64 .CNTHCTL_EL2)) with hMask | hMask <;>
    simp [TimerParts.checkV, bankCheck, HaveEL, HaveSecureEL2Ext, HaveVirtHostExt,
    HaveRME, feature_apply, bind_app, pure_apply, map_apply, read_apply, write_apply,
    _get_CNTV_CTL_EL0_Type_ENABLE, _get_CNTV_CTL_EL0_Type_IMASK,
    Sail.BitVec.extractLsb, BitVec.extractLsb, bit_is_one, BEq.beq,
    ArmFull.instBEqSecurityState.beq, SecurityState.ctorIdx, Zeros, hE, hRME, hMask]

#print axioms eqV

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankEq.eqHV"
  (← IO.getStderr).flush

theorem eqHV (status : Bool) (s : NativeState) :
    TimerParts.checkHV status s =
      bankCheck .CNTHV_CTL_EL2 .CNTHV_CVAL_EL2 .InterruptID_CNTHV
        (featureValue s .FEAT_VHE) (false) (0#64) status (fun _ b => b) s := by
  by_cases hE : (s.regs.bank_BitVec_64 .CNTHV_CTL_EL2)[0] = true <;>
    cases hVHE : featureValue s .FEAT_VHE <;>
    simp [TimerParts.checkHV, bankCheck, HaveEL, HaveSecureEL2Ext, HaveVirtHostExt,
    HaveRME, feature_apply, bind_app, pure_apply, map_apply, read_apply, write_apply,
    _get_CNTHV_CTL_EL2_Type_ENABLE, _get_CNTHV_CTL_EL2_Type_IMASK,
    Sail.BitVec.extractLsb, BitVec.extractLsb, bit_is_one, BEq.beq,
    ArmFull.instBEqSecurityState.beq, SecurityState.ctorIdx, Zeros, hE, hVHE]

#print axioms eqHV

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankEq.eqHVS"
  (← IO.getStderr).flush

theorem eqHVS  (s : NativeState) :
    TimerParts.checkHVS  s =
      bankCheck .CNTHVS_CTL_EL2 .CNTHVS_CVAL_EL2 .InterruptID_CNTHVS
        (featureValue s .FEAT_SEL2 && featureValue s .FEAT_VHE) (false) (0#64) () (fun _ _ => ()) s := by
  by_cases hE : (s.regs.bank_BitVec_64 .CNTHVS_CTL_EL2)[0] = true <;>
    cases hSEL2 : featureValue s .FEAT_SEL2 <;>
    cases hVHE : featureValue s .FEAT_VHE <;>
    simp [TimerParts.checkHVS, bankCheck, HaveEL, HaveSecureEL2Ext, HaveVirtHostExt,
    HaveRME, feature_apply, bind_app, pure_apply, map_apply, read_apply, write_apply,
    _get_CNTHVS_CTL_EL2_Type_ENABLE, _get_CNTHVS_CTL_EL2_Type_IMASK,
    Sail.BitVec.extractLsb, BitVec.extractLsb, bit_is_one, BEq.beq,
    ArmFull.instBEqSecurityState.beq, SecurityState.ctorIdx, Zeros, hE, hSEL2, hVHE]

#print axioms eqHVS

end NativeTagCheck.Hooks.TimerBankEq

-- Source proof structure: TimerGuard.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmFull.SecurityState

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerGuard.security_class_quiet"
  (← IO.getStderr).flush

theorem security_class_quiet (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    (featureValue s .FEAT_RME &&
      ((securityValue s == SS_Root) || (securityValue s == SS_Realm))) =
      ArmCert.HookQuiet.V0.realm s.regs := by
  have hv : featureValue s .FEAT_RME = false ∨
      _get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1 ∨
      effectiveNSValue s = 1#1 := q.validSecurity
  have hfR : ArmCert.HookQuiet.V0.feature s.regs .FEAT_RME = featureValue s .FEAT_RME := rfl
  have hfS : ArmCert.HookQuiet.V0.feature s.regs .FEAT_SEL2 = featureValue s .FEAT_SEL2 := rfl
  have heff : ArmCert.HookQuiet.V0.effectiveNS s.regs = effectiveNSValue s := rfl
  cases hr : featureValue s .FEAT_RME <;>
    cases hs : featureValue s .FEAT_SEL2 <;>
    rcases bit_cases (_get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3)) with hnse | hnse <;>
    rcases bit_cases (_get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3)) with hns | hns <;>
    simp_all [securityValue, securityRMEValue, effectiveNSValue, ArmCert.HookQuiet.V0.realm,
      ArmCert.HookQuiet.V0.reg64, BEq.beq, ArmFull.instBEqSecurityState.beq, SecurityState.ctorIdx]

#print axioms security_class_quiet

end NativeTagCheck.Hooks

-- Source proof structure: TimerBankFacts.lean
-- GENERATED by gen/gen_timer_bank_facts.py; all callbacks are instantiated.
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
namespace NativeTagCheck.Hooks.TimerBankFacts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankFacts.totalP"
  (← IO.getStderr).flush

theorem totalP (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (imask : BitVec 1) (status : Bool) :
    ∃ v t, TimerParts.checkP (securityValue s) (ArmCert.HookQuiet.V0.physicalOffset s.regs) imask status s = .ok v t ∧ TimerFrame s t := by
  rw [TimerBankEq.eqP, security_class_quiet budget s q]
  exact bank_check_total budget s .CNTP_CTL_EL0 .CNTP_CVAL_EL0 .InterruptID_CNTP
    (true) (ArmCert.HookQuiet.V0.realm s.regs && (_get_CNTHCTL_EL2_Type_CNTPMASK (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1)) (ArmCert.HookQuiet.V0.physicalOffset s.regs) (imask, status) (fun m b => (m, b)) (by simp [TimerKey]) q.timers.1

#print axioms totalP

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankFacts.totalHP"
  (← IO.getStderr).flush

theorem totalHP (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (status : Bool) :
    ∃ v t, TimerParts.checkHP status s = .ok v t ∧ TimerFrame s t := by
  rw [TimerBankEq.eqHP]
  exact bank_check_total budget s .CNTHP_CTL_EL2 .CNTHP_CVAL_EL2 .InterruptID_CNTHP
    (true) (false) (0#64) status (fun _ b => b) (by simp [TimerKey]) q.timers.2.1

#print axioms totalHP

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankFacts.totalHPS"
  (← IO.getStderr).flush

theorem totalHPS (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (status : Bool) :
    ∃ v t, TimerParts.checkHPS status s = .ok v t ∧ TimerFrame s t := by
  rw [TimerBankEq.eqHPS]
  exact bank_check_total budget s .CNTHPS_CTL_EL2 .CNTHPS_CVAL_EL2 .InterruptID_CNTHPS
    (featureValue s .FEAT_SEL2) (false) (0#64) status (fun _ b => b) (by simp [TimerKey]) q.timers.2.2.1

#print axioms totalHPS

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankFacts.totalPS"
  (← IO.getStderr).flush

theorem totalPS (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (status : Bool) :
    ∃ v t, TimerParts.checkPS (ArmCert.HookQuiet.V0.physicalOffset s.regs) status s = .ok v t ∧ TimerFrame s t := by
  rw [TimerBankEq.eqPS]
  exact bank_check_total budget s .CNTPS_CTL_EL1 .CNTPS_CVAL_EL1 .InterruptID_CNTPS
    (true) (false) (ArmCert.HookQuiet.V0.physicalOffset s.regs) status (fun _ b => b) (by simp [TimerKey]) q.timers.2.2.2.1

#print axioms totalPS

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankFacts.totalV"
  (← IO.getStderr).flush

theorem totalV (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (status : Bool) :
    ∃ v t, TimerParts.checkV (securityValue s) status s = .ok v t ∧ TimerFrame s t := by
  rw [TimerBankEq.eqV, security_class_quiet budget s q]
  exact bank_check_total budget s .CNTV_CTL_EL0 .CNTV_CVAL_EL0 .InterruptID_CNTV
    (true) (ArmCert.HookQuiet.V0.realm s.regs && (_get_CNTHCTL_EL2_Type_CNTVMASK (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1)) (s.regs.bank_BitVec_64 .CNTVOFF_EL2) status (fun _ b => b) (by simp [TimerKey]) q.timers.2.2.2.2.1

#print axioms totalV

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankFacts.totalHV"
  (← IO.getStderr).flush

theorem totalHV (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (status : Bool) :
    ∃ v t, TimerParts.checkHV status s = .ok v t ∧ TimerFrame s t := by
  rw [TimerBankEq.eqHV]
  exact bank_check_total budget s .CNTHV_CTL_EL2 .CNTHV_CVAL_EL2 .InterruptID_CNTHV
    (featureValue s .FEAT_VHE) (false) (0#64) status (fun _ b => b) (by simp [TimerKey]) q.timers.2.2.2.2.2.1

#print axioms totalHV

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerBankFacts.totalHVS"
  (← IO.getStderr).flush

theorem totalHVS (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s)  :
    ∃ v t, TimerParts.checkHVS  s = .ok v t ∧ TimerFrame s t := by
  rw [TimerBankEq.eqHVS]
  exact bank_check_total budget s .CNTHVS_CTL_EL2 .CNTHVS_CVAL_EL2 .InterruptID_CNTHVS
    (featureValue s .FEAT_SEL2 && featureValue s .FEAT_VHE) (false) (0#64) () (fun _ _ => ()) (by simp [TimerKey]) q.timers.2.2.2.2.2.2

#print axioms totalHVS

end NativeTagCheck.Hooks.TimerBankFacts

-- Source proof structure: TimerFlow.lean
-- GENERATED by gen/gen_timer_flow.py from the selected actual preamble.
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmFull.SecurityState ArmFull.InterruptID
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks.TimerFlow
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerFlow.preamble"
  (← IO.getStderr).flush

def preamble : SailM (SecurityState × (BitVec 64) × (BitVec 1) × Bool) := do
  let status ← (( do (undefined_bool_at (.site 1174) ()) ) : SailM Bool )
  let offset ← (( do (undefined_bitvector_at (.site 1175) 64) ) : SailM (BitVec 64) )
  let imask ← (( do (undefined_bitvector_at (.site 1176) 1) ) : SailM (BitVec 1) )
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let ecv : Bool := false
  let w__0 ← (( do (HaveECVExt ()) ) : SailM Bool )
  let ecv ← (( do
    if (w__0 : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__1 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_CNTHCTL_EL2_Type_ECV w__1) == 1#1) : Bool)))) : Bool)
             then
               (do
                 let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                 (pure ((((_get_SCR_EL3_Type_ECVEn w__2) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false))
    else (pure (ecv)) ) : SailM Bool )
  let offset ← (( do
    if (ecv : Bool)
    then
      (do
        readReg CNTPOFF_EL2)
    else
      (let offset : (BitVec 64) := (Zeros (n := 64))
      (pure (offset))) ) : SailM (BitVec 64) )
  pure (ss, offset, imask, status)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerFlow.banks"
  (← IO.getStderr).flush

def banks (ss : SecurityState) (offset : BitVec 64) (imask : BitVec 1) (status : Bool) : SailM Unit := do
  let (_imask, status) ← TimerParts.checkP ss offset imask status
  let status ← TimerParts.checkHP status
  let status ← TimerParts.checkHPS status
  let status ← TimerParts.checkPS offset status
  let status ← TimerParts.checkV ss status
  let _status ← TimerParts.checkHV status
  TimerParts.checkHVS

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerFlow.preamble_equation"
  (← IO.getStderr).flush

theorem preamble_equation (s : NativeState) :
    (AArch64_CheckTimerConditions () : SailM Unit) s =
      (do let (ss, offset, imask, status) ← preamble
          banks ss offset imask status : SailM Unit) s := by
  rw [TimerParts.actual_equation]
  simp only [TimerParts.combined, preamble, banks, bind_assoc, pure_bind]

#print axioms preamble_equation
end NativeTagCheck.Hooks.TimerFlow

-- Source proof structure: TimerPrepare.lean
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

namespace NativeTagCheck.Hooks

@[simp] theorem security_query_regs (s : NativeState) :
    (securityQueryState s).regs = s.regs := by unfold securityQueryState; split <;> rfl
@[simp] theorem security_query_mem (s : NativeState) :
    (securityQueryState s).mem = s.mem := by unfold securityQueryState; split <;> rfl
@[simp] theorem security_query_events (s : NativeState) :
    (securityQueryState s).events = s.events := by unfold securityQueryState; split <;> rfl

@[simp] theorem el2_query_regs (s : NativeState) :
    (el2QueryState s).regs = s.regs := by
  unfold el2QueryState secureEL2QueryState
  split <;> first | rfl | (split <;> rfl)
@[simp] theorem el2_query_mem (s : NativeState) :
    (el2QueryState s).mem = s.mem := by
  unfold el2QueryState secureEL2QueryState
  split <;> first | rfl | (split <;> rfl)
@[simp] theorem el2_query_events (s : NativeState) :
    (el2QueryState s).events = s.events := by
  unfold el2QueryState secureEL2QueryState
  split <;> first | rfl | (split <;> rfl)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerPrepare.ecvGate"
  (← IO.getStderr).flush

def ecvGate (s : NativeState) : Bool :=
  featureValue s .FEAT_ECV &&
    (_get_CNTHCTL_EL2_Type_ECV (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1) &&
    (_get_SCR_EL3_Type_ECVEn (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerPrepare.timerPrepareState"
  (← IO.getStderr).flush

def timerPrepareState (s : NativeState) : NativeState :=
  if ecvGate s then el2QueryState (securityQueryState s) else securityQueryState s

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerPrepare.timer_prepare_regs"
  (← IO.getStderr).flush

theorem timer_prepare_regs (s : NativeState) : (timerPrepareState s).regs = s.regs := by
  unfold timerPrepareState
  split <;> simp only [security_query_regs, el2_query_regs]
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerPrepare.timer_prepare_mem"
  (← IO.getStderr).flush

theorem timer_prepare_mem (s : NativeState) : (timerPrepareState s).mem = s.mem := by
  unfold timerPrepareState
  split <;> simp only [security_query_mem, el2_query_mem]
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerPrepare.timer_prepare_events"
  (← IO.getStderr).flush

theorem timer_prepare_events (s : NativeState) : (timerPrepareState s).events = s.events := by
  unfold timerPrepareState
  split <;> simp only [security_query_events, el2_query_events]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerPrepare.timer_preamble"
  (← IO.getStderr).flush

theorem timer_preamble (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ (mask : BitVec 1) (status : Bool), TimerFlow.preamble s =
      .ok (securityValue s, ArmCert.HookQuiet.V0.physicalOffset s.regs, mask, status)
        (timerPrepareState s) := by
  let status := oracleChoiceSource.chooseAt .bool (.site 1174) s.choiceState
  let mask := oracleChoiceSource.chooseAt (.bitvector 1) (.site 1176) s.choiceState
  refine ⟨mask, status, ?_⟩
  have ha : featureValue (securityQueryState s) .FEAT_AA64EL0 = true := by
    unfold featureValue
    rw [security_query_regs]
    exact q.a64
  have hel := el2_enabled (securityQueryState s) ha
  rw [security_query_regs] at hel
  have hf (f : Feature) : featureValue (securityQueryState s) f = featureValue s f := by
    unfold featureValue
    rw [security_query_regs]
  have hQf : ArmCert.HookQuiet.V0.feature s.regs .FEAT_ECV = featureValue s .FEAT_ECV := rfl
  cases hF : featureValue s .FEAT_ECV <;>
    rcases bit_cases (_get_CNTHCTL_EL2_Type_ECV (s.regs.bank_BitVec_64 .CNTHCTL_EL2)) with hC | hC <;>
    rcases bit_cases (_get_SCR_EL3_Type_ECVEn (s.regs.bank_BitVec_64 .SCR_EL3)) with hS | hS <;>
    cases hEL : ArmCert.HookQuiet.V0.el2Enabled s.regs <;>
    simp [TimerFlow.preamble, bind_app, pure_apply, map_apply, ubool, ubv,
      current_security_quiet budget s q, HaveECVExt, feature_apply, read_apply,
      hel, hf, hQf, hF, hC, hS, hEL, timerPrepareState, ecvGate,
      ArmCert.HookQuiet.V0.physicalOffset, ArmCert.HookQuiet.V0.reg64,
      status, mask, Zeros]

#print axioms timer_prepare_regs
#print axioms timer_prepare_mem
#print axioms timer_prepare_events
#print axioms timer_preamble

end NativeTagCheck.Hooks

-- Source proof structure: TimerCompose.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCompose.lowbits_trans"
  (← IO.getStderr).flush

theorem lowbits_trans {a b c : Regs}
    (hab : ArmCert.HookQuiet.V0.TimerLowBitsEq a b)
    (hbc : ArmCert.HookQuiet.V0.TimerLowBitsEq b c) :
    ArmCert.HookQuiet.V0.TimerLowBitsEq a c := by
  exact ⟨⟨hbc.p.1.trans hab.p.1, hbc.p.2.trans hab.p.2⟩,
    ⟨hbc.hp.1.trans hab.hp.1, hbc.hp.2.trans hab.hp.2⟩,
    ⟨hbc.hps.1.trans hab.hps.1, hbc.hps.2.trans hab.hps.2⟩,
    ⟨hbc.ps.1.trans hab.ps.1, hbc.ps.2.trans hab.ps.2⟩,
    ⟨hbc.v.1.trans hab.v.1, hbc.v.2.trans hab.v.2⟩,
    ⟨hbc.hv.1.trans hab.hv.1, hbc.hv.2.trans hab.hv.2⟩,
    ⟨hbc.hvs.1.trans hab.hvs.1, hbc.hvs.2.trans hab.hvs.2⟩⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCompose.TimerFrame.trans"
  (← IO.getStderr).flush

theorem TimerFrame.trans {s t u : NativeState} (a : TimerFrame s t) (b : TimerFrame t u) :
    TimerFrame s u :=
  ⟨b.frame.trans a.frame, lowbits_trans a.bits b.bits, b.counterValue.trans a.counterValue,
    b.gic.trans a.gic, b.mem.trans a.mem, b.events.trans a.events,
    b.choiceState.trans a.choiceState, b.tags.trans a.tags,
    b.cycleCount.trans a.cycleCount, b.sailOutput.trans a.sailOutput⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCompose.TimerFrame.quiet"
  (← IO.getStderr).flush

theorem TimerFrame.quiet {budget : Nat} {s t : NativeState}
    (f : TimerFrame s t) (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ArmCert.HookQuiet.V0.HookQuiet budget t :=
  ArmCert.HookQuiet.V0.hookQuiet_same_budget_E22_of_physicalCount_eq q f.frame f.bits f.counterValue

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCompose.TimerFrame.security_eq"
  (← IO.getStderr).flush

theorem TimerFrame.security_eq {s t : NativeState} (f : TimerFrame s t) :
    securityValue t = securityValue s := by
  exact frame_pres_E22 (fun r => securityValue {s with regs := r}) (fun _ => rfl) f.frame

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCompose.TimerFrame.offset_eq"
  (← IO.getStderr).flush

theorem TimerFrame.offset_eq {s t : NativeState} (f : TimerFrame s t) :
    ArmCert.HookQuiet.V0.physicalOffset t.regs = ArmCert.HookQuiet.V0.physicalOffset s.regs :=
  frame_pres_E22 ArmCert.HookQuiet.V0.physicalOffset (fun _ => rfl) f.frame

/- Only occurrence bookkeeping is erased for this equality. The actual
successor is still passed to every subsequent model call. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCompose.eraseOcc"
  (← IO.getStderr).flush

def eraseOcc (s : NativeState) : NativeState :=
  {s with choiceOcc := ({} : Std.ExtHashMap Nat Nat).insert 1354 (s.choiceOcc.getD 1354 0)}

@[simp] theorem erase_afterOcc (site : Nat) (s : NativeState) (different : site ≠ 1354) :
    eraseOcc (afterOcc site s) = eraseOcc s := by
  simp [eraseOcc, afterOcc, Std.ExtHashMap.getD_insert, different, Ne.symm different]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCompose.erase_security_query"
  (← IO.getStderr).flush

theorem erase_security_query (s : NativeState) :
    eraseOcc (securityQueryState s) = eraseOcc s := by
  unfold securityQueryState
  split <;> simp [eraseOcc, securityNoRMEState, afterOcc, Std.ExtHashMap.getD_insert]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCompose.erase_el2_query"
  (← IO.getStderr).flush

theorem erase_el2_query (s : NativeState) :
    eraseOcc (el2QueryState s) = eraseOcc s := by
  unfold el2QueryState secureEL2QueryState
  split <;> first
    | (simp [eraseOcc, el3QueryState, afterOcc, Std.ExtHashMap.getD_insert]; done)
    | (split <;> simp [eraseOcc, el3QueryState, afterOcc, Std.ExtHashMap.getD_insert])

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCompose.erase_timer_prepare"
  (← IO.getStderr).flush

theorem erase_timer_prepare (s : NativeState) :
    eraseOcc (timerPrepareState s) = eraseOcc s := by
  unfold timerPrepareState
  split
  · exact (erase_el2_query _).trans (erase_security_query s)
  · exact erase_security_query s

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCompose.TimerFrame.of_eraseOcc_eq"
  (← IO.getStderr).flush

theorem TimerFrame.of_eraseOcc_eq {s t : NativeState}
    (h : eraseOcc t = eraseOcc s) : TimerFrame s t := by
  have hr : t.regs = s.regs := by
    simpa only [eraseOcc] using congrArg (fun x : NativeState => x.regs) h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show E22Frame s.regs t.regs = (eraseE22 t.regs = eraseE22 s.regs) from rfl, hr]
  · rw [hr]; constructor <;> exact ⟨rfl, rfl⟩
  · exact congrArg Regs.PhysicalCount hr
  · exact congrArg (fun r : Regs => r.bank_Option_InterruptID .__GIC_Pending) hr
  · simpa only [eraseOcc] using congrArg (fun x : NativeState => x.mem) h
  · simpa only [eraseOcc] using congrArg (fun x : NativeState => x.events) h
  · simpa [eraseOcc, choiceView, Std.ExtHashMap.getD_insert] using congrArg (fun x : NativeState => choiceView x) h
  · simpa only [eraseOcc] using congrArg (fun x : NativeState => x.tags) h
  · simpa only [eraseOcc] using congrArg (fun x : NativeState => x.cycleCount) h
  · simpa only [eraseOcc] using congrArg (fun x : NativeState => x.sailOutput) h

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerCompose.timer_prepare_frame"
  (← IO.getStderr).flush

theorem timer_prepare_frame (s : NativeState) : TimerFrame s (timerPrepareState s) :=
  TimerFrame.of_eraseOcc_eq (erase_timer_prepare s)

#print axioms TimerFrame.trans
#print axioms TimerFrame.quiet
#print axioms TimerFrame.security_eq
#print axioms timer_prepare_frame

end NativeTagCheck.Hooks

-- Source proof structure: PMUQueries.lean
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
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUQueries.QueryResult"
  (← IO.getStderr).flush

def QueryResult {α : Type} (x : SailM α) (s : NativeState) : Prop :=
  ∃ v t, x s = .ok v t ∧ eraseOcc t = eraseOcc s

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUQueries.query_bind"
  (← IO.getStderr).flush

theorem query_bind {α β : Type} (x : SailM α) (f : α → SailM β) (s : NativeState)
    (hx : QueryResult x s)
    (hf : ∀ v t, eraseOcc t = eraseOcc s → QueryResult (f v) t) :
    QueryResult (x >>= f) s := by
  obtain ⟨v, t, hx, ht⟩ := hx
  obtain ⟨w, u, hf, hu⟩ := hf v t ht
  exact ⟨w, u, by simp only [bind_app, hx, hf], hu.trans ht⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUQueries.query_pure"
  (← IO.getStderr).flush

theorem query_pure {α : Type} (v : α) (s : NativeState) : QueryResult (pure v) s :=
  ⟨v, s, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUQueries.query_read"
  (← IO.getStderr).flush

theorem query_read {α : Type} (r : RegisterRef Regs α) (s : NativeState) :
    QueryResult (readReg r) s := ⟨r.get s.regs, s, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUQueries.halted_total"
  (← IO.getStderr).flush

theorem halted_total (s : NativeState) : ∃ b, (Halted () : SailM Bool) s = .ok b s := by
  have hED : (EDSCR_read () : SailM (BitVec 32)) s =
      .ok (Sail.BitVec.updateSubrange (s.regs.bank_BitVec_32 ._EDSCR) 30 29
        (BitVec.slice (s.regs.bank_BitVec_64 .MDCCSR_EL0) 29 2)) s := rfl
  simp only [Halted, bind_assoc, bind_if, pure_bind]
  simp only [bind_app, hED, pure_apply, map_apply, if_apply]
  repeat' first | split | exact ⟨_, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUQueries.external_debug_total"
  (← IO.getStderr).flush

theorem external_debug_total (s : NativeState) :
    ∃ b, (ExternalSecureNoninvasiveDebugEnabled () : SailM Bool) s = .ok b s := by
  cases hF : featureValue s .FEAT_Debugv8p4 <;>
    simp only [ExternalSecureNoninvasiveDebugEnabled, ExternalSecureInvasiveDebugEnabled,
      ExternalNoninvasiveDebugEnabled, ExternalInvasiveDebugEnabled,
      HaveNoninvasiveDebugAuth, HaveEL, bind_assoc, bind_if, pure_bind]
  all_goals simp only [bind_app, pure_apply, map_apply, if_apply,
      Bool.not_true, Bool.false_eq_true, reduceIte, feature_apply, hF, read_apply,
      Bool.not_false]
  all_goals repeat'
    try simp only [bind_app, pure_apply, map_apply, if_apply, read_apply]
    first | split | exact ⟨_, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUQueries.pmu_hyp_query"
  (← IO.getStderr).flush

theorem pmu_hyp_query (n : Int) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) : QueryResult (PMUCounterIsHyp n) s := by
  have hA := have_a64 (afterOcc 515 s) ha
  by_cases hI : n = (INSTRUCTION_COUNTER_ID : Int) <;>
    by_cases hC : n = (CYCLE_COUNTER_ID : Int) <;>
    cases hF : featureValue s .FEAT_HPMN0 <;>
    simp only [PMUCounterIsHyp, bind_assoc, bind_if, pure_bind] <;>
    simp only [QueryResult, bind_app, pure_apply, map_apply, if_apply,
      hI, hC, occ_apply, ubool, HaveEL, hA, read_apply, get_num_counters,
      HaveFeatHPMN0, feature_apply, afterOcc_feature, hF, ConstrainUnpredictableBool,
      beq_iff_eq, Bool.false_eq_true, reduceIte]
  all_goals repeat'
    try simp only [bind_app, pure_apply, map_apply, if_apply, read_apply, occ_apply, ubool,
      feature_apply, afterOcc_feature, hF, Bool.false_eq_true, reduceIte]
    first | split | exact ⟨_, _, rfl, by simp [eraseOcc, afterOcc, Std.ExtHashMap.getD_insert]⟩
#print axioms query_bind
#print axioms halted_total
#print axioms external_debug_total
#print axioms pmu_hyp_query
end NativeTagCheck.Hooks

-- Source proof structure: OverflowParts.lean
-- GENERATED by gen/gen_overflow_parts.py from actual PMUOverflowCondition.
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
namespace NativeTagCheck.Hooks.OverflowParts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowParts.preamble"
  (← IO.getStderr).flush

def preamble : SailM (Int × (BitVec 64)) := do
  let counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  let ovsf ← (( do (undefined_bitvector_at (← occLabel 516) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  let ovsf ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
        let ovsf := (w__1 : (BitVec 64))
        let ovsf : (BitVec 64) := (Sail.BitVec.updateSubrange ovsf 63 33 (Zeros (n := 31)))
        let w__2 ← (( do (HavePMUv3ICNTR ()) ) : SailM Bool )
        let ovsf : (BitVec 64) :=
          if ((! w__2) : Bool)
          then (BitVec.update ovsf INSTRUCTION_COUNTER_ID (Bit 0#1))
          else ovsf
        (pure (ovsf)))
    else
      (do
        let w__3 ← (( do (PMOVSR_read ()) ) : SailM (BitVec 32) )
        let ovsf := ((Sail.BitVec.zeroExtend w__3 64) : (BitVec 64))
        (pure (ovsf))) ) : SailM (BitVec 64) )
  let ovsf ← (( do
    if ((counters <b 31) : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b counters) && (counters ≤b 30)) "sail-arm/v8_base.sail:4603.61-4603.62"
        let ovsf : (BitVec 64) :=
          (Sail.BitVec.castWidth (Sail.BitVec.updateSubrange ovsf 30
            (Sail.Int.toNatChecked (counters))
            (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((31 -i counters))))))))
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  pure (counters, ovsf)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowParts.body"
  (← IO.getStderr).flush

def body (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool) (idx : Int) (ovsf : BitVec 64) : SailM (BitVec 64) := do
  let E ← (( do (undefined_bitvector_at (← occLabel 517) 1) ) : SailM (BitVec 1) )
  let is_hyp ← (( do (PMUCounterIsHyp idx) ) : SailM Bool )
  let w__4 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  let E ← (( do
    if (w__4 : Bool)
    then
      (do
        if (is_hyp : Bool)
        then
          (do
            let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_MDCR_EL2_Type_HPME w__5))))
        else
          (do
            let w__6 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
            (pure ((_get_PMCR_EL0_Type_E w__6)))))
    else
      (do
        if (is_hyp : Bool)
        then
          (do
            let w__8 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
            (pure ((_get_HDCR_Type_HPME w__8))))
        else
          (do
            let w__9 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
            (pure ((_get_PMCR_Type_E w__9))))) ) : SailM (BitVec 1) )
  let ovsf ← (( do
    if (check_e : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b idx) && (idx <b 64)) "sail-arm/v8_base.sail:4615.64-4615.65"
        let ovsf : (BitVec 64) :=
          (BitVec.update ovsf (Sail.Int.toNatChecked (idx))
            (Bit
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ovsf
                    (Sail.Int.toNatChecked (idx)))])) &&& E)))
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  if ((((! is_hyp) && (! include_lo_name)) || (is_hyp && (! include_hi_name))) : Bool)
  then
    (do
      ArmFull.assert ((0 ≤b idx) && (idx <b 64)) "sail-arm/v8_base.sail:4619.64-4619.65"
      let ovsf : (BitVec 64) := (BitVec.update ovsf (Sail.Int.toNatChecked (idx)) (Bit 0#1))
      (pure (ovsf)))
  else (pure (ovsf))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowParts.callback"
  (← IO.getStderr).flush

def callback (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool) (idx : Int) (ovsf : BitVec 64) : SailM (ForInStep (BitVec 64)) := do
  let E ← (( do (undefined_bitvector_at (← occLabel 517) 1) ) : SailM (BitVec 1) )
  let is_hyp ← (( do (PMUCounterIsHyp idx) ) : SailM Bool )
  let w__4 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  let E ← (( do
    if (w__4 : Bool)
    then
      (do
        if (is_hyp : Bool)
        then
          (do
            let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_MDCR_EL2_Type_HPME w__5))))
        else
          (do
            let w__6 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
            (pure ((_get_PMCR_EL0_Type_E w__6)))))
    else
      (do
        if (is_hyp : Bool)
        then
          (do
            let w__8 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
            (pure ((_get_HDCR_Type_HPME w__8))))
        else
          (do
            let w__9 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
            (pure ((_get_PMCR_Type_E w__9))))) ) : SailM (BitVec 1) )
  let ovsf ← (( do
    if (check_e : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b idx) && (idx <b 64)) "sail-arm/v8_base.sail:4615.64-4615.65"
        let ovsf : (BitVec 64) :=
          (BitVec.update ovsf (Sail.Int.toNatChecked (idx))
            (Bit
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ovsf
                    (Sail.Int.toNatChecked (idx)))])) &&& E)))
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  if ((((! is_hyp) && (! include_lo_name)) || (is_hyp && (! include_hi_name))) : Bool)
  then
    (do
      ArmFull.assert ((0 ≤b idx) && (idx <b 64)) "sail-arm/v8_base.sail:4619.64-4619.65"
      let ovsf : (BitVec 64) := (BitVec.update ovsf (Sail.Int.toNatChecked (idx)) (Bit 0#1))
      (pure (ForInStep.yield ovsf)))
  else (pure (ForInStep.yield ovsf))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowParts.loop"
  (← IO.getStderr).flush

def loop (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool) (counters : Int) (ovsf : BitVec 64) : SailM (BitVec 64) :=
  forIn ([0:counters-1:1]i : IntRange) ovsf
    (fun idx v => callback check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync idx v)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowParts.tail"
  (← IO.getStderr).flush

def tail (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool) (ovsf : BitVec 64) : SailM Bool := do
  let ovsf : (BitVec 64) :=
    if ((exclude_cyc || (! include_lo_name)) : Bool)
    then (BitVec.update ovsf CYCLE_COUNTER_ID (Bit 0#1))
    else ovsf
  let ovsf ← (( do
    if (check_e : Bool)
    then
      (do
        let w__11 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
        let ovsf :=
          ((BitVec.update ovsf CYCLE_COUNTER_ID
            (Bit
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ovsf CYCLE_COUNTER_ID)])) &&& (_get_PMCR_EL0_Type_E
                  w__11)))) : (BitVec 64))
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  let w__14 ← (( do
    if ((← do
         (HaveAArch64 ())) : Bool)
    then
      (do
        (HavePMUv3ICNTR ()))
    else (pure false) ) : SailM Bool )
  let ovsf ← (( do
    if (w__14 : Bool)
    then
      (do
        let ovsf : (BitVec 64) :=
          if ((! include_lo_name) : Bool)
          then (BitVec.update ovsf INSTRUCTION_COUNTER_ID (Bit 0#1))
          else ovsf
        if (check_e : Bool)
        then
          (do
            let w__15 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
            let ovsf :=
              ((BitVec.update ovsf INSTRUCTION_COUNTER_ID
                (Bit
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ovsf INSTRUCTION_COUNTER_ID)])) &&& (_get_PMCR_EL0_Type_E
                      w__15)))) : (BitVec 64))
            (pure (ovsf)))
        else (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  let ovsf ← (( do
    if (check_cnten : Bool)
    then
      (do
        let w__16 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let cnten ← (( do
          if (w__16 : Bool)
          then
            (do
              readReg PMCNTENCLR_EL0)
          else
            (do
              let w__18 ← (( do (PMCNTENCLR_read ()) ) : SailM (BitVec 32) )
              (pure ((Sail.BitVec.zeroExtend w__18 64)))) ) : SailM (BitVec 64) )
        let ovsf : (BitVec 64) := (ovsf &&& cnten)
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  let ovsf ← (( do
    if (check_inten : Bool)
    then
      (do
        let w__19 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let inten ← (( do
          if (w__19 : Bool)
          then
            (do
              readReg PMINTENCLR_EL1)
          else
            (do
              let w__21 ← (( do (PMINTENCLR_read ()) ) : SailM (BitVec 32) )
              (pure ((Sail.BitVec.zeroExtend w__21 64)))) ) : SailM (BitVec 64) )
        let ovsf : (BitVec 64) := (ovsf &&& inten)
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  (pure ((! (IsZero ovsf))))
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowParts.equation"
  (← IO.getStderr).flush

theorem equation (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool) (s : NativeState) :
    (PMUOverflowCondition check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : SailM Bool) s =
      (do let (counters, ovsf) ← preamble
          let ovsf ← loop check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync counters ovsf
          tail check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync ovsf : SailM Bool) s := by
  simp only [PMUOverflowCondition, preamble, loop, callback, tail, bind_assoc, pure_bind, bind_pure]
  rfl
#print axioms equation
end NativeTagCheck.Hooks.OverflowParts

-- Source proof structure: OverflowFacts.lean
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
set_option linter.unusedSimpArgs false
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowFacts.eraseOcc_regs"
  (← IO.getStderr).flush

theorem eraseOcc_regs {s t : NativeState} (h : eraseOcc t = eraseOcc s) : t.regs = s.regs := by
  simpa only [eraseOcc] using congrArg (fun x : NativeState => x.regs) h

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowFacts.overflow_preamble"
  (← IO.getStderr).flush

theorem overflow_preamble (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ ovsf, OverflowParts.preamble s =
      .ok (s.regs.bank_Int .NUM_PMU_COUNTERS, ovsf) (afterOcc 516 s) := by
  have hA := have_a64 (afterOcc 516 s) q.a64
  by_cases hc : s.regs.bank_Int .NUM_PMU_COUNTERS < 31
  · have hb : ((0 ≤b s.regs.bank_Int .NUM_PMU_COUNTERS) &&
        (s.regs.bank_Int .NUM_PMU_COUNTERS ≤b 30)) = true := by
      have hl := q.pmuCountLower
      simp; omega
    cases hI : featureValue s .FEAT_PMUv3_ICNTR <;>
      simp [OverflowParts.preamble, bind_assoc, bind_if, pure_bind, bind_app,
        get_num_counters, occ_apply, ubv, hA, HavePMUv3ICNTR, feature_apply,
        afterOcc_feature, hI, read_apply, hc, hb, assert_true, pure_apply, map_apply]
  · cases hI : featureValue s .FEAT_PMUv3_ICNTR <;>
      simp [OverflowParts.preamble, bind_assoc, bind_if, pure_bind, bind_app,
        get_num_counters, occ_apply, ubv, hA, HavePMUv3ICNTR, feature_apply,
        afterOcc_feature, hI, read_apply, hc, pure_apply, map_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowFacts.overflow_callback"
  (← IO.getStderr).flush

theorem overflow_callback (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool)
    (idx : Int) (ovsf : BitVec 64) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (hl : 0 ≤ idx) (hu : idx < 64) :
    ∃ (v : BitVec 64) (t : NativeState),
      OverflowParts.callback check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync idx ovsf s = .ok (.yield v) t ∧ eraseOcc t = eraseOcc s := by
  obtain ⟨hyp, t, ht, hframe⟩ := pmu_hyp_query idx (afterOcc 517 s) ha
  have hr : t.regs = s.regs := by simpa only [afterOcc] using eraseOcc_regs hframe
  have hat : featureValue t .FEAT_AA64EL0 = true := by
    unfold featureValue
    rw [hr]
    exact ha
  have hA := have_a64 t hat
  have hb : ((0 ≤b idx) && (idx <b 64)) = true := by simp; omega
  have hresult : ∃ v,
      OverflowParts.callback check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync idx ovsf s = .ok (.yield v) t := by
    cases hyp <;> cases check_e <;> cases include_hi_name <;> cases include_lo_name <;>
      simp only [OverflowParts.callback, bind_assoc, bind_if, pure_bind] <;>
      simp [bind_app, occ_apply, ubv, ht, hA, hb, assert_true, pure_apply, map_apply, read_apply]
  obtain ⟨v, hv⟩ := hresult
  exact ⟨v, t, hv, hframe.trans (by first | rfl | simp)⟩

#print axioms overflow_preamble
#print axioms overflow_callback
end NativeTagCheck.Hooks

-- Source proof structure: OverflowTail.lean
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
set_option linter.unusedSimpArgs false
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowTail.overflow_tail"
  (← IO.getStderr).flush

theorem overflow_tail (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool)
    (ovsf : BitVec 64) (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    ∃ b, OverflowParts.tail check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync ovsf s = .ok b s := by
  have hA := have_a64 s ha
  have hI : (HavePMUv3ICNTR () : SailM Bool) s = .ok (featureValue s .FEAT_PMUv3_ICNTR) s := rfl
  cases check_e <;> cases check_cnten <;> cases check_inten <;>
    cases include_lo_name <;> cases exclude_cyc <;>
    cases hIC : featureValue s .FEAT_PMUv3_ICNTR <;>
    simp [OverflowParts.tail, bind_assoc, bind_if, pure_bind, bind_app,
      hA, hI, hIC, read_apply, pure_apply, map_apply, if_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowTail.overflow_tail_masked"
  (← IO.getStderr).flush

theorem overflow_tail_masked (check_e check_cnten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool)
    (ovsf : BitVec 64) (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true)
    (hm : s.regs.bank_BitVec_64 .PMINTENCLR_EL1 = 0#64) :
    OverflowParts.tail check_e check_cnten true include_hi_name include_lo_name exclude_cyc exclude_sync ovsf s = .ok false s := by
  have hA := have_a64 s ha
  have hI : (HavePMUv3ICNTR () : SailM Bool) s = .ok (featureValue s .FEAT_PMUv3_ICNTR) s := rfl
  have hM : (readReg PMINTENCLR_EL1 : SailM (BitVec 64)) s = .ok 0#64 s := by
    rw [read_apply]
    congr 1
  cases check_e <;> cases check_cnten <;> cases include_lo_name <;> cases exclude_cyc <;>
    cases hIC : featureValue s .FEAT_PMUv3_ICNTR <;>
    simp [OverflowParts.tail, bind_assoc, bind_if, pure_bind, bind_app,
      hA, hI, hM, hIC, read_apply, pure_apply, map_apply, if_apply, IsZero, Zeros]
#print axioms overflow_tail
#print axioms overflow_tail_masked
end NativeTagCheck.Hooks

-- Source proof structure: OverflowRun.lean
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
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowRun.overflow_loop"
  (← IO.getStderr).flush

theorem overflow_loop (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool)
    (counters : Int) (ovsf : BitVec 64) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (hu : counters ≤ 31) :
    QueryResult (OverflowParts.loop check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync counters ovsf) s := by
  let range : IntRange := [0:counters-1:1]i
  let body := OverflowParts.callback check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync
  let I : BitVec 64 → NativeState → Prop := fun _ t => eraseOcc t = eraseOcc s
  have hs : I ovsf s := rfl
  have hstep : ∀ i, i ∈ range → ∀ b t, I b t →
      ∃ v u, body i b t = .ok v u ∧ I (stepValue v) u := by
    intro i hi b t ht
    have bounds : 0 ≤ i ∧ i ≤ counters-1 := by simpa [range, Membership.mem] using hi
    have hr : t.regs = s.regs := by simpa only [afterOcc] using eraseOcc_regs ht
    have hat : featureValue t .FEAT_AA64EL0 = true := by
      unfold featureValue
      rw [hr]
      exact ha
    obtain ⟨v, u, hv, hf⟩ := overflow_callback check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync
      i b t hat bounds.1 (by omega)
    exact ⟨.yield v, u, hv, hf.trans ht⟩
  exact range_forIn_preserves range body I hstep ovsf s hs

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowRun.overflow_condition_query"
  (← IO.getStderr).flush

theorem overflow_condition_query (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s)
    (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool) :
    QueryResult (PMUOverflowCondition check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync) s := by
  obtain ⟨ovsf, hp⟩ := overflow_preamble budget s q
  obtain ⟨v, t, hl, hf⟩ := overflow_loop check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync
    (s.regs.bank_Int .NUM_PMU_COUNTERS) ovsf (afterOcc 516 s) q.a64 q.pmuCountUpper
  have hr : t.regs = s.regs := by simpa only [afterOcc] using eraseOcc_regs hf
  have hat : featureValue t .FEAT_AA64EL0 = true := by
    unfold featureValue
    rw [hr]
    exact q.a64
  obtain ⟨b, ht⟩ := overflow_tail check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync v t hat
  refine ⟨b, t, ?_, hf.trans (by first | rfl | simp)⟩
  rw [OverflowParts.equation]
  simp only [bind_app, hp, hl, ht]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowRun.overflow_condition_masked"
  (← IO.getStderr).flush

theorem overflow_condition_masked (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s)
    (check_e check_cnten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool) :
    ∃ t, (PMUOverflowCondition check_e check_cnten true include_hi_name include_lo_name exclude_cyc exclude_sync : SailM Bool) s =
      .ok false t ∧ eraseOcc t = eraseOcc s := by
  obtain ⟨ovsf, hp⟩ := overflow_preamble budget s q
  obtain ⟨v, t, hl, hf⟩ := overflow_loop check_e check_cnten true include_hi_name include_lo_name exclude_cyc exclude_sync
    (s.regs.bank_Int .NUM_PMU_COUNTERS) ovsf (afterOcc 516 s) q.a64 q.pmuCountUpper
  have hr : t.regs = s.regs := by simpa only [afterOcc] using eraseOcc_regs hf
  have hat : featureValue t .FEAT_AA64EL0 = true := by
    unfold featureValue
    rw [hr]
    exact q.a64
  have hm : t.regs.bank_BitVec_64 .PMINTENCLR_EL1 = 0#64 := by rw [hr]; exact q.pmuIrqMask
  have ht := overflow_tail_masked check_e check_cnten include_hi_name include_lo_name exclude_cyc exclude_sync v t hat hm
  refine ⟨t, ?_, hf.trans (by first | rfl | simp)⟩
  rw [OverflowParts.equation]
  simp only [bind_app, hp, hl, ht]

#print axioms overflow_loop
#print axioms overflow_condition_query
#print axioms overflow_condition_masked
end NativeTagCheck.Hooks

-- Source proof structure: OverflowCheck.lean
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
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowCheck.PMUPost.of_eraseOcc_eq"
  (← IO.getStderr).flush

theorem PMUPost.of_eraseOcc_eq {budget : Nat} {s t : NativeState}
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (h : eraseOcc t = eraseOcc s) :
    PMUPost budget s t := by
  have hr := by simpa only [afterOcc] using eraseOcc_regs h
  have f := TimerFrame.of_eraseOcc_eq h
  refine ⟨?_, f.gic, f.mem, f.events, f.choiceState, f.tags, f.cycleCount, f.sailOutput, ?_⟩
  · change eraseE20 t.regs = eraseE20 s.regs
    rw [hr]
  · exact ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq hr.symm q

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.OverflowCheck.pmu_check_overflow_total"
  (← IO.getStderr).flush

theorem pmu_check_overflow_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (CheckForPMUOverflow () : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨t, ht, hf⟩ := overflow_condition_masked budget s q true false true true false false
  have hr := by simpa only [afterOcc] using eraseOcc_regs hf
  have qt := ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq hr.symm q
  have hB := should_brbe_paused t qt.a64 qt.el0 qt.nrw qt.scrRW qt.hcrRW qt.brbePaused
  have hE : eraseOcc (el0QueryState t) = eraseOcc t := by simp [el0QueryState]
  refine ⟨el0QueryState t, ?_, PMUPost.of_eraseOcc_eq q (hE.trans hf)⟩
  cases hP : featureValue t .FEAT_PMUv3p9 <;>
    cases hD : featureValue t .FEAT_Debugv8p9 <;>
    simp [CheckForPMUOverflow, bind_assoc, bind_if, pure_bind, bind_app, ht,
      irq_low, HavePMUv3p9, Havev8p9Debug, feature_apply, hP, hD, hB, pure_apply, map_apply]
#print axioms PMUPost.of_eraseOcc_eq
#print axioms pmu_check_overflow_total
end NativeTagCheck.Hooks

-- Source proof structure: CountParts.lean
-- GENERATED by gen/gen_count_parts.py from actual CountPMUEvents.
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmFull.SecurityState
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks.CountParts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountParts.start"
  (← IO.getStderr).flush

def start (idx : Nat) : SailM (Bool × Bool × SecurityState × Bool) := do
  let dp ← (( do (undefined_bitvector_at (← occLabel 530) 1) ) : SailM (BitVec 1) )
  let hccd ← (( do (undefined_bitvector_at (← occLabel 531) 1) ) : SailM (BitVec 1) )
  let hpmd ← (( do (undefined_bitvector_at (← occLabel 532) 1) ) : SailM (BitVec 1) )
  let sccd ← (( do (undefined_bitvector_at (← occLabel 533) 1) ) : SailM (BitVec 1) )
  let num_counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  let w__2 ← (( do
    if ((((idx == CYCLE_COUNTER_ID) || (idx <b num_counters)) : Bool) : Bool)
    then (pure true)
    else
      (do
        if (((idx == INSTRUCTION_COUNTER_ID) : Bool) : Bool)
        then
          (do
            (HavePMUv3ICNTR ()))
        else (pure false)) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:4945.108-4945.109"
  let enabled ← (( do (undefined_bool_at (← occLabel 534) ()) ) : SailM Bool )
  let filtered ← (( do (undefined_bool_at (← occLabel 535) ()) ) : SailM Bool )
  let E ← (( do (undefined_bitvector_at (← occLabel 536) 1) ) : SailM (BitVec 1) )
  let debug ← (( do (Halted ()) ) : SailM Bool )
  let resvd_for_el2 ← (( do (PMUCounterIsHyp idx) ) : SailM Bool )
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let questionMark : Nat := idx
  pure (debug, resvd_for_el2, ss, filtered)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountParts.enable"
  (← IO.getStderr).flush

def enable (idx : Nat) (resvd_for_el2 : Bool) : SailM (Bool) := do
  let questionMark : Nat := idx
  let enabled ← (( do
    if ((questionMark == INSTRUCTION_COUNTER_ID) : Bool)
    then
      (do
        let w__3 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        ArmFull.assert w__3 "sail-arm/v8_base.sail:4954.30-4954.31"
        if ((← do
             let w__4 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
             (pure ((((_get_PMCR_EL0_Type_E w__4) == 1#1) : Bool)))) : Bool)
        then
          (do
            let w__5 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
            (pure ((((_get_PMCNTENSET_EL0_Type_F0 w__5) == 1#1) : Bool))))
        else (pure false))
    else
      (do
        if ((questionMark == CYCLE_COUNTER_ID) : Bool)
        then
          (do
            let w__7 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            if (w__7 : Bool)
            then
              (do
                if ((← do
                     let w__8 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                     (pure ((((_get_PMCR_EL0_Type_E w__8) == 1#1) : Bool)))) : Bool)
                then
                  (do
                    let w__9 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
                    (pure ((((_get_PMCNTENSET_EL0_Type_C w__9) == 1#1) : Bool))))
                else (pure false))
            else
              (do
                if ((← do
                     let w__11 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                     (pure ((((_get_PMCR_Type_E w__11) == 1#1) : Bool)))) : Bool)
                then
                  (do
                    let w__12 ← (( do (PMCNTENSET_read ()) ) : SailM (BitVec 32) )
                    (pure ((((_get_PMCNTENSET_Type_C w__12) == 1#1) : Bool))))
                else (pure false)))
        else
          (do
            let E ← (( do
              if (resvd_for_el2 : Bool)
              then
                (do
                  let w__14 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_MDCR_EL2_Type_HPME w__15))))
                  else
                    (do
                      let w__16 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                      (pure ((_get_HDCR_Type_HPME w__16)))))
              else
                (do
                  let w__18 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      let w__19 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                      (pure ((_get_PMCR_EL0_Type_E w__19))))
                  else
                    (do
                      let w__20 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                      (pure ((_get_PMCR_Type_E w__20))))) ) : SailM (BitVec 1) )
            let w__22 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            if (w__22 : Bool)
            then
              (do
                if (((E == 1#1) : Bool) : Bool)
                then
                  (do
                    let w__23 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
                    (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__23 idx)])) == 1#1) : Bool))))
                else (pure false))
            else
              (do
                ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "sail-arm/v8_base.sail:4973.56-4973.57"
                if (((E == 1#1) : Bool) : Bool)
                then
                  (do
                    let w__25 ← (( do (PMCNTENSET_read ()) ) : SailM (BitVec 32) )
                    (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__25 idx)])) == 1#1) : Bool))))
                else (pure false)))) ) : SailM Bool )
  pure enabled

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountParts.prohibit"
  (← IO.getStderr).flush

def prohibit (ss : SecurityState) (resvd_for_el2 : Bool) : SailM (Bool) := do
  let prohibited : Bool := false
  let prohibited ← (( do
    if (((HaveEL EL3) && (BEq.beq ss SS_Secure)) : Bool)
    then
      (do
        let w__27 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        let prohibited ← (( do
          if ((! w__27) : Bool)
          then
            (do
              if ((← do
                   if ((← do
                        let w__28 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_MDCR_EL3_Type_SPME w__28) == 0#1) : Bool)))) : Bool)
                   then
                     (do
                       (HavePMUv3p7 ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__31 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_MDCR_EL3_Type_MPMX w__31) == 0#1) : Bool))))
              else (pure false))
          else
            (do
              let w__33 ← (( do readReg SDCR ) : SailM (BitVec 32) )
              let prohibited := (((_get_SDCR_Type_SPME w__33) == 0#1) : Bool)
              (pure (prohibited))) ) : SailM Bool )
        let w__35 ← (( do
          if ((prohibited : Bool) : Bool)
          then
            (do
              let w__34 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__34.EL == EL0) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__35 : Bool)
        then
          (do
            let w__36 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            if (w__36 : Bool)
            then
              (do
                let w__37 ← (( do (SDER_read ()) ) : SailM (BitVec 32) )
                let prohibited := (((_get_SDER_Type_SUNIDEN w__37) == 0#1) : Bool)
                (pure (prohibited)))
            else
              (do
                let w__38 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                if (w__38 : Bool)
                then
                  (do
                    let w__39 ← (( do (SDER32_EL3_read ()) ) : SailM (BitVec 64) )
                    let prohibited := (((_get_SDER32_EL3_Type_SUNIDEN w__39) == 0#1) : Bool)
                    (pure (prohibited)))
                else (pure (prohibited))))
        else (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let w__45 ← (( do
    if ((← do
         if ((← do
              if (((! prohibited) : Bool) : Bool)
              then
                (do
                  (HavePMUv3p7 ()))
              else (pure false)) : Bool)
         then
           (do
             let w__42 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__42.EL == EL3) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (HaveAArch64 ()))
    else (pure false) ) : SailM Bool )
  let prohibited ← (( do
    if (w__45 : Bool)
    then
      (do
        if ((← do
             let w__46 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
             (pure ((((_get_MDCR_EL3_Type_MPMX w__46) == 1#1) : Bool)))) : Bool)
        then
          (pure ((← do
                let w__47 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                (pure ((((_get_MDCR_EL3_Type_SPME w__47) == 0#1) : Bool)))) || (! resvd_for_el2)))
        else (pure false))
    else (pure (prohibited)) ) : SailM Bool )
  let w__54 ← (( do
    (pure ((← do
          if ((← do
               if (((! prohibited) : Bool) : Bool)
               then
                 (do
                   let w__50 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__50.EL == EL2) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              (HaveHPMDExt ()))
          else (pure false)) && (! resvd_for_el2))) ) : SailM Bool )
  let prohibited ← (( do
    if (w__54 : Bool)
    then
      (do
        let w__55 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let hpmd ← (( do
          if (w__55 : Bool)
          then
            (do
              let w__56 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_MDCR_EL2_Type_HPMD w__56))))
          else
            (do
              let w__57 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
              (pure ((_get_HDCR_Type_HPMD w__57)))) ) : SailM (BitVec 1) )
        let prohibited : Bool := (hpmd == 1#1)
        (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let w__59 ← (( do
    if ((prohibited : Bool) : Bool)
    then
      (do
        let w__58 ← (( do (HaveNoSecurePMUDisableOverride ()) ) : SailM Bool )
        (pure (((! w__58) : Bool))))
    else (pure false) ) : SailM Bool )
  let prohibited ← (( do
    if (w__59 : Bool)
    then
      (do
        let w__60 ← (( do (ExternalSecureNoninvasiveDebugEnabled ()) ) : SailM Bool )
        let prohibited := ((! w__60) : Bool)
        (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  pure prohibited

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountParts.freeze"
  (← IO.getStderr).flush

def freeze (resvd_for_el2 : Bool) : SailM (Bool) := do
  let frozen : Bool := false
  let w__61 ← (( do (HavePMUv3p7 ()) ) : SailM Bool )
  let frozen ← (( do
    if (w__61 : Bool)
    then
      (do
        let FZ ← (( do (undefined_bitvector_at (← occLabel 537) 1) ) : SailM (BitVec 1) )
        let FZ ← (( do
          if (resvd_for_el2 : Bool)
          then
            (do
              let w__62 ← (( do (HaveAArch64 ()) ) : SailM Bool )
              if (w__62 : Bool)
              then
                (do
                  let w__63 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MDCR_EL2_Type_HPMFZO w__63))))
              else
                (do
                  let w__64 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                  (pure ((_get_HDCR_Type_HPMFZO w__64)))))
          else
            (do
              let w__66 ← (( do (HaveAArch64 ()) ) : SailM Bool )
              if (w__66 : Bool)
              then
                (do
                  let w__67 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                  (pure ((_get_PMCR_EL0_Type_FZO w__67))))
              else
                (do
                  let w__68 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                  (pure ((_get_PMCR_Type_FZO w__68))))) ) : SailM (BitVec 1) )
        if (((FZ == 1#1) : Bool) : Bool)
        then
          (do
            (HiLoPMUOverflow resvd_for_el2))
        else (pure false))
    else (pure (frozen)) ) : SailM Bool )
  pure frozen

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountParts.adjust"
  (← IO.getStderr).flush

def adjust (idx : Nat) (ss : SecurityState) (resvd_for_el2 enabled frozen prohibited : Bool) : SailM (Bool × Bool × Bool) := do
  let (enabled, frozen, prohibited) ← (( do
    if (((prohibited || frozen) && (idx == CYCLE_COUNTER_ID)) : Bool)
    then
      (do
        let w__72 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let dp ← (( do
          if (w__72 : Bool)
          then
            (do
              let w__73 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
              (pure ((_get_PMCR_EL0_Type_DP w__73))))
          else
            (do
              let w__74 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
              (pure ((_get_PMCR_Type_DP w__74)))) ) : SailM (BitVec 1) )
        let enabled : Bool := (enabled && (dp == 0#1))
        let prohibited : Bool := false
        let frozen : Bool := false
        (pure ((enabled, frozen, prohibited))))
    else (pure ((enabled, frozen, prohibited))) ) : SailM (Bool × Bool × Bool) )
  let w__76 ← (( do
    (pure ((← do
          (HavePMUv3p5 ())) && ((idx == CYCLE_COUNTER_ID) : Bool))) ) : SailM Bool )
  let prohibited ← (( do
    if (w__76 : Bool)
    then
      (do
        let prohibited ← (( do
          if (((HaveEL EL3) && (BEq.beq ss SS_Secure)) : Bool)
          then
            (do
              let w__77 ← (( do (HaveAArch64 ()) ) : SailM Bool )
              let sccd ← (( do
                if (w__77 : Bool)
                then
                  (do
                    let w__78 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                    (pure ((_get_MDCR_EL3_Type_SCCD w__78))))
                else
                  (do
                    let w__79 ← (( do readReg SDCR ) : SailM (BitVec 32) )
                    (pure ((_get_SDCR_Type_SCCD w__79)))) ) : SailM (BitVec 1) )
              let prohibited : Bool :=
                if ((sccd == 1#1) : Bool)
                then true
                else prohibited
              (pure (prohibited)))
          else (pure (prohibited)) ) : SailM Bool )
        let w__80 ← (( do readReg PSTATE ) : SailM ProcState )
        if ((w__80.EL == EL2) : Bool)
        then
          (do
            let w__81 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            let hccd ← (( do
              if (w__81 : Bool)
              then
                (do
                  let w__82 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MDCR_EL2_Type_HCCD w__82))))
              else
                (do
                  let w__83 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                  (pure ((_get_HDCR_Type_HCCD w__83)))) ) : SailM (BitVec 1) )
            let prohibited : Bool :=
              if ((hccd == 1#1) : Bool)
              then true
              else prohibited
            (pure (prohibited)))
        else (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let w__85 ← (( do
    (pure ((← do
          (HavePMUv3p7 ())) && ((idx == CYCLE_COUNTER_ID) : Bool))) ) : SailM Bool )
  let prohibited ← (( do
    if (w__85 : Bool)
    then
      (do
        let w__90 ← (( do
          if ((← do
               if ((← do
                    let w__86 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__86.EL == EL3) : Bool)))) : Bool)
               then
                 (do
                   (HaveAArch64 ()))
               else (pure false)) : Bool)
          then
            (do
              let w__89 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_MDCR_EL3_Type_MCCD w__89) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let prohibited : Bool :=
          if (w__90 : Bool)
          then true
          else prohibited
        (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  pure (enabled, frozen, prohibited)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountParts.getFilter"
  (← IO.getStderr).flush

def getFilter (idx : Nat) : SailM (BitVec 32) := do
  let questionMark : Nat := idx
  let filter ← (( do (undefined_bitvector_at (← occLabel 538) 32) ) : SailM (BitVec 32) )
  let questionMark : Nat := idx
  let filter ← (( do
    if ((questionMark == INSTRUCTION_COUNTER_ID) : Bool)
    then
      (do
        let w__91 ← (( do readReg PMICFILTR_EL0 ) : SailM (BitVec 64) )
        let filter := ((Sail.BitVec.extractLsb w__91 31 0) : (BitVec 32))
        (pure (filter)))
    else
      (do
        if ((questionMark == CYCLE_COUNTER_ID) : Bool)
        then
          (do
            let w__92 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            if (w__92 : Bool)
            then
              (do
                let w__93 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
                (pure ((Sail.BitVec.extractLsb w__93 31 0))))
            else
              (do
                (PMCCFILTR_read ())))
        else
          (do
            let w__96 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            if (w__96 : Bool)
            then
              (do
                ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "sail-arm/v8_base.sail:5058.56-5058.57"
                let w__97 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
                (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! w__97 idx) 31 0))))
            else
              (do
                ArmFull.assert ((0 ≤b idx) && (idx <b 31)) "sail-arm/v8_base.sail:5061.56-5061.57"
                (PMEVTYPER_read idx)))) ) : SailM (BitVec 32) )
  pure filter

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountParts.finish"
  (← IO.getStderr).flush

def finish (debug enabled frozen prohibited filtered : Bool) (filter : BitVec 32) : SailM (Bool) := do
  let filter := filter
  let P : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 31)]))
  let U : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 30)]))
  let NSK : (BitVec 1) :=
    if ((HaveEL EL3) : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 29)]))
    else 0#1
  let NSU : (BitVec 1) :=
    if ((HaveEL EL3) : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 28)]))
    else 0#1
  let NSH : (BitVec 1) :=
    if ((HaveEL EL2) : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 27)]))
    else 0#1
  let w__101 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        (HaveAArch64 ()))
    else (pure false) ) : SailM Bool )
  let M : (BitVec 1) :=
    if (w__101 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 26)]))
    else 0#1
  let w__103 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        (HaveSecureEL2Ext ()))
    else (pure false) ) : SailM Bool )
  let SH : (BitVec 1) :=
    if (w__103 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 24)]))
    else 0#1
  let w__104 ← (( do (HaveRME ()) ) : SailM Bool )
  let RLK : (BitVec 1) :=
    if (w__104 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 22)]))
    else 0#1
  let w__105 ← (( do (HaveRME ()) ) : SailM Bool )
  let RLU : (BitVec 1) :=
    if (w__105 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 21)]))
    else 0#1
  let w__106 ← (( do (HaveRME ()) ) : SailM Bool )
  let RLH : (BitVec 1) :=
    if (w__106 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 20)]))
    else 0#1
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let w__107 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__107.EL
  let filtered ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (let filtered : Bool :=
        match ss with
        | .SS_NonSecure => (U != NSU)
        | .SS_Secure => (U == 1#1)
        | .SS_Realm => (U != RLU)
        | _ => filtered
      (pure (filtered)))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (let filtered : Bool :=
            match ss with
            | .SS_NonSecure => (P != NSK)
            | .SS_Secure => (P == 1#1)
            | .SS_Realm => (P != RLK)
            | _ => filtered
          (pure (filtered)))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (let filtered : Bool :=
                match ss with
                | .SS_NonSecure => (NSH == 0#1)
                | .SS_Secure => (NSH == SH)
                | .SS_Realm => (NSH == RLH)
                | _ => filtered
              (pure (filtered)))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__108 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                    let filtered : Bool :=
                      if (w__108 : Bool)
                      then (M != P)
                      else (P == 1#1)
                    (pure (filtered)))
                else (pure (filtered))))) ) : SailM Bool )
  (pure ((((((! debug) && enabled) && (! prohibited)) && (! filtered)) && (! frozen))))
set_option maxHeartbeats 100000 in
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountParts.equation"
  (← IO.getStderr).flush

theorem equation (idx : Nat) (s : NativeState) :
    (CountPMUEvents idx : SailM Bool) s =
      (do let (debug, resvd, ss, filtered) ← start idx
          let enabled ← enable idx resvd
          let prohibited ← prohibit ss resvd
          let frozen ← freeze resvd
          let (enabled, frozen, prohibited) ← adjust idx ss resvd enabled frozen prohibited
          let filter ← getFilter idx
          finish debug enabled frozen prohibited filtered filter : SailM Bool) s := by
  simp only [CountPMUEvents, start, enable, prohibit, freeze, adjust, getFilter, finish,
    bind_assoc, pure_bind]
  rfl
#print axioms equation
end NativeTagCheck.Hooks.CountParts

-- Source proof structure: CountSimple.lean
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
set_option linter.unusedSimpArgs false
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountSimple.count_enable_total"
  (← IO.getStderr).flush

theorem count_enable_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (resvd : Bool) :
    ∃ b, CountParts.enable idx resvd s = .ok b s := by
  cases resvd <;>
    by_cases hI : idx = INSTRUCTION_COUNTER_ID <;>
    by_cases hC : idx = CYCLE_COUNTER_ID <;>
    rcases bit_cases (_get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0)) with hE | hE <;>
    rcases bit_cases (_get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2)) with hH | hH <;>
    simp_all [CountParts.enable, bind_assoc, bind_if, pure_bind, bind_app,
      hI, hC, hE, hH, INSTRUCTION_COUNTER_ID, CYCLE_COUNTER_ID, have_a64 s q.a64, assert_true, read_apply, pure_apply, map_apply, if_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountSimple.count_filter_total"
  (← IO.getStderr).flush

theorem count_filter_total (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true)
    (idx : Nat) (hi : idx = INSTRUCTION_COUNTER_ID ∨ idx = CYCLE_COUNTER_ID ∨ idx < 32) :
    ∃ filter, CountParts.getFilter idx s = .ok filter (afterOcc 538 s) := by
  have hA := have_a64 (afterOcc 538 s) ha
  have hb : idx = INSTRUCTION_COUNTER_ID ∨ idx = CYCLE_COUNTER_ID ∨ ((0 ≤b idx) && (idx <b 32)) = true := by
    rcases hi with hi | hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (by simp; omega))
  by_cases hI : idx = INSTRUCTION_COUNTER_ID <;>
    by_cases hC : idx = CYCLE_COUNTER_ID <;>
    simp_all [CountParts.getFilter, bind_assoc, bind_if, pure_bind, bind_app,
      INSTRUCTION_COUNTER_ID, CYCLE_COUNTER_ID,
      occ_apply, ubv, hA, read_apply, assert_true, pure_apply, map_apply, if_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountSimple.count_finish_total"
  (← IO.getStderr).flush

theorem count_finish_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s)
    (debug enabled frozen prohibited filtered : Bool) (filter : BitVec 32) :
    ∃ b, CountParts.finish debug enabled frozen prohibited filtered filter s =
      .ok b (securityQueryState s) := by
  have hA := have_a64 s q.a64
  cases hS : featureValue s .FEAT_SEL2 <;>
    cases hR : featureValue s .FEAT_RME <;>
    cases hSS : securityValue s <;>
    simp [CountParts.finish, bind_assoc, bind_if, pure_bind, bind_app,
      HaveEL, hA, HaveSecureEL2Ext, HaveRME, feature_apply, hS, hR,
      current_security_quiet budget s q, hSS, read_apply, security_query_regs,
      q.el0, EL0, pure_apply, map_apply, if_apply]
#print axioms count_enable_total
#print axioms count_filter_total
#print axioms count_finish_total
end NativeTagCheck.Hooks

-- Source proof structure: CountStartParts.lean
-- GENERATED by gen/gen_count_start.py; exact actual eligibility/prefix split.
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmFull.SecurityState
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks.CountStartParts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountStartParts.check"
  (← IO.getStderr).flush

def check (idx : Nat) : SailM Unit := do
  let dp ← (( do (undefined_bitvector_at (← occLabel 530) 1) ) : SailM (BitVec 1) )
  let hccd ← (( do (undefined_bitvector_at (← occLabel 531) 1) ) : SailM (BitVec 1) )
  let hpmd ← (( do (undefined_bitvector_at (← occLabel 532) 1) ) : SailM (BitVec 1) )
  let sccd ← (( do (undefined_bitvector_at (← occLabel 533) 1) ) : SailM (BitVec 1) )
  let num_counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  let w__2 ← (( do
    if ((((idx == CYCLE_COUNTER_ID) || (idx <b num_counters)) : Bool) : Bool)
    then (pure true)
    else
      (do
        if (((idx == INSTRUCTION_COUNTER_ID) : Bool) : Bool)
        then
          (do
            (HavePMUv3ICNTR ()))
        else (pure false)) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:4945.108-4945.109"
  pure ()

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountStartParts.tail"
  (← IO.getStderr).flush

def tail (idx : Nat) : SailM (Bool × Bool × SecurityState × Bool) := do
  let enabled ← (( do (undefined_bool_at (← occLabel 534) ()) ) : SailM Bool )
  let filtered ← (( do (undefined_bool_at (← occLabel 535) ()) ) : SailM Bool )
  let E ← (( do (undefined_bitvector_at (← occLabel 536) 1) ) : SailM (BitVec 1) )
  let debug ← (( do (Halted ()) ) : SailM Bool )
  let resvd_for_el2 ← (( do (PMUCounterIsHyp idx) ) : SailM Bool )
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let questionMark : Nat := idx
  pure (debug, resvd_for_el2, ss, filtered)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountStartParts.equation"
  (← IO.getStderr).flush

theorem equation (idx : Nat) (s : NativeState) : CountParts.start idx s =
    (do check idx
        tail idx : SailM (Bool × Bool × SecurityState × Bool)) s := by
  simp only [CountParts.start, check, tail, bind_assoc, pure_bind]
  all_goals rfl
#print axioms equation
end NativeTagCheck.Hooks.CountStartParts

-- Source proof structure: CountFreeze.lean
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
set_option linter.unusedSimpArgs false
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountFreeze.freezeBit"
  (← IO.getStderr).flush

def freezeBit (resvd : Bool) (s : NativeState) : BitVec 1 :=
  if resvd then _get_MDCR_EL2_Type_HPMFZO (s.regs.bank_BitVec_64 .MDCR_EL2)
  else _get_PMCR_EL0_Type_FZO (s.regs.bank_BitVec_64 .PMCR_EL0)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountFreeze.count_freeze_shape"
  (← IO.getStderr).flush

theorem count_freeze_shape (resvd : Bool) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) :
    CountParts.freeze resvd s =
      (if featureValue s .FEAT_PMUv3p7 then
        if freezeBit resvd s == 1#1 then HiLoPMUOverflow resvd (afterOcc 537 s)
        else .ok false (afterOcc 537 s)
      else .ok false s) := by
  have hA := have_a64 (afterOcc 537 s) ha
  cases resvd <;> cases hF : featureValue s .FEAT_PMUv3p7 <;>
    rcases bit_cases (_get_MDCR_EL2_Type_HPMFZO (s.regs.bank_BitVec_64 .MDCR_EL2)) with hH | hH <;>
    rcases bit_cases (_get_PMCR_EL0_Type_FZO (s.regs.bank_BitVec_64 .PMCR_EL0)) with hP | hP <;>
    simp [CountParts.freeze, freezeBit, bind_assoc, bind_if, pure_bind, bind_app,
      occ_apply, ubv, HavePMUv3p7, feature_apply, hF, hA, hH, hP, read_apply, pure_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountFreeze.count_freeze_query"
  (← IO.getStderr).flush

theorem count_freeze_query (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (resvd : Bool) :
    QueryResult (CountParts.freeze resvd) s := by
  have qa : ArmCert.HookQuiet.V0.HookQuiet budget (afterOcc 537 s) :=
    ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq (s := s) (t := afterOcc 537 s) rfl q
  obtain ⟨b, t, ht, hf⟩ := overflow_condition_query budget (afterOcc 537 s) qa
    false false false resvd (!resvd) false false
  have hh : (HiLoPMUOverflow resvd : SailM Bool) (afterOcc 537 s) = .ok b t := by
    simpa only [HiLoPMUOverflow] using ht
  unfold QueryResult
  rw [count_freeze_shape resvd s q.a64]
  split
  · split
    · exact ⟨b, t, hh, hf.trans (by first | rfl | simp)⟩
    · exact ⟨false, afterOcc 537 s, rfl, by simp⟩
  · exact ⟨false, s, rfl, rfl⟩
#print axioms count_freeze_shape
#print axioms count_freeze_query
end NativeTagCheck.Hooks

-- Source proof structure: CountAdjust.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmFull.SecurityState
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountAdjust.security_eq_secure"
  (← IO.getStderr).flush

theorem security_eq_secure (ss : SecurityState) : (ss == SS_Secure) =
    (match ss with | .SS_Secure => true | _ => false) := by cases ss <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountAdjust.count_adjust_total"
  (← IO.getStderr).flush

set_option maxHeartbeats 200000 in
theorem count_adjust_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (ss : SecurityState)
    (resvd enabled frozen prohibited : Bool) :
    ∃ v, CountParts.adjust idx ss resvd enabled frozen prohibited s = .ok v s := by
  by_cases hC : idx = 31
  · cases frozen <;> cases prohibited <;> cases ss <;>
      cases h5 : featureValue s .FEAT_PMUv3p5 <;>
      cases h7 : featureValue s .FEAT_PMUv3p7 <;>
      simp [CountParts.adjust, bind_assoc, bind_if, pure_bind, bind_app,
      CYCLE_COUNTER_ID, HaveEL, have_a64 s q.a64, HavePMUv3p5, HavePMUv3p7,
      feature_apply, h5, h7, read_apply, q.el0, EL0, EL2, EL3,
      hC, security_eq_secure,
      pure_apply, map_apply, if_apply]
  · simp [CountParts.adjust, bind_assoc, bind_if, pure_bind, bind_app,
      CYCLE_COUNTER_ID, HaveEL, have_a64 s q.a64, HavePMUv3p5, HavePMUv3p7,
      feature_apply, read_apply, q.el0, EL0, EL2, EL3,
      hC, security_eq_secure,
      pure_apply, map_apply, if_apply]
#print axioms count_adjust_total
end NativeTagCheck.Hooks

-- Source proof structure: CountProhibit.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmFull.SecurityState
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false
namespace NativeTagCheck.Hooks

@[simp] theorem el3_query_regs (s : NativeState) : (el3QueryState s).regs = s.regs := rfl
@[simp] theorem el3_query_feature (s : NativeState) (f : Feature) :
    featureValue (el3QueryState s) f = featureValue s f := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountProhibit.el_query_nonzero"
  (← IO.getStderr).flush

theorem el_query_nonzero (el : BitVec 2) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (he : el ≠ 0#2) :
    (ELUsingAArch32 el : SailM Bool) s = .ok false (el3QueryState s) :=
  el_using_nonzero el s ha he

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountProhibit.prohibitBit"
  (← IO.getStderr).flush

def prohibitBit (s : NativeState) : Bool :=
  (_get_MDCR_EL3_Type_SPME (s.regs.bank_BitVec_64 .MDCR_EL3) == 0#1) &&
    featureValue s .FEAT_PMUv3p7 &&
    (_get_MDCR_EL3_Type_MPMX (s.regs.bank_BitVec_64 .MDCR_EL3) == 0#1)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountProhibit.prohibitState"
  (← IO.getStderr).flush

def prohibitState (ss : SecurityState) (s : NativeState) : NativeState :=
  if ss == SS_Secure then
    if prohibitBit s then el3QueryState (el3QueryState (el3QueryState s))
    else el3QueryState s
  else s

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountProhibit.count_prohibit_total"
  (← IO.getStderr).flush

set_option maxHeartbeats 200000 in
theorem count_prohibit_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (ss : SecurityState) (resvd : Bool) :
    ∃ b, CountParts.prohibit ss resvd s = .ok b (prohibitState ss s) := by
  obtain ⟨db, hd⟩ := external_debug_total (el3QueryState (el3QueryState (el3QueryState s)))
  have ha : featureValue s .FEAT_AA64EL0 = true := q.a64
  cases ss
  case SS_Secure =>
    cases h7 : featureValue s .FEAT_PMUv3p7 <;>
    cases hD : featureValue s .FEAT_Debugv8p2 <;>
    rcases bit_cases (_get_MDCR_EL3_Type_SPME (s.regs.bank_BitVec_64 .MDCR_EL3)) with hS | hS <;>
    rcases bit_cases (_get_MDCR_EL3_Type_MPMX (s.regs.bank_BitVec_64 .MDCR_EL3)) with hM | hM <;>
    simp [CountParts.prohibit, prohibitState, prohibitBit,
      bind_assoc, bind_if, pure_bind, bind_app, pure_apply, map_apply, if_apply,
      HaveEL, HavePMUv3p7, HaveNoSecurePMUDisableOverride, feature_apply,
      el_query_nonzero, ha, el3_query_feature, read_apply, el3_query_regs,
      h7, hD, hS, hM, hd, q.el0, EL0, EL1, EL2, EL3,
      security_eq_secure]
  all_goals
    cases h7 : featureValue s .FEAT_PMUv3p7 <;>
      simp [CountParts.prohibit, prohibitState, prohibitBit,
      bind_assoc, bind_if, pure_bind, bind_app, pure_apply, map_apply, if_apply,
      HaveEL, HavePMUv3p7, HaveNoSecurePMUDisableOverride, feature_apply,
      el_query_nonzero, ha, el3_query_feature, read_apply, el3_query_regs,
      h7, hd, q.el0, EL0, EL1, EL2, EL3,
      security_eq_secure]
#print axioms count_prohibit_total
end NativeTagCheck.Hooks

-- Source proof structure: CountStart.lean
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
set_option linter.unusedSimpArgs false
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountStart.CountIndexValid"
  (← IO.getStderr).flush

def CountIndexValid (idx : Nat) (s : NativeState) : Prop :=
  idx = CYCLE_COUNTER_ID ∨ (idx : Int) < s.regs.bank_Int .NUM_PMU_COUNTERS ∨
    (idx = INSTRUCTION_COUNTER_ID ∧ featureValue s .FEAT_PMUv3_ICNTR = true)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountStart.countCheckState"
  (← IO.getStderr).flush

def countCheckState (s : NativeState) : NativeState :=
  afterOcc 533 (afterOcc 532 (afterOcc 531 (afterOcc 530 s)))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountStart.countTailState"
  (← IO.getStderr).flush

def countTailState (s : NativeState) : NativeState :=
  afterOcc 536 (afterOcc 535 (afterOcc 534 s))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountStart.count_check_total"
  (← IO.getStderr).flush

theorem count_check_total (s : NativeState) (idx : Nat) (hi : CountIndexValid idx s) :
    CountStartParts.check idx s = .ok () (countCheckState s) := by
  rcases hi with hc | hl | ⟨hI, hIC⟩
  · subst idx
    simp [CountStartParts.check, countCheckState, bind_assoc, bind_if, pure_bind,
      bind_app, occ_apply, ubv, get_num_counters, CYCLE_COUNTER_ID,
      assert_true, pure_apply]
  · simp [CountStartParts.check, countCheckState, bind_assoc, bind_if, pure_bind,
      bind_app, occ_apply, ubv, get_num_counters, hl, assert_true, pure_apply]
  · subst idx
    simp [CountStartParts.check, countCheckState, bind_assoc, bind_if, pure_bind,
      bind_app, occ_apply, ubv, get_num_counters, INSTRUCTION_COUNTER_ID, CYCLE_COUNTER_ID,
      HavePMUv3ICNTR, feature_apply, afterOcc_feature, hIC, assert_true, pure_apply]
    split <;> simp [bind_app, feature_apply, afterOcc_feature, hIC, assert_true, pure_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountStart.count_start_tail_query"
  (← IO.getStderr).flush

theorem count_start_tail_query (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) :
    QueryResult (CountStartParts.tail idx) s := by
  obtain ⟨debug, hd⟩ := halted_total (countTailState s)
  obtain ⟨resvd, t, hh, hf⟩ := pmu_hyp_query (idx : Int) (countTailState s) q.a64
  have hr : t.regs = s.regs := by simpa only [countTailState, afterOcc] using eraseOcc_regs hf
  have qt := ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq (s := s) (t := t) hr.symm q
  have hS := current_security_quiet budget t qt
  have hv : ∃ v, CountStartParts.tail idx s = .ok v (securityQueryState t) := by
    simp only [countTailState] at hd hh
    simp [CountStartParts.tail, bind_assoc, pure_bind, bind_app, occ_apply,
      ubool, ubv, hd, hh, hS, pure_apply, map_apply]
  obtain ⟨v, hv⟩ := hv
  exact ⟨v, securityQueryState t, hv, (erase_security_query t).trans (hf.trans (by simp [countTailState, countCheckState]))⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountStart.count_start_query"
  (← IO.getStderr).flush

theorem count_start_query (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (hi : CountIndexValid idx s) :
    QueryResult (CountParts.start idx) s := by
  have hc := count_check_total s idx hi
  have qa : ArmCert.HookQuiet.V0.HookQuiet budget (countCheckState s) :=
    ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq (s := s) (t := countCheckState s) rfl q
  obtain ⟨v, t, ht, hf⟩ := count_start_tail_query budget (countCheckState s) qa idx
  refine ⟨v, t, ?_, hf.trans (by simp [countTailState, countCheckState])⟩
  rw [CountStartParts.equation]
  simp only [bind_app, hc, ht]
#print axioms count_check_total
#print axioms count_start_tail_query
#print axioms count_start_query
end NativeTagCheck.Hooks

-- Source proof structure: CountRun.lean
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
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountRun.quiet_of_eraseOcc_eq"
  (← IO.getStderr).flush

theorem quiet_of_eraseOcc_eq {budget : Nat} {s t : NativeState}
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (h : eraseOcc t = eraseOcc s) :
    ArmCert.HookQuiet.V0.HookQuiet budget t :=
  ArmCert.HookQuiet.V0.hookQuiet_of_regs_eq (s := s) (t := t) (eraseOcc_regs h).symm q

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountRun.erase_el3_query"
  (← IO.getStderr).flush

theorem erase_el3_query (s : NativeState) : eraseOcc (el3QueryState s) = eraseOcc s := by simp [eraseOcc, el3QueryState, afterOcc, Std.ExtHashMap.getD_insert]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountRun.erase_prohibit_state"
  (← IO.getStderr).flush

theorem erase_prohibit_state (ss : SecurityState) (s : NativeState) :
    eraseOcc (prohibitState ss s) = eraseOcc s := by
  unfold prohibitState
  split
  · split <;> simp only [erase_el3_query]
  · simp [eraseOcc, afterOcc, Std.ExtHashMap.getD_insert]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountRun.count_index_bounds"
  (← IO.getStderr).flush

theorem count_index_bounds (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (h : CountIndexValid idx s) :
    idx = INSTRUCTION_COUNTER_ID ∨ idx = CYCLE_COUNTER_ID ∨ idx < 32 := by
  rcases h with h | h | ⟨h, _⟩
  · exact Or.inr (Or.inl h)
  · have hu := q.pmuCountUpper
    exact Or.inr (Or.inr (by omega))
  · exact Or.inl h

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CountRun.count_pmu_events_query"
  (← IO.getStderr).flush

theorem count_pmu_events_query (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (h : CountIndexValid idx s) :
    QueryResult (CountPMUEvents idx) s := by
  obtain ⟨v0, s1, h0, f0⟩ := count_start_query budget s q idx h
  rcases v0 with ⟨debug, resvd, ss, filtered⟩
  have q1 := quiet_of_eraseOcc_eq q f0
  obtain ⟨enabled, he⟩ := count_enable_total budget s1 q1 idx resvd
  obtain ⟨prohibited, hp⟩ := count_prohibit_total budget s1 q1 ss resvd
  let s2 := prohibitState ss s1
  have f1 : eraseOcc s2 = eraseOcc s1 := erase_prohibit_state ss s1
  have q2 := quiet_of_eraseOcc_eq q1 f1
  obtain ⟨frozen, s3, hf, f2⟩ := count_freeze_query budget s2 q2 resvd
  have q3 := quiet_of_eraseOcc_eq q2 f2
  obtain ⟨v3, ha⟩ := count_adjust_total budget s3 q3 idx ss resvd enabled frozen prohibited
  rcases v3 with ⟨enabled3, frozen3, prohibited3⟩
  obtain ⟨filter, hg⟩ := count_filter_total s3 q3.a64 idx (count_index_bounds budget s q idx h)
  let s4 := afterOcc 538 s3
  have f3 : eraseOcc s4 = eraseOcc s3 := by simpa only [s4] using erase_afterOcc 538 s3 (by decide)
  have q4 := quiet_of_eraseOcc_eq q3 f3
  obtain ⟨result, hz⟩ := count_finish_total budget s4 q4 debug enabled3 frozen3 prohibited3 filtered filter
  refine ⟨result, securityQueryState s4, ?_, ?_⟩
  · rw [CountParts.equation]
    simp only [s2] at hf
    simp only [s4] at hz
    simp only [bind_app, h0, he, hp, hf, ha, hg, hz]
    all_goals rfl
  · exact (erase_security_query s4).trans (f3.trans (f2.trans (f1.trans f0)))
#print axioms count_pmu_events_query
end NativeTagCheck.Hooks

-- Source proof structure: ICNTRParts.lean
-- GENERATED by gen/gen_icntr_parts.py from actual IncrementInstructionCounter.
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
namespace NativeTagCheck.Hooks.ICNTRParts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.ICNTRParts.body"
  (← IO.getStderr).flush

def body (increment_name : Int) : SailM Unit := do
  let w__1 ← (( do readReg PMICNTR_EL0 ) : SailM (BitVec 64) )
  let old_value : Int := (BitVec.toNat w__1)
  let new_value : Int := (old_value +i increment_name)
  writeReg PMICNTR_EL0 (Mk_PMICNTR_EL0_Type (integer_subrange new_value 63 0))
  if (((BitVec.setWidth 1 (BitVec.join1 [(integer_access old_value 64)])) != (BitVec.setWidth 1 (BitVec.join1 [(integer_access
           new_value 64)]))) : Bool)
  then
    (do
      let w__2 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
      writeReg PMOVSSET_EL0 (Sail.BitVec.updateSubrange w__2 32 32 1#1)
      let w__3 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
      writeReg PMOVSCLR_EL0 (Sail.BitVec.updateSubrange w__3 32 32 1#1))
  else (pure (()))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.ICNTRParts.equation"
  (← IO.getStderr).flush

theorem equation (inc : Int) (s : NativeState) :
    (IncrementInstructionCounter inc : SailM Unit) s =
      (do let counted ← CountPMUEvents INSTRUCTION_COUNTER_ID
          if counted then body inc else pure () : SailM Unit) s := by
  simp only [IncrementInstructionCounter, body, bind_assoc, pure_bind]
  all_goals rfl
#print axioms equation
end NativeTagCheck.Hooks.ICNTRParts

-- Source proof structure: ICNTRBody.lean
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
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.ICNTRBody.icntr_body_success"
  (← IO.getStderr).flush

theorem icntr_body_success (inc : Int) (s : NativeState) :
    ∃ t, ICNTRParts.body inc s = .ok () t := by
  simp only [ICNTRParts.body, bind_app, read_apply, write_apply]
  split
  · simp only [bind_app, read_apply, write_apply]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
#print axioms icntr_body_success
end NativeTagCheck.Hooks

-- Source proof structure: PMUWriteFrame.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeTagCheck.HookWrites
open ArmBridge.Draft ArmBridge.CruxCore
open ArmCert.HookQuiet.V0 (HookQuiet hookQuiet_of_E20Frame)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! GENERATED from the selected E20 erasure schema. These are actual primitive
register writes, not replacements for PMU hook execution. GIC is proved
separately from E20. Literal public heads have no frame/run/future-Q premise. -/

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.e20_bank_BitVec_64_set"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.e20_bank_BitVec_64_set"
  (← IO.getStderr).flush

theorem e20_bank_BitVec_64_set (r : Regs) (key : Bank_BitVec_64) (v : BitVec 64)
    (hk : key = .PMCCNTR_EL0 ∨ key = .PMICNTR_EL0 ∨ key = .PMOVSSET_EL0 ∨ key = .PMOVSCLR_EL0 ∨ key = .BRBTS_EL1) :
    E20Frame r {r with bank_BitVec_64 := r.bank_BitVec_64.set key v} := by
  unfold E20Frame eraseE20
  congr 1
  funext k
  by_cases h : k = key
  · subst k
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [RegMap.set]
  · simp [RegMap.set, h]

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.e20_bank_Int_set"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.e20_bank_Int_set"
  (← IO.getStderr).flush

theorem e20_bank_Int_set (r : Regs) (key : Bank_Int) (v : Int)
    (hk : key = .__clock_divider ∨ key = .__last_cycle_count) :
    E20Frame r {r with bank_Int := r.bank_Int.set key v} := by
  unfold E20Frame eraseE20
  congr 1
  funext k
  by_cases h : k = key
  · subst k
    rcases hk with rfl | rfl <;> simp [RegMap.set]
  · simp [RegMap.set, h]

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.e20_counter_vector_set"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.e20_counter_vector_set"
  (← IO.getStderr).flush

theorem e20_counter_vector_set (r : Regs) (v : Vector (BitVec 64) 32) :
    E20Frame r {r with bank_Vector_BitVec_64_32 := r.bank_Vector_BitVec_64_32.set .PMEVCNTR_EL0 v} := by
  simp only [E20Frame, eraseE20, RegMap.set_set_same]

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.e20_PMUEventAccumulator_set"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.e20_PMUEventAccumulator_set"
  (← IO.getStderr).flush

theorem e20_PMUEventAccumulator_set (r : Regs) (v : Vector Int 31) :
    E20Frame r {r with PMUEventAccumulator := v} := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.e20_PMULastThresholdValue_set"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.e20_PMULastThresholdValue_set"
  (← IO.getStderr).flush

theorem e20_PMULastThresholdValue_set (r : Regs) (v : Vector Bool 31) :
    E20Frame r {r with PMULastThresholdValue := v} := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_post_of_frame"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.write_post_of_frame"
  (← IO.getStderr).flush

private theorem write_post_of_frame {α : Type} (r : RegisterRef Regs α)
    (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : α)
    (hf : E20Frame s.regs (r.set v s.regs))
    (hg : (r.set v s.regs).bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending) :
    (writeReg r v : SailM Unit) s = .ok () {s with regs := r.set v s.regs} ∧
    NativeTagCheck.Hooks.PMUPost budget s {s with regs := r.set v s.regs} ∧
    ({s with regs := r.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  exact ⟨rfl, ⟨hf, hg, rfl, rfl, rfl, rfl, rfl, rfl, hookQuiet_of_E20Frame hf q⟩, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMICNTR_EL0"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.write_PMICNTR_EL0"
  (← IO.getStderr).flush

theorem write_PMICNTR_EL0 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : BitVec 64) :
    (writeReg Register.PMICNTR_EL0 v : SailM Unit) s = .ok () {s with regs := Register.PMICNTR_EL0.set v s.regs} ∧
    NativeTagCheck.Hooks.PMUPost budget s {s with regs := Register.PMICNTR_EL0.set v s.regs} ∧
    ({s with regs := Register.PMICNTR_EL0.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMICNTR_EL0 budget s q v
  · exact e20_bank_BitVec_64_set s.regs .PMICNTR_EL0 v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMCCNTR_EL0"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.write_PMCCNTR_EL0"
  (← IO.getStderr).flush

theorem write_PMCCNTR_EL0 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : BitVec 64) :
    (writeReg Register.PMCCNTR_EL0 v : SailM Unit) s = .ok () {s with regs := Register.PMCCNTR_EL0.set v s.regs} ∧
    NativeTagCheck.Hooks.PMUPost budget s {s with regs := Register.PMCCNTR_EL0.set v s.regs} ∧
    ({s with regs := Register.PMCCNTR_EL0.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMCCNTR_EL0 budget s q v
  · exact e20_bank_BitVec_64_set s.regs .PMCCNTR_EL0 v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMOVSSET_EL0"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.write_PMOVSSET_EL0"
  (← IO.getStderr).flush

theorem write_PMOVSSET_EL0 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : BitVec 64) :
    (writeReg Register.PMOVSSET_EL0 v : SailM Unit) s = .ok () {s with regs := Register.PMOVSSET_EL0.set v s.regs} ∧
    NativeTagCheck.Hooks.PMUPost budget s {s with regs := Register.PMOVSSET_EL0.set v s.regs} ∧
    ({s with regs := Register.PMOVSSET_EL0.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMOVSSET_EL0 budget s q v
  · exact e20_bank_BitVec_64_set s.regs .PMOVSSET_EL0 v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMOVSCLR_EL0"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.write_PMOVSCLR_EL0"
  (← IO.getStderr).flush

theorem write_PMOVSCLR_EL0 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : BitVec 64) :
    (writeReg Register.PMOVSCLR_EL0 v : SailM Unit) s = .ok () {s with regs := Register.PMOVSCLR_EL0.set v s.regs} ∧
    NativeTagCheck.Hooks.PMUPost budget s {s with regs := Register.PMOVSCLR_EL0.set v s.regs} ∧
    ({s with regs := Register.PMOVSCLR_EL0.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMOVSCLR_EL0 budget s q v
  · exact e20_bank_BitVec_64_set s.regs .PMOVSCLR_EL0 v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_BRBTS_EL1"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.write_BRBTS_EL1"
  (← IO.getStderr).flush

theorem write_BRBTS_EL1 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : BitVec 64) :
    (writeReg Register.BRBTS_EL1 v : SailM Unit) s = .ok () {s with regs := Register.BRBTS_EL1.set v s.regs} ∧
    NativeTagCheck.Hooks.PMUPost budget s {s with regs := Register.BRBTS_EL1.set v s.regs} ∧
    ({s with regs := Register.BRBTS_EL1.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.BRBTS_EL1 budget s q v
  · exact e20_bank_BitVec_64_set s.regs .BRBTS_EL1 v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMEVCNTR_EL0"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.write_PMEVCNTR_EL0"
  (← IO.getStderr).flush

theorem write_PMEVCNTR_EL0 (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : Vector (BitVec 64) 32) :
    (writeReg Register.PMEVCNTR_EL0 v : SailM Unit) s = .ok () {s with regs := Register.PMEVCNTR_EL0.set v s.regs} ∧
    NativeTagCheck.Hooks.PMUPost budget s {s with regs := Register.PMEVCNTR_EL0.set v s.regs} ∧
    ({s with regs := Register.PMEVCNTR_EL0.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMEVCNTR_EL0 budget s q v
  · exact e20_counter_vector_set s.regs v
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMUEventAccumulator"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.write_PMUEventAccumulator"
  (← IO.getStderr).flush

theorem write_PMUEventAccumulator (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : Vector Int 31) :
    (writeReg Register.PMUEventAccumulator v : SailM Unit) s = .ok () {s with regs := Register.PMUEventAccumulator.set v s.regs} ∧
    NativeTagCheck.Hooks.PMUPost budget s {s with regs := Register.PMUEventAccumulator.set v s.regs} ∧
    ({s with regs := Register.PMUEventAccumulator.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMUEventAccumulator budget s q v
  · exact e20_PMUEventAccumulator_set s.regs v
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write_PMULastThresholdValue"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.write_PMULastThresholdValue"
  (← IO.getStderr).flush

theorem write_PMULastThresholdValue (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : Vector Bool 31) :
    (writeReg Register.PMULastThresholdValue v : SailM Unit) s = .ok () {s with regs := Register.PMULastThresholdValue.set v s.regs} ∧
    NativeTagCheck.Hooks.PMUPost budget s {s with regs := Register.PMULastThresholdValue.set v s.regs} ∧
    ({s with regs := Register.PMULastThresholdValue.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.PMULastThresholdValue budget s q v
  · exact e20_PMULastThresholdValue_set s.regs v
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write___clock_divider"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.write___clock_divider"
  (← IO.getStderr).flush

theorem write___clock_divider (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : Int) :
    (writeReg Register.__clock_divider v : SailM Unit) s = .ok () {s with regs := Register.__clock_divider.set v s.regs} ∧
    NativeTagCheck.Hooks.PMUPost budget s {s with regs := Register.__clock_divider.set v s.regs} ∧
    ({s with regs := Register.__clock_divider.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.__clock_divider budget s q v
  · exact e20_bank_Int_set s.regs .__clock_divider v (by decide)
  · rfl

run_cmd do
  IO.eprintln "CURRENT_DECL PMUWriteFrame.write___last_cycle_count"
  (← IO.getStderr).flush

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUWriteFrame.write___last_cycle_count"
  (← IO.getStderr).flush

theorem write___last_cycle_count (budget : Nat) (s : NativeState) (q : HookQuiet budget s) (v : Int) :
    (writeReg Register.__last_cycle_count v : SailM Unit) s = .ok () {s with regs := Register.__last_cycle_count.set v s.regs} ∧
    NativeTagCheck.Hooks.PMUPost budget s {s with regs := Register.__last_cycle_count.set v s.regs} ∧
    ({s with regs := Register.__last_cycle_count.set v s.regs} : NativeState).choiceOcc = s.choiceOcc := by
  apply write_post_of_frame Register.__last_cycle_count budget s q v
  · exact e20_bank_Int_set s.regs .__last_cycle_count v (by decide)
  · rfl

#print axioms e20_bank_BitVec_64_set
#print axioms e20_bank_Int_set
#print axioms e20_counter_vector_set
#print axioms e20_PMUEventAccumulator_set
#print axioms e20_PMULastThresholdValue_set
#print axioms write_post_of_frame
#print axioms write_PMICNTR_EL0
#print axioms write_PMCCNTR_EL0
#print axioms write_PMOVSSET_EL0
#print axioms write_PMOVSCLR_EL0
#print axioms write_BRBTS_EL1
#print axioms write_PMEVCNTR_EL0
#print axioms write_PMUEventAccumulator
#print axioms write_PMULastThresholdValue
#print axioms write___clock_divider
#print axioms write___last_cycle_count
end NativeTagCheck.HookWrites

-- Source proof structure: ICNTRRun.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
open NativeTagCheck.HookWrites
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.ICNTRRun.PMUPost.refl"
  (← IO.getStderr).flush

theorem PMUPost.refl (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) : PMUPost budget s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, q⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.ICNTRRun.PMUPost.trans"
  (← IO.getStderr).flush

theorem PMUPost.trans {budget : Nat} {s t u : NativeState}
    (a : PMUPost budget s t) (b : PMUPost budget t u) : PMUPost budget s u :=
  ⟨b.frame.trans a.frame, b.gic.trans a.gic, b.mem.trans a.mem, b.events.trans a.events,
    b.choiceState.trans a.choiceState, b.tags.trans a.tags, b.cycleCount.trans a.cycleCount,
    b.sailOutput.trans a.sailOutput, b.quiet⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.ICNTRRun.icntr_body_total"
  (← IO.getStderr).flush

theorem icntr_body_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (inc : Int) :
    ∃ t, ICNTRParts.body inc s = .ok () t ∧ PMUPost budget s t := by
  let old_value : Int := (s.regs.bank_BitVec_64 .PMICNTR_EL0).toNat
  let new_value : Int := old_value + inc
  let value := Mk_PMICNTR_EL0_Type (integer_subrange new_value 63 0)
  let s1 : NativeState := {s with regs := PMICNTR_EL0.set value s.regs}
  have f1 := (write_PMICNTR_EL0 budget s q value).2.1
  let ovset := Sail.BitVec.updateSubrange (s1.regs.bank_BitVec_64 .PMOVSSET_EL0) 32 32 1#1
  let s2 : NativeState := {s1 with regs := PMOVSSET_EL0.set ovset s1.regs}
  have f2 := (write_PMOVSSET_EL0 budget s1 f1.quiet ovset).2.1
  let ovclr := Sail.BitVec.updateSubrange (s2.regs.bank_BitVec_64 .PMOVSCLR_EL0) 32 32 1#1
  let s3 : NativeState := {s2 with regs := PMOVSCLR_EL0.set ovclr s2.regs}
  have f3 := (write_PMOVSCLR_EL0 budget s2 f2.quiet ovclr).2.1
  simp only [ICNTRParts.body, bind_app, read_apply, write_apply]
  split
  · refine ⟨s3, ?_, (f1.trans f2).trans f3⟩
    simp only [bind_app, read_apply, write_apply]
    rfl
  · exact ⟨s1, rfl, f1⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.ICNTRRun.instruction_counter_total"
  (← IO.getStderr).flush

theorem instruction_counter_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (inc : Int)
    (hi : featureValue s .FEAT_PMUv3_ICNTR = true) :
    ∃ t, (IncrementInstructionCounter inc : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  have hv : CountIndexValid INSTRUCTION_COUNTER_ID s := Or.inr (Or.inr ⟨rfl, hi⟩)
  obtain ⟨counted, t, ht, hf⟩ := count_pmu_events_query budget s q INSTRUCTION_COUNTER_ID hv
  have fp := PMUPost.of_eraseOcc_eq q hf
  rw [ICNTRParts.equation]
  cases counted with
  | false => exact ⟨t, by simp only [bind_app, ht, Bool.false_eq_true, reduceIte, pure_apply], fp⟩
  | true =>
    obtain ⟨u, hu, fu⟩ := icntr_body_total budget t fp.quiet inc
    exact ⟨u, by simp only [bind_app, ht, reduceIte, hu], fp.trans fu⟩
#print axioms icntr_body_total
#print axioms instruction_counter_total
end NativeTagCheck.Hooks

-- Source proof structure: TimerRun.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerRun.timer_banks_total"
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
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.TimerRun.a64_timers_total"
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

end NativeTagCheck.Hooks

-- Source proof structure: EventCore.lean
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

namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventCore.uint"
  (← IO.getStderr).flush

theorem uint (label : ChoiceLabel) (s : NativeState) :
    ∃ n, (undefined_int_at label () : SailM Int) s = .ok n s := ⟨_, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventCore.eventState"
  (← IO.getStderr).flush

def eventState (s : NativeState) : NativeState :=
  let r : Regs := {s.regs with bank_BitVec_1 := RegMap.set s.regs.bank_BitVec_1 .EventRegister 1#1}
  {s with regs := r}

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventCore.set_event_apply"
  (← IO.getStderr).flush

theorem set_event_apply (s : NativeState) :
    (SetEventRegister () : SailM Unit) s = .ok () (eventState s) := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventCore.event_frame"
  (← IO.getStderr).flush

theorem event_frame (s : NativeState) : TimerFrame s (eventState s) := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [E22Frame, eraseE22, eventState, RegMap.set_set_same]
  · constructor <;> exact ⟨rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventCore.event_index_range"
  (← IO.getStderr).flush

theorem event_index_range (i : BitVec 4) (high : Bool) :
    ((0 ≤b ((i.toNat : Int) + (if high then 8 else 0))) &&
      (((i.toNat : Int) + (if high then 8 else 0)) <b 64)) = true := by
  have hi := i.isLt
  cases high <;> simp <;> omega

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventCore.unit_bind"
  (← IO.getStderr).flush

theorem unit_bind (x : SailM Unit) : (x >>= fun _ => (pure () : SailM Unit)) = x := by
  have h : (fun _ : Unit => (pure () : SailM Unit)) = (pure : Unit → SailM Unit) := by
    funext u; cases u; rfl
  rw [h, bind_pure]

#print axioms unit_bind
#print axioms set_event_apply
#print axioms event_frame
#print axioms event_index_range

end NativeTagCheck.Hooks

-- Source proof structure: PMUEventParts.lean
-- GENERATED by gen/gen_pmu_event_parts.py from actual PMUEvent__1.
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
namespace NativeTagCheck.Hooks.PMUEventParts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventParts.counter"
  (← IO.getStderr).flush

def counter (pmuevent : BitVec 16) (increment_name : Int) : SailM Unit := do
  let counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  if ((counters != 0) : Bool)
  then
    (do
      let loop_idx_lower : Nat := 0
      let loop_idx_upper : Int := (counters -i 1)
      (do
        let mut loop_vars := ()
        for idx in [loop_idx_lower:loop_idx_upper:1]i do
          let () := loop_vars
          loop_vars ← do (PMUEvent__2 pmuevent increment_name idx)
        (pure loop_vars)))
  else (pure (()))
  pure ()

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventParts.instruction"
  (← IO.getStderr).flush

def instruction (pmuevent : BitVec 16) (increment_name : Int) : SailM Unit := do
  let w__7 ← (( do
    (pure ((← do
          if ((← do
               (HaveAArch64 ())) : Bool)
          then
            (do
              (HavePMUv3ICNTR ()))
          else (pure false)) && ((pmuevent == PMU_EVENT_INST_RETIRED) : Bool))) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      (IncrementInstructionCounter increment_name))
  else (pure (()))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventParts.combined"
  (← IO.getStderr).flush

def combined (pmuevent : BitVec 16) (increment_name : Int) : SailM Unit := do
  let w__0 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (SPEEvent pmuevent))
  else (pure (()))
  let w__3 ← (( do
    if ((← do
         let w__1 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
         (pure ((((_get_PMCR_EL0_Type_E w__1) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__2 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_MDCR_EL2_Type_HPME w__2) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then (pure (()))
  else
    (do
      counter pmuevent increment_name
      instruction pmuevent increment_name)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventParts.equation"
  (← IO.getStderr).flush

theorem equation (e : BitVec 16) (inc : Int) (s : NativeState) :
    (PMUEvent__1 e inc : SailM Unit) s = combined e inc s := by
  simp only [PMUEvent__1, combined, counter, instruction, bind_assoc, bind_if, pure_bind, bind_pure, unit_bind]
  all_goals rfl
#print axioms equation
end NativeTagCheck.Hooks.PMUEventParts

-- Source proof structure: PMUEventRun.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
open NativeTagCheck.HookWrites
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventRun.pmu_counter_stage_total"
  (← IO.getStderr).flush

theorem pmu_counter_stage_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (e : BitVec 16) (inc : Int) :
    ∃ t, PMUEventParts.counter e inc s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨acc, hacc⟩ := event_loop_acc e inc (s.regs.bank_Int .NUM_PMU_COUNTERS) s q.a64 q.nrw q.pmuCountUpper
  simp [eventLoop] at hacc
  let t : NativeState := {s with regs := {s.regs with PMUEventAccumulator := acc}}
  have fp : PMUPost budget s t := (write_PMUEventAccumulator budget s q acc).2.1
  by_cases hn : s.regs.bank_Int .NUM_PMU_COUNTERS = 0
  · exact ⟨s, by simp [PMUEventParts.counter, bind_app, get_num_counters, hn, pure_apply], PMUPost.refl budget s q⟩
  · refine ⟨t, ?_, fp⟩
    simp [PMUEventParts.counter, bind_app, get_num_counters, hn, hacc, pure_apply, unit_bind, map_apply]
    all_goals rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventRun.pmu_instruction_stage_total"
  (← IO.getStderr).flush

theorem pmu_instruction_stage_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (e : BitVec 16) (inc : Int) :
    ∃ t, PMUEventParts.instruction e inc s = .ok () t ∧ PMUPost budget s t := by
  have hA := have_a64 s q.a64
  cases hi : featureValue s .FEAT_PMUv3_ICNTR with
  | false =>
    exact ⟨s, by simp [PMUEventParts.instruction, bind_app, hA, HavePMUv3ICNTR, feature_apply, hi, pure_apply, map_apply], PMUPost.refl budget s q⟩
  | true =>
    by_cases he : e = PMU_EVENT_INST_RETIRED
    · obtain ⟨t, ht, ft⟩ := instruction_counter_total budget s q inc hi
      exact ⟨t, by simp [PMUEventParts.instruction, bind_app, hA, HavePMUv3ICNTR, feature_apply, hi, he, ht, pure_apply, map_apply], ft⟩
    · exact ⟨s, by simp [PMUEventParts.instruction, bind_app, hA, HavePMUv3ICNTR, feature_apply, hi, he, pure_apply, map_apply], PMUPost.refl budget s q⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventRun.pmu_event1_total"
  (← IO.getStderr).flush

theorem pmu_event1_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (e : BitVec 16) (inc : Int) :
    ∃ t, (PMUEvent__1 e inc : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨t, hc, fc⟩ := pmu_counter_stage_total budget s q e inc
  obtain ⟨u, hi, fi⟩ := pmu_instruction_stage_total budget t fc.quiet e inc
  rw [PMUEventParts.equation]
  rcases bit_cases (_get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0)) with hE | hE
  · rcases bit_cases (_get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2)) with hH | hH
    · refine ⟨s, ?_, PMUPost.refl budget s q⟩
      simp [PMUEventParts.combined, bind_app, read_spe, q.spe, read_pmcr, read_mdcr, hE, hH, pure_apply, map_apply]
    · refine ⟨u, ?_, fc.trans fi⟩
      simp [PMUEventParts.combined, bind_app, read_spe, q.spe, read_pmcr, read_mdcr, hE, hH, hc, hi, pure_apply, map_apply]
  · refine ⟨u, ?_, fc.trans fi⟩
    simp [PMUEventParts.combined, bind_app, read_spe, q.spe, read_pmcr, read_mdcr, hE, hc, hi, pure_apply, map_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventRun.pmu_event_total"
  (← IO.getStderr).flush

theorem pmu_event_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (e : BitVec 16) :
    ∃ t, (PMUEvent e : SailM Unit) s = .ok () t ∧ PMUPost budget s t :=
  pmu_event1_total budget s q e 1

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUEventRun.pmu_retired_total"
  (← IO.getStderr).flush

theorem pmu_retired_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (PMUEvent PMU_EVENT_INST_RETIRED : SailM Unit) s = .ok () t ∧ PMUPost budget s t :=
  pmu_event_total budget s q PMU_EVENT_INST_RETIRED
#print axioms pmu_counter_stage_total
#print axioms pmu_instruction_stage_total
#print axioms pmu_event1_total
#print axioms pmu_event_total
#print axioms pmu_retired_total
end NativeTagCheck.Hooks

-- Source proof structure: EventParts.lean
-- GENERATED by gen/gen_event_parts.py from actual TestEventCNTP/V.
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
namespace NativeTagCheck.Hooks.EventParts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventParts.prepareP"
  (← IO.getStderr).flush

def prepareP : SailM (Option (Int × (BitVec 64))) := do
  let n ← (( do (undefined_int_at (.site 1179) ()) ) : SailM Int )
  let offset ← (( do (undefined_bitvector_at (.site 1180) 64) ) : SailM (BitVec 64) )
  let previousbit ← (( do (undefined_bitvector_at (.site 1181) 1) ) : SailM (BitVec 1) )
  let samplebit ← (( do (undefined_bitvector_at (.site 1182) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  if (((_get_CNTHCTL_EL2_Type_EVNTEN w__0) == 1#1) : Bool) then do
    let w__1 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
    let n : Int := ((BitVec.toNat (_get_CNTHCTL_EL2_Type_EVNTI w__1)) : Int)
    let w__4 ← (( do
      if ((← do
           (HaveECVExt ())) : Bool)
      then
        (do
          let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
          (pure ((((_get_CNTHCTL_EL2_Type_EVNTIS w__3) == 1#1) : Bool))))
      else (pure false) ) : SailM Bool )
    let n : Int :=
      if (w__4 : Bool)
      then (n +i 8)
      else n
    let n : Int := n
    let ecv : Bool := false
    let w__5 ← (( do (HaveECVExt ()) ) : SailM Bool )
    let offset ← (( do
      if (w__5 : Bool)
      then
        (do
          let ecv ← (( do
            if ((← do
                 if ((← do
                      (EL2Enabled ())) : Bool)
                 then
                   (do
                     let w__7 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                     (pure ((((_get_CNTHCTL_EL2_Type_ECV w__7) == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__9 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure ((((_get_SCR_EL3_Type_ECVEn w__9) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (ecv : Bool)
          then
            (do
              readReg CNTPOFF_EL2)
          else (pure ((Zeros (n := 64)))))
      else (pure (offset)) ) : SailM (BitVec 64) )
    pure (some (n, offset))
  else pure none

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventParts.edgeP"
  (← IO.getStderr).flush

def edgeP (prev_physical_count current_physical_count : BitVec 64)
    (n : Int) (offset : BitVec 64) : SailM Unit := do
  ArmFull.assert ((0 ≤b n) && (n <b 64)) "sail-arm/v8_base.sail:18360.46-18360.47"
  let samplebit : (BitVec 1) :=
    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (current_physical_count - offset)
        (Sail.Int.toNatChecked (n)))]))
  let previousbit : (BitVec 1) :=
    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (prev_physical_count - offset)
        (Sail.Int.toNatChecked (n)))]))
  let w__12 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  if (((_get_CNTHCTL_EL2_Type_EVNTDIR w__12) == 0#1) : Bool)
  then
    (do
      if (((previousbit == 0#1) && (samplebit == 1#1)) : Bool)
      then
        (do
          (SetEventRegister ()))
      else (pure (())))
  else
    (do
      if (((previousbit == 1#1) && (samplebit == 0#1)) : Bool)
      then
        (do
          (SetEventRegister ()))
      else (pure (())))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventParts.equationP"
  (← IO.getStderr).flush

theorem equationP (prev current : BitVec 64) (s : NativeState) :
    (TestEventCNTP prev current : SailM Unit) s =
      (do let p ← prepareP
          match p with
          | none => pure ()
          | some (n, offset) => edgeP prev current n offset : SailM Unit) s := by
  simp only [TestEventCNTP, prepareP, edgeP, bind_assoc, bind_if, pure_bind, unit_bind]
#print axioms equationP

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventParts.prepareV"
  (← IO.getStderr).flush

def prepareV : SailM (Option (Int × (BitVec 64))) := do
  let n ← (( do (undefined_int_at (.site 1184) ()) ) : SailM Int )
  let offset ← (( do (undefined_bitvector_at (.site 1185) 64) ) : SailM (BitVec 64) )
  let previousbit ← (( do (undefined_bitvector_at (.site 1186) 1) ) : SailM (BitVec 1) )
  let samplebit ← (( do (undefined_bitvector_at (.site 1187) 1) ) : SailM (BitVec 1) )
  let w__5 ← (( do
    if ((← do
         let w__3 ← (( do
           if ((← do
                (HaveVirtHostExt ())) : Bool)
           then
             (do
               let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               (pure (((((_get_HCR_EL2_Type_E2H w__1) +++ (_get_HCR_EL2_Type_TGE w__2)) == 0b11#2) : Bool))))
           else (pure false) ) : SailM Bool )
         (pure (((! w__3) : Bool)))) : Bool)
    then
      (do
        let w__4 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTKCTL_EL1_Type_EVNTEN w__4) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__5 : Bool) then do
    let w__6 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
    let n : Int := ((BitVec.toNat (_get_CNTKCTL_EL1_Type_EVNTI w__6)) : Int)
    let w__9 ← (( do
      if ((← do
           (HaveECVExt ())) : Bool)
      then
        (do
          let w__8 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
          (pure ((((_get_CNTKCTL_EL1_Type_EVNTIS w__8) == 1#1) : Bool))))
      else (pure false) ) : SailM Bool )
    let n : Int :=
      if (w__9 : Bool)
      then (n +i 8)
      else n
    let n : Int := n
    let w__14 ← (( do
      if (((HaveEL EL2) : Bool) : Bool)
      then
        (do
          if ((← do
               let w__10 ← (( do (EL2Enabled ()) ) : SailM Bool )
               (pure (((! w__10) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__12 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              (pure (((((_get_HCR_EL2_Type_E2H w__11) +++ (_get_HCR_EL2_Type_TGE w__12)) != 0b11#2) : Bool)))))
      else (pure false) ) : SailM Bool )
    let offset ← (( do
      if (w__14 : Bool)
      then
        (do
          readReg CNTVOFF_EL2)
      else
        (let offset : (BitVec 64) := (Zeros (n := 64))
        (pure (offset))) ) : SailM (BitVec 64) )
    pure (some (n, offset))
  else pure none

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventParts.edgeV"
  (← IO.getStderr).flush

def edgeV (prev_physical_count current_physical_count : BitVec 64)
    (n : Int) (offset : BitVec 64) : SailM Unit := do
  ArmFull.assert ((0 ≤b n) && (n <b 64)) "sail-arm/v8_base.sail:18411.46-18411.47"
  let samplebit : (BitVec 1) :=
    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (current_physical_count - offset)
        (Sail.Int.toNatChecked (n)))]))
  let previousbit : (BitVec 1) :=
    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (prev_physical_count - offset)
        (Sail.Int.toNatChecked (n)))]))
  let w__16 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  if (((_get_CNTKCTL_EL1_Type_EVNTDIR w__16) == 0#1) : Bool)
  then
    (do
      if (((previousbit == 0#1) && (samplebit == 1#1)) : Bool)
      then
        (do
          (SetEventRegister ()))
      else (pure (())))
  else
    (do
      if (((previousbit == 1#1) && (samplebit == 0#1)) : Bool)
      then
        (do
          (SetEventRegister ()))
      else (pure (())))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventParts.equationV"
  (← IO.getStderr).flush

theorem equationV (prev current : BitVec 64) (s : NativeState) :
    (TestEventCNTV prev current : SailM Unit) s =
      (do let p ← prepareV
          match p with
          | none => pure ()
          | some (n, offset) => edgeV prev current n offset : SailM Unit) s := by
  simp only [TestEventCNTV, prepareV, edgeV, bind_assoc, bind_if, pure_bind, unit_bind]
#print axioms equationV

end NativeTagCheck.Hooks.EventParts

-- Source proof structure: EventPrepare.lean
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
set_option linter.unusedSimpArgs false
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.EventRange"
  (← IO.getStderr).flush

def EventRange (p : Option (Int × (BitVec 64))) : Prop :=
  match p with
  | none => True
  | some (n, _) => ((0 ≤b n) && (n <b 64)) = true

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.eventIndex"
  (← IO.getStderr).flush

def eventIndex (i : BitVec 4) (high : Bool) : Int :=
  if high then (i.toNat : Int)+8 else (i.toNat : Int)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.event_range_index"
  (← IO.getStderr).flush

theorem event_range_index (i : BitVec 4) (high : Bool) (offset : BitVec 64) :
    EventRange (some (eventIndex i high, offset)) := by
  have h := event_index_range i high
  cases high <;> simpa only [EventRange, eventIndex, Bool.false_eq_true, reduceIte, Int.add_zero] using h

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.eventPEnabled"
  (← IO.getStderr).flush

def eventPEnabled (s : NativeState) : Bool :=
  _get_CNTHCTL_EL2_Type_EVNTEN (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.eventPState"
  (← IO.getStderr).flush

def eventPState (s : NativeState) : NativeState :=
  if eventPEnabled s && featureValue s .FEAT_ECV then el2QueryState s else s

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.eventPValue"
  (← IO.getStderr).flush

def eventPValue (s : NativeState) : Option (Int × (BitVec 64)) :=
  if eventPEnabled s then
    let n := eventIndex (_get_CNTHCTL_EL2_Type_EVNTI (s.regs.bank_BitVec_64 .CNTHCTL_EL2))
      (featureValue s .FEAT_ECV && (_get_CNTHCTL_EL2_Type_EVNTIS (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1))
    let offset := if featureValue s .FEAT_ECV then
      if ArmCert.HookQuiet.V0.el2Enabled s.regs &&
        (_get_CNTHCTL_EL2_Type_ECV (s.regs.bank_BitVec_64 .CNTHCTL_EL2) == 1#1) &&
        (_get_SCR_EL3_Type_ECVEn (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1)
      then s.regs.bank_BitVec_64 .CNTPOFF_EL2 else 0#64
    else oracleChoiceSource.chooseAt (.bitvector 64) (.site 1180) s.choiceState
    some (n, offset)
  else none

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.event_prepare_p_eq"
  (← IO.getStderr).flush

theorem event_prepare_p_eq (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    EventParts.prepareP s = .ok (eventPValue s) (eventPState s) := by
  rcases uint (.site 1179) s with ⟨n, hn⟩
  have hel := el2_enabled s ha
  cases hF : featureValue s .FEAT_ECV <;>
    rcases bit_cases (_get_CNTHCTL_EL2_Type_EVNTEN (s.regs.bank_BitVec_64 .CNTHCTL_EL2)) with hEN | hEN <;>
    rcases bit_cases (_get_CNTHCTL_EL2_Type_EVNTIS (s.regs.bank_BitVec_64 .CNTHCTL_EL2)) with hIS | hIS <;>
    cases hEL : ArmCert.HookQuiet.V0.el2Enabled s.regs <;>
    rcases bit_cases (_get_CNTHCTL_EL2_Type_ECV (s.regs.bank_BitVec_64 .CNTHCTL_EL2)) with hC | hC <;>
    rcases bit_cases (_get_SCR_EL3_Type_ECVEn (s.regs.bank_BitVec_64 .SCR_EL3)) with hS | hS <;>
    simp [EventParts.prepareP, bind_app, pure_apply, map_apply, hn, ubv,
      read_apply, HaveECVExt, feature_apply, hF, hEN, hIS, hEL, hC, hS,
      hel, el2_query_regs, eventPValue, eventPState, eventPEnabled, eventIndex, Zeros]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.event_p_range"
  (← IO.getStderr).flush

theorem event_p_range (s : NativeState) : EventRange (eventPValue s) := by
  unfold eventPValue
  by_cases he : eventPEnabled s = true
  · rw [if_pos he]
    exact event_range_index _ _ _
  · rw [if_neg he]
    trivial

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.event_p_frame"
  (← IO.getStderr).flush

theorem event_p_frame (s : NativeState) : TimerFrame s (eventPState s) := by
  unfold eventPState
  split
  · exact TimerFrame.of_eraseOcc_eq (erase_el2_query s)
  · exact TimerFrame.refl s

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.event_prepare_p"
  (← IO.getStderr).flush

theorem event_prepare_p (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    ∃ p t, EventParts.prepareP s = .ok p t ∧ TimerFrame s t ∧ EventRange p :=
  ⟨eventPValue s, eventPState s, event_prepare_p_eq s ha, event_p_frame s, event_p_range s⟩
#print axioms event_prepare_p

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.eventVHost"
  (← IO.getStderr).flush

def eventVHost (s : NativeState) : Bool :=
  ((_get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2)) +++
    (_get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2))) == 3#2

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.eventVEnabled"
  (← IO.getStderr).flush

def eventVEnabled (s : NativeState) : Bool :=
  !(featureValue s .FEAT_VHE && eventVHost s) &&
    (_get_CNTKCTL_EL1_Type_EVNTEN (s.regs.bank_BitVec_64 .CNTKCTL_EL1) == 1#1)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.eventVState"
  (← IO.getStderr).flush

def eventVState (s : NativeState) : NativeState :=
  if eventVEnabled s then el2QueryState s else s

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.eventVValue"
  (← IO.getStderr).flush

def eventVValue (s : NativeState) : Option (Int × (BitVec 64)) :=
  if eventVEnabled s then
    let n := eventIndex (_get_CNTKCTL_EL1_Type_EVNTI (s.regs.bank_BitVec_64 .CNTKCTL_EL1))
      (featureValue s .FEAT_ECV && (_get_CNTKCTL_EL1_Type_EVNTIS (s.regs.bank_BitVec_64 .CNTKCTL_EL1) == 1#1))
    let offset := if !(ArmCert.HookQuiet.V0.el2Enabled s.regs) || !(eventVHost s)
      then s.regs.bank_BitVec_64 .CNTVOFF_EL2 else 0#64
    some (n, offset)
  else none

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.event_prepare_v_eq"
  (← IO.getStderr).flush

theorem event_prepare_v_eq (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    EventParts.prepareV s = .ok (eventVValue s) (eventVState s) := by
  rcases uint (.site 1184) s with ⟨n, hn⟩
  have hel := el2_enabled s ha
  cases hF : featureValue s .FEAT_ECV <;>
    cases hVH : featureValue s .FEAT_VHE <;>
    by_cases hHost : ((_get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2)) +++
      (_get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2))) = 3#2 <;>
    rcases bit_cases (_get_CNTKCTL_EL1_Type_EVNTEN (s.regs.bank_BitVec_64 .CNTKCTL_EL1)) with hEN | hEN <;>
    rcases bit_cases (_get_CNTKCTL_EL1_Type_EVNTIS (s.regs.bank_BitVec_64 .CNTKCTL_EL1)) with hIS | hIS <;>
    cases hEL : ArmCert.HookQuiet.V0.el2Enabled s.regs <;>
    simp [EventParts.prepareV, bind_app, pure_apply, map_apply, hn, ubv,
      read_apply, HaveECVExt, HaveVirtHostExt, HaveEL, feature_apply, hF, hVH, hHost, hEN, hIS, hEL,
      hel, el2_query_regs, eventVValue, eventVState, eventVEnabled, eventVHost, eventIndex, Zeros]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.event_v_range"
  (← IO.getStderr).flush

theorem event_v_range (s : NativeState) : EventRange (eventVValue s) := by
  unfold eventVValue
  by_cases he : eventVEnabled s = true
  · rw [if_pos he]
    exact event_range_index _ _ _
  · rw [if_neg he]
    trivial

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.event_v_frame"
  (← IO.getStderr).flush

theorem event_v_frame (s : NativeState) : TimerFrame s (eventVState s) := by
  unfold eventVState
  split
  · exact TimerFrame.of_eraseOcc_eq (erase_el2_query s)
  · exact TimerFrame.refl s

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventPrepare.event_prepare_v"
  (← IO.getStderr).flush

theorem event_prepare_v (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    ∃ p t, EventParts.prepareV s = .ok p t ∧ TimerFrame s t ∧ EventRange p :=
  ⟨eventVValue s, eventVState s, event_prepare_v_eq s ha, event_v_frame s, event_v_range s⟩

#print axioms event_prepare_v
end NativeTagCheck.Hooks

-- Source proof structure: EventEdges.lean
-- GENERATED by gen/gen_event_edges.py; one common proof template, two source-bound bodies.
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
namespace NativeTagCheck.Hooks.EventEdges

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventEdges.totalP"
  (← IO.getStderr).flush

theorem totalP (s : NativeState) (prev current : BitVec 64) (n : Int) (offset : BitVec 64)
    (hr : ((0 ≤b n) && (n <b 64)) = true) :
    ∃ t, EventParts.edgeP prev current n offset s = .ok () t ∧ TimerFrame s t := by
  simp only [EventParts.edgeP, bind_app, hr, assert_true, read_apply]
  repeat' first
    | split
    | exact ⟨_, rfl, TimerFrame.refl _⟩
    | exact ⟨_, set_event_apply _, event_frame _⟩
#print axioms totalP

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventEdges.totalV"
  (← IO.getStderr).flush

theorem totalV (s : NativeState) (prev current : BitVec 64) (n : Int) (offset : BitVec 64)
    (hr : ((0 ≤b n) && (n <b 64)) = true) :
    ∃ t, EventParts.edgeV prev current n offset s = .ok () t ∧ TimerFrame s t := by
  simp only [EventParts.edgeV, bind_app, hr, assert_true, read_apply]
  repeat' first
    | split
    | exact ⟨_, rfl, TimerFrame.refl _⟩
    | exact ⟨_, set_event_apply _, event_frame _⟩
#print axioms totalV
end NativeTagCheck.Hooks.EventEdges

-- Source proof structure: EventRun.lean
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
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventRun.event_p_total"
  (← IO.getStderr).flush

theorem event_p_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (prev current : BitVec 64) :
    ∃ t, (TestEventCNTP prev current : SailM Unit) s = .ok () t ∧
      TimerFrame s t ∧ ArmCert.HookQuiet.V0.HookQuiet budget t := by
  obtain ⟨p, s1, hp, fp, hr⟩ := event_prepare_p s q.a64
  rw [EventParts.equationP]
  cases p with
  | none =>
    exact ⟨s1, by simp only [bind_app, hp, pure_apply], fp, fp.quiet q⟩
  | some p =>
    obtain ⟨t, he, fe⟩ := EventEdges.totalP s1 prev current p.1 p.2 hr
    exact ⟨t, by simp only [bind_app, hp, he], fp.trans fe, (fp.trans fe).quiet q⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.EventRun.event_v_total"
  (← IO.getStderr).flush

theorem event_v_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (prev current : BitVec 64) :
    ∃ t, (TestEventCNTV prev current : SailM Unit) s = .ok () t ∧
      TimerFrame s t ∧ ArmCert.HookQuiet.V0.HookQuiet budget t := by
  obtain ⟨p, s1, hp, fp, hr⟩ := event_prepare_v s q.a64
  rw [EventParts.equationV]
  cases p with
  | none =>
    exact ⟨s1, by simp only [bind_app, hp, pure_apply], fp, fp.quiet q⟩
  | some p =>
    obtain ⟨t, he, fe⟩ := EventEdges.totalV s1 prev current p.1 p.2 hr
    exact ⟨t, by simp only [bind_app, hp, he], fp.trans fe, (fp.trans fe).quiet q⟩
#print axioms event_p_total
#print axioms event_v_total
end NativeTagCheck.Hooks

-- Source proof structure: CounterRun.lean
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
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterRun.counter_tail_total"
  (← IO.getStderr).flush

theorem counter_tail_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (prior : BitVec 64) :
    ∃ t, afterIncrement prior s = .ok () t ∧ TimerFrame s t ∧
      ArmCert.HookQuiet.V0.HookQuiet budget t := by
  obtain ⟨s1, ht, ft, q1⟩ := a64_timers_total budget s q
  obtain ⟨s2, hp, fp, q2⟩ := event_p_total budget s1 q1 prior (physicalValue s1)
  obtain ⟨s3, hv, fv, q3⟩ := event_v_total budget s2 q2 prior (physicalValue s2)
  refine ⟨s3, ?_, (ft.trans fp).trans fv, q3⟩
  simp only [afterIncrement, bind_app, have_a64 s q.a64, Bool.not_true,
    Bool.false_eq_true, reduceIte, ht, physical_count_apply, hp, hv]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterRun.CounterPost"
  (← IO.getStderr).flush

structure CounterPost (budget : Nat) (s t : NativeState) : Prop where
  frame : E22Frame s.regs t.regs
  bits : ArmCert.HookQuiet.V0.TimerLowBitsEq s.regs t.regs
  gic : t.regs.bank_Option_InterruptID .__GIC_Pending = s.regs.bank_Option_InterruptID .__GIC_Pending
  mem : t.mem = s.mem
  events : t.events = s.events
  choiceState : choiceView t = choiceView s
  tags : t.tags = s.tags
  cycleCount : t.cycleCount = s.cycleCount
  sailOutput : t.sailOutput = s.sailOutput
  quiet : ArmCert.HookQuiet.V0.HookQuiet budget t

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterRun.CounterPost.of_timer"
  (← IO.getStderr).flush

theorem CounterPost.of_timer {budget : Nat} {s t : NativeState}
    (f : TimerFrame s t) (q : ArmCert.HookQuiet.V0.HookQuiet budget t) :
    CounterPost budget s t :=
  ⟨f.frame, f.bits, f.gic, f.mem, f.events, f.choiceState, f.tags, f.cycleCount, f.sailOutput, q⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterRun.counter_tick_total"
  (← IO.getStderr).flush

theorem counter_tick_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet (budget+1) s) :
    ∃ t, (GenericCounterTick () : SailM Unit) s = .ok () t ∧ CounterPost budget s t := by
  rw [counter_prefix_quiet budget s q]
  split
  · have q0 := ArmCert.HookQuiet.V0.hookQuiet_mono (Nat.le_succ budget) q
    obtain ⟨t, ht, ft, qt⟩ := a64_timers_total budget s q0
    exact ⟨t, ht, CounterPost.of_timer ft qt⟩
  · obtain ⟨t, ht, ft, qt⟩ := counter_tail_total budget (advanceCount s)
      (advance_quiet budget s q) (physicalValue s)
    refine ⟨t, ht, ?_⟩
    have hb : ArmCert.HookQuiet.V0.TimerLowBitsEq s.regs (advanceCount s).regs := by
      constructor <;> exact ⟨rfl, rfl⟩
    exact ⟨ft.frame.trans (by first | rfl | simp), lowbits_trans hb ft.bits, ft.gic, ft.mem, ft.events,
      ft.choiceState, ft.tags, ft.cycleCount, ft.sailOutput, qt⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CounterRun.system_counter_total"
  (← IO.getStderr).flush

theorem system_counter_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet (budget+1) s) :
    ∃ t, (__UpdateSystemCounter () : SailM Unit) s = .ok () t ∧ CounterPost budget s t := by
  exact counter_tick_total budget s q
#print axioms counter_tail_total
#print axioms counter_tick_total
#print axioms system_counter_total
end NativeTagCheck.Hooks

-- Source proof structure: PMUChoices.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUChoices.undefined_constraint_total"
  (← IO.getStderr).flush

theorem undefined_constraint_total (label : ChoiceLabel) (s : NativeState) :
    ∃ c, (undefined_Constraint label () : SailM Constraint) s = .ok c s := ⟨_, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUChoices.constrain_restc_total"
  (← IO.getStderr).flush

theorem constrain_restc_total (s : NativeState) :
    ∃ (c : Constraint) (bits : BitVec 2),
      (ConstrainUnpredictableBits .Unpredictable_RESTC 2 : SailM (Constraint × (BitVec 2))) s =
        .ok (c, bits) (afterOcc 543 (afterOcc 542 s)) := ⟨_, _, rfl⟩
#print axioms undefined_constraint_total
#print axioms constrain_restc_total
end NativeTagCheck.Hooks

-- Source proof structure: PMUValueParts.lean
-- GENERATED by gen/gen_pmu_value_parts.py from actual PMUCountValue.
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmFull.Constraint ArmFull.Unpredictable
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks.PMUValueParts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUValueParts.prepare"
  (← IO.getStderr).flush

def prepare (n : Nat) (Vb : Int) : SailM (Option (Int × Bool)) := do
  let Vp ← (( do (undefined_bool_at (← occLabel 545) ()) ) : SailM Bool )
  let tc ← (( do (undefined_bitvector_at (← occLabel 546) 2) ) : SailM (BitVec 2) )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HavePMUv3TH ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if w__2 then pure none else do
    let w__3 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
    let T : Int := (BitVec.toNat (_get_PMEVTYPER_EL0_Type_TH (GetElem?.getElem! w__3 n)))
    let Vc ← (( do (undefined_bool_at (← occLabel 547) ()) ) : SailM Bool )
    let w__4 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
    let Vc : Bool :=
      match (BitVec.setWidth 2 (Sail.BitVec.extractLsb
        (_get_PMEVTYPER_EL0_Type_TC (GetElem?.getElem! w__4 n)) 2 1)) with
      | 0b00 => (Vb != T)
      | 0b01 => (Vb == T)
      | 0b10 => (Vb ≥b T)
      | 0b11 => (Vb <b T)
      | _ => Vc
    let Vt ← (( do (undefined_int_at (← occLabel 548) ()) ) : SailM Int )
    let w__5 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
    let Vt : Int :=
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               (_get_PMEVTYPER_EL0_Type_TC (GetElem?.getElem! w__5 n)) 0)])) == 0#1) : Bool)
      then
        (if (Vc : Bool)
        then Vb
        else 0)
      else
        (if (Vc : Bool)
        then 1
        else 0)
    let Vt : Int := Vt
    let v ← (( do (undefined_int_at (← occLabel 549) ()) ) : SailM Int )
    let w__8 ← (( do
      if ((← do
           (HavePMUv3EDGE ())) : Bool)
      then
        (do
          let w__7 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
          (pure ((((_get_PMEVTYPER_EL0_Type_TE (GetElem?.getElem! w__7 n)) == 1#1) : Bool))))
      else (pure false) ) : SailM Bool )
    let v ← (( do
      if (w__8 : Bool)
      then
        (do
          ArmFull.assert ((0 ≤b n) && (n <b 31)) "sail-arm/v8_base.sail:5457.46-5457.47"
          let w__9 ← (( do readReg PMULastThresholdValue ) : SailM (Vector Bool 31) )
          let Vp : Bool := (GetElem?.getElem! w__9 n)
          let w__10 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
          let tc : (BitVec 2) :=
            ((Sail.BitVec.extractLsb (_get_PMEVTYPER_EL0_Type_TC (GetElem?.getElem! w__10 n)) 1 0) : (BitVec 2))
          let tc ← (( do
            if ((tc == 0b00#2) : Bool)
            then
              (do
                let c ← (( do (undefined_Constraint (← occLabel 550) ()) ) : SailM Constraint
                  )
                let w__11 ← (( do (ConstrainUnpredictableBits Unpredictable_RESTC 2) ) : SailM
                  (Constraint × (BitVec 2)) )
                let (tup__0, tup__1) := (w__11 : (Constraint × (BitVec 2)))
                let c : Constraint := tup__0
                let tc : (BitVec 2) := tup__1
                let tc : (BitVec 2) :=
                  if ((BEq.beq c Constraint_DISABLED) : Bool)
                  then 0b00#2
                  else tc
                (pure (tc)))
            else (pure (tc)) ) : SailM (BitVec 2) )
          let v : Int :=
            match tc with
            | 0b00 => Vt
            | 0b10 =>
              (if ((neq_bool Vp Vc) : Bool)
              then 1
              else 0)
            | b__0 =>
              (if (((! Vp) && Vc) : Bool)
              then 1
              else 0)
          (pure (v)))
      else (pure (Vt)) ) : SailM Int )
    let v : Int := v
    pure (some (v, Vc))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUValueParts.commit"
  (← IO.getStderr).flush

def commit (n : Nat) (Vb : Int) (result : Option (Int × Bool)) : SailM Int := do
  match result with
  | none => pure Vb
  | some (v, Vc) =>
    let w__12 ← (( do readReg PMULastThresholdValue ) : SailM (Vector Bool 31) )
    writeReg PMULastThresholdValue (vectorUpdate w__12 n Vc)
    (pure (v))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUValueParts.equation"
  (← IO.getStderr).flush

theorem equation (n : Nat) (Vb : Int) (s : NativeState) :
    (PMUCountValue n Vb : SailM Int) s =
      (do let result ← prepare n Vb
          commit n Vb result : SailM Int) s := by
  simp only [PMUCountValue, prepare, commit, bind_assoc, bind_if, pure_bind]
  all_goals rfl
#print axioms equation
end NativeTagCheck.Hooks.PMUValueParts

-- Source proof structure: MonadLaws.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace NativeTagCheck.Hooks
/- Normalize the compiler's map optimization using actual EStateM semantics. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.MonadLaws.map_as_bind"
  (← IO.getStderr).flush

theorem map_as_bind {α β : Type} (f : α → β) (x : SailM α) :
    (f <$> x) = (x >>= fun a => pure (f a)) := by
  funext s
  simp only [map_apply, bind_app]
  cases x s <;> rfl
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.MonadLaws.bind_dif"
  (← IO.getStderr).flush

theorem bind_dif {m : Type → Type} [Monad m] {α β : Type}
    (p : Prop) [Decidable p] (x : p → m α) (y : ¬p → m α) (f : α → m β) :
    ((if h : p then x h else y h) >>= f) =
      (if h : p then x h >>= f else y h >>= f) := by
  split <;> rfl
#print axioms bind_dif
#print axioms map_as_bind
end NativeTagCheck.Hooks

-- Source proof structure: QueryM.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.QueryM"
  (← IO.getStderr).flush

def QueryM {α : Type} (x : SailM α) : Prop := ∀ s, QueryResult x s
namespace QueryM

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.bind"
  (← IO.getStderr).flush

theorem bind {α β : Type} {x : SailM α} {f : α → SailM β}
    (hx : QueryM x) (hf : ∀ a, QueryM (f a)) : QueryM (x >>= f) := by
  intro s
  exact query_bind x f s (hx s) (fun a t _ => hf a t)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.ite"
  (← IO.getStderr).flush

theorem ite {α : Type} (p : Prop) [Decidable p] {x y : SailM α}
    (hx : QueryM x) (hy : QueryM y) : QueryM (if p then x else y) := by
  split <;> assumption

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.pure"
  (← IO.getStderr).flush

theorem pure {α : Type} (a : α) : QueryM (Pure.pure a : SailM α) := query_pure a

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.read"
  (← IO.getStderr).flush

theorem read {α : Type} (r : RegisterRef Regs α) : QueryM (readReg r : SailM α) := query_read r

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.occ"
  (← IO.getStderr).flush

theorem occ (site : Nat) (different : site ≠ 1354) : QueryM (occLabel site : SailM ChoiceLabel) := by
  intro s
  exact ⟨_, afterOcc site s, rfl, erase_afterOcc site s different⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.bool"
  (← IO.getStderr).flush

theorem bool (label : ChoiceLabel) : QueryM (undefined_bool_at label () : SailM Bool) := by
  intro s
  exact ⟨_, s, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.bits"
  (← IO.getStderr).flush

theorem bits (label : ChoiceLabel) (n : Nat) : QueryM (undefined_bitvector_at label n : SailM (BitVec n)) := by
  intro s
  exact ⟨_, s, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.int"
  (← IO.getStderr).flush

theorem int (label : ChoiceLabel) : QueryM (undefined_int_at label () : SailM Int) := by
  intro s
  exact ⟨_, s, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.constraint"
  (← IO.getStderr).flush

theorem constraint (label : ChoiceLabel) : QueryM (undefined_Constraint label () : SailM Constraint) := by
  intro s
  obtain ⟨c, hc⟩ := undefined_constraint_total label s
  exact ⟨c, s, hc, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.feature"
  (← IO.getStderr).flush

theorem feature (f : Feature) : QueryM (IsFeatureImplemented f : SailM Bool) := by
  intro s
  exact ⟨featureValue s f, s, feature_apply f s, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.have_a64"
  (← IO.getStderr).flush

theorem have_a64 : QueryM (HaveAArch64 () : SailM Bool) := by
  intro s
  cases h0 : featureValue s .FEAT_AA64EL0 <;>
    cases h1 : featureValue s .FEAT_AA64EL1 <;>
    cases h2 : featureValue s .FEAT_AA64EL2 <;>
    cases h3 : featureValue s .FEAT_AA64EL3 <;>
    simp only [QueryResult, HaveAArch64, pure_apply, map_apply, feature_apply, h0, h1, h2, h3,
      Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte,
      Pure.pure, EStateM.pure, Bind.bind, EStateM.bind] <;>
    exact ⟨_, _, rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.assert"
  (← IO.getStderr).flush

theorem assert {b : Bool} (h : b = true) (msg : String) : QueryM (ArmFull.assert b msg : SailM Unit) := by
  intro s
  exact ⟨(), s, by rw [h]; rfl, rfl⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.QueryM.restc"
  (← IO.getStderr).flush

theorem restc : QueryM (ConstrainUnpredictableBits .Unpredictable_RESTC 2 : SailM (Constraint × (BitVec 2))) := by
  intro s
  obtain ⟨c, v, hc⟩ := constrain_restc_total s
  exact ⟨(c, v), _, hc, by simp⟩
end QueryM
#print axioms QueryM.bind
#print axioms QueryM.have_a64
#print axioms QueryM.restc
end NativeTagCheck.Hooks

-- Source proof structure: PMUValuePrepare.lean
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
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUValuePrepare.pmu_value_prepare_query"
  (← IO.getStderr).flush

theorem pmu_value_prepare_query (n : Nat) (Vb : Int) (hn : n < 31) :
    QueryM (PMUValueParts.prepare n Vb) := by
  simp only [PMUValueParts.prepare, HavePMUv3TH, HavePMUv3EDGE,
    map_as_bind, bind_assoc, pure_bind]
  refine QueryM.bind (QueryM.occ 545 (by decide)) (fun l0 => ?_)
  refine QueryM.bind (QueryM.bool l0) (fun Vp => ?_)
  refine QueryM.bind (QueryM.occ 546 (by decide)) (fun l1 => ?_)
  refine QueryM.bind (QueryM.bits l1 2) (fun tc => ?_)
  refine QueryM.bind (QueryM.feature .FEAT_PMUv3_TH) (fun haveTH => ?_)
  refine QueryM.bind ?_ (fun w2 => ?_)
  · apply QueryM.ite
    · exact QueryM.pure true
    · exact QueryM.bind QueryM.have_a64 (fun a64 => QueryM.pure (!a64))
  · cases w2 with
    | true => exact QueryM.pure none
    | false =>
      simp only [Bool.false_eq_true, reduceIte]
      refine QueryM.bind (QueryM.read PMEVTYPER_EL0) (fun row0 => ?_)
      refine QueryM.bind (QueryM.occ 547 (by decide)) (fun l2 => ?_)
      refine QueryM.bind (QueryM.bool l2) (fun Vc0 => ?_)
      refine QueryM.bind (QueryM.read PMEVTYPER_EL0) (fun row1 => ?_)
      refine QueryM.bind (QueryM.occ 548 (by decide)) (fun l3 => ?_)
      refine QueryM.bind (QueryM.int l3) (fun Vt0 => ?_)
      refine QueryM.bind (QueryM.read PMEVTYPER_EL0) (fun row2 => ?_)
      refine QueryM.bind (QueryM.occ 549 (by decide)) (fun l4 => ?_)
      refine QueryM.bind (QueryM.int l4) (fun v0 => ?_)
      refine QueryM.bind (QueryM.feature .FEAT_PMUv3_EDGE) (fun haveEDGE => ?_)
      refine QueryM.bind ?_ (fun active => ?_)
      · apply QueryM.ite
        · exact QueryM.bind (QueryM.read PMEVTYPER_EL0) (fun row3 => QueryM.pure _)
        · exact QueryM.pure false
      · refine QueryM.bind ?_ (fun v => QueryM.pure _)
        apply QueryM.ite
        · refine QueryM.bind ?_ (fun _ => ?_)
          · apply QueryM.assert
            simp; omega
          · refine QueryM.bind (QueryM.read PMULastThresholdValue) (fun threshold => ?_)
            refine QueryM.bind (QueryM.read PMEVTYPER_EL0) (fun row4 => ?_)
            refine QueryM.bind ?_ (fun tc1 => QueryM.pure _)
            apply QueryM.ite
            · refine QueryM.bind (QueryM.occ 550 (by decide)) (fun l5 => ?_)
              refine QueryM.bind (QueryM.constraint l5) (fun c0 => ?_)
              refine QueryM.bind QueryM.restc (fun p => QueryM.pure _)
            · exact QueryM.pure _
        · exact QueryM.pure _
#print axioms pmu_value_prepare_query
end NativeTagCheck.Hooks

-- Source proof structure: PMUValueRun.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
open NativeTagCheck.HookWrites
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUValueRun.pmu_value_commit_total"
  (← IO.getStderr).flush

theorem pmu_value_commit_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (n : Nat) (Vb : Int)
    (result : Option (Int × Bool)) :
    ∃ v t, PMUValueParts.commit n Vb result s = .ok v t ∧ PMUPost budget s t := by
  cases result with
  | none => exact ⟨Vb, s, rfl, PMUPost.refl budget s q⟩
  | some p =>
    let value := vectorUpdate s.regs.PMULastThresholdValue n p.2
    let t : NativeState := {s with regs := PMULastThresholdValue.set value s.regs}
    have fp := (write_PMULastThresholdValue budget s q value).2.1
    refine ⟨p.1, t, ?_, fp⟩
    simp only [PMUValueParts.commit, bind_app, read_apply, write_apply, pure_apply]
    rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUValueRun.pmu_count_value_total"
  (← IO.getStderr).flush

theorem pmu_count_value_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (n : Nat) (Vb : Int) (hn : n < 31) :
    ∃ v t, (PMUCountValue n Vb : SailM Int) s = .ok v t ∧ PMUPost budget s t := by
  obtain ⟨result, t, hp, hf⟩ := pmu_value_prepare_query n Vb hn s
  have fp := PMUPost.of_eraseOcc_eq q hf
  obtain ⟨v, u, hc, fc⟩ := pmu_value_commit_total budget t fp.quiet n Vb result
  refine ⟨v, u, ?_, fp.trans fc⟩
  rw [PMUValueParts.equation]
  simp only [bind_app, hp, hc]
#print axioms pmu_value_commit_total
#print axioms pmu_count_value_total
end NativeTagCheck.Hooks

-- Source proof structure: IncrementEventParts.lean
-- GENERATED by gen/gen_increment_event_parts.py from actual AArch64_IncrementEventCounter.
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
namespace NativeTagCheck.Hooks.IncrementEventParts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventParts.prefixStage"
  (← IO.getStderr).flush

def prefixStage (idx : Nat) (increment_name : Int) : SailM (Int × Int) := do
  let ovflw : Int := 32
  let w__0 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
  let old_value : Int := (BitVec.toNat (GetElem?.getElem! w__0 idx))
  let w__1 ← (( do (PMUCountValue idx increment_name) ) : SailM Int )
  let new_value : Int := (old_value +i w__1)
  pure (old_value, new_value)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventParts.middle"
  (← IO.getStderr).flush

def middle (idx : Nat) (new_value : Int) : SailM ((BitVec 1) × Int) := do
  let ovflw : Int := 32
  let lp ← (( do (undefined_bitvector_at (← occLabel 2422) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do (HavePMUv3p5 ()) ) : SailM Bool )
  let (lp, ovflw) ← (( do
    if (w__2 : Bool)
    then
      (do
        let w__3 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
        writeReg PMEVCNTR_EL0 (vectorUpdate w__3 idx (integer_subrange new_value 63 0))
        let w__4 ← (( do (PMUCounterIsHyp idx) ) : SailM Bool )
        let w__7 ← (( do
          if (w__4 : Bool)
          then
            (do
              let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_MDCR_EL2_Type_HLP w__5))))
          else
            (do
              let w__6 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
              (pure ((_get_PMCR_EL0_Type_LP w__6)))) ) : SailM (BitVec 1) )
        let lp := (w__7 : (BitVec 1))
        let ovflw : Int :=
          if ((lp == 1#1) : Bool)
          then 64
          else 32
        (pure ((lp, ovflw))))
    else
      (do
        let w__8 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
        writeReg PMEVCNTR_EL0 (vectorUpdate w__8 idx
          (Sail.BitVec.zeroExtend (integer_subrange new_value 31 0) 64))
        let ovflw : Int := 32
        (pure ((lp, ovflw)))) ) : SailM ((BitVec 1) × Int) )
  pure (lp, ovflw)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventParts.tail"
  (← IO.getStderr).flush

def tail (idx : Nat) (old_value new_value : Int) (lp : BitVec 1) (ovflw : Int) : SailM Unit := do
  let ovflw : Int := ovflw
  if (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((64 : Int) -i (ovflw : Int)) +i (1 : Int)))) (integer_subrange
         old_value 64 ovflw)) != (Sail.BitVec.castWidth (integer_subrange new_value 64 ovflw))) : Bool)
  then
    (do
      let w__9 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
      writeReg PMOVSSET_EL0 (BitVec.update w__9 idx (Bit 1#1))
      let w__10 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
      writeReg PMOVSCLR_EL0 (BitVec.update w__10 idx (Bit 1#1))
      let w__15 ← (( do
        if ((← do
             if ((((BitVec.setWidth 1 (BitVec.join1 [(integer_access idx 0)])) == 0#1) : Bool) : Bool)
             then
               (do
                 let w__11 ← (( do (GetNumEventCounters ()) ) : SailM Int )
                 (pure ((((idx +i 1) <b w__11) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            (pure ((← do
                  let w__13 ← (( do (HavePMUv3p5 ()) ) : SailM Bool )
                  (pure (((! w__13) : Bool)))) || ((lp == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__15 : Bool)
      then
        (do
          (PMUEvent__2 PMU_EVENT_CHAIN 1 (idx +i 1)))
      else (pure (())))
  else (pure (()))
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventParts.mark"
  (← IO.getStderr).flush

def mark (idx : Nat) : SailM Unit := do
  let w__9 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSSET_EL0 (BitVec.update w__9 idx (Bit 1#1))
  let w__10 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSCLR_EL0 (BitVec.update w__10 idx (Bit 1#1))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventParts.chain"
  (← IO.getStderr).flush

def chain (idx : Nat) (lp : BitVec 1) : SailM Unit := do
  let w__15 ← (( do
    if ((← do
         if ((((BitVec.setWidth 1 (BitVec.join1 [(integer_access idx 0)])) == 0#1) : Bool) : Bool)
         then
           (do
             let w__11 ← (( do (GetNumEventCounters ()) ) : SailM Int )
             (pure ((((idx +i 1) <b w__11) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (pure ((← do
              let w__13 ← (( do (HavePMUv3p5 ()) ) : SailM Bool )
              (pure (((! w__13) : Bool)))) || ((lp == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__15 : Bool)
  then
    (do
      (PMUEvent__2 PMU_EVENT_CHAIN 1 (idx +i 1)))
  else (pure (()))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventParts.tailCombined"
  (← IO.getStderr).flush

def tailCombined (idx : Nat) (old_value new_value : Int) (lp : BitVec 1) (ovflw : Int) : SailM Unit := do
  let ovflw : Int := ovflw
  if (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((64 : Int) -i (ovflw : Int)) +i (1 : Int)))) (integer_subrange
         old_value 64 ovflw)) != (Sail.BitVec.castWidth (integer_subrange new_value 64 ovflw))) : Bool)
  then
    (do
      mark idx
      chain idx lp)
  else (pure (()))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventParts.tail_equation"
  (← IO.getStderr).flush

theorem tail_equation (idx : Nat) (old_value new_value : Int) (lp : BitVec 1) (ovflw : Int) (s : NativeState) :
    tail idx old_value new_value lp ovflw s = tailCombined idx old_value new_value lp ovflw s := by
  simp only [tail, tailCombined, mark, chain, bind_assoc, pure_bind]
  all_goals rfl
#print axioms tail_equation

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventParts.equation"
  (← IO.getStderr).flush

theorem equation (idx : Nat) (inc : Int) (s : NativeState) :
    (AArch64_IncrementEventCounter idx inc : SailM Unit) s =
      (do let (old_value, new_value) ← prefixStage idx inc
          let (lp, ovflw) ← middle idx new_value
          tail idx old_value new_value lp ovflw : SailM Unit) s := by
  simp only [AArch64_IncrementEventCounter, prefixStage, middle, tail, bind_assoc, pure_bind]
  all_goals rfl
#print axioms equation
end NativeTagCheck.Hooks.IncrementEventParts

-- Source proof structure: IncrementEventMiddle.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
open NativeTagCheck.HookWrites
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventMiddle.increment_event_prefix"
  (← IO.getStderr).flush

theorem increment_event_prefix (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (inc : Int) (hn : idx < 31) :
    ∃ values t, IncrementEventParts.prefixStage idx inc s = .ok values t ∧ PMUPost budget s t := by
  obtain ⟨v, t, hv, fv⟩ := pmu_count_value_total budget s q idx inc hn
  let old : Int := BitVec.toNat (GetElem?.getElem! (s.regs.bank_Vector_BitVec_64_32 .PMEVCNTR_EL0) idx)
  refine ⟨(old, old + v), t, ?_, fv⟩
  simp only [IncrementEventParts.prefixStage, bind_app, read_apply, hv, pure_apply]
  rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventMiddle.increment_event_middle"
  (← IO.getStderr).flush

theorem increment_event_middle (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (newValue : Int) :
    ∃ (lp : BitVec 1) (width : Int) (t : NativeState),
      IncrementEventParts.middle idx newValue s = .ok (lp, width) t ∧
      PMUPost budget s t ∧ (width = 32 ∨ width = 64) := by
  let a := afterOcc 2422 s
  have fa : PMUPost budget s a := PMUPost.of_eraseOcc_eq (s := s) (t := a) q (by simpa only [a] using erase_afterOcc 2422 s (by decide))
  cases h5 : featureValue s .FEAT_PMUv3p5 with
  | false =>
    let value := vectorUpdate (PMEVCNTR_EL0.get a.regs) idx
      (Sail.BitVec.zeroExtend (integer_subrange newValue 31 0) 64)
    let t : NativeState := {a with regs := PMEVCNTR_EL0.set value a.regs}
    have fw := (write_PMEVCNTR_EL0 budget a fa.quiet value).2.1
    refine ⟨oracleChoiceSource.chooseAt (.bitvector 1) (.occ 2422 (s.choiceOcc.getD 2422 0)) s.choiceState, 32, t, ?_, fa.trans fw, Or.inl rfl⟩
    simp only [IncrementEventParts.middle, bind_app, occ_apply, ubv, HavePMUv3p5,
      feature_apply, afterOcc_feature, h5, Bool.false_eq_true, reduceIte, read_apply,
      write_apply, pure_apply]
    rfl
  | true =>
    let value := vectorUpdate (PMEVCNTR_EL0.get a.regs) idx
      (integer_subrange newValue 63 0)
    let w : NativeState := {a with regs := PMEVCNTR_EL0.set value a.regs}
    have fw := (write_PMEVCNTR_EL0 budget a fa.quiet value).2.1
    obtain ⟨hyp, t, hh, hf⟩ := pmu_hyp_query (idx : Int) w fw.quiet.a64
    have fh := PMUPost.of_eraseOcc_eq fw.quiet hf
    simp only [w, value, a] at hh
    cases hyp with
    | false =>
      let lp := _get_PMCR_EL0_Type_LP (t.regs.bank_BitVec_64 .PMCR_EL0)
      refine ⟨lp, (if lp == 1#1 then 64 else 32), t, ?_, (fa.trans fw).trans fh, ?_⟩
      · simp only [IncrementEventParts.middle, bind_app, occ_apply, ubv, HavePMUv3p5,
          feature_apply, afterOcc_feature, h5, reduceIte, read_apply, write_apply,
          hh, Bool.false_eq_true, pure_apply]
        rfl
      · split <;> simp
    | true =>
      let lp := _get_MDCR_EL2_Type_HLP (t.regs.bank_BitVec_64 .MDCR_EL2)
      refine ⟨lp, (if lp == 1#1 then 64 else 32), t, ?_, (fa.trans fw).trans fh, ?_⟩
      · simp only [IncrementEventParts.middle, bind_app, occ_apply, ubv, HavePMUv3p5,
          feature_apply, afterOcc_feature, h5, reduceIte, read_apply, write_apply, hh, pure_apply]
        rfl
      · split <;> simp
#print axioms increment_event_prefix
#print axioms increment_event_middle
end NativeTagCheck.Hooks

-- Source proof structure: IncrementEventTail.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
open NativeTagCheck.HookWrites
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventTail.increment_event_mark"
  (← IO.getStderr).flush

theorem increment_event_mark (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) :
    ∃ t, IncrementEventParts.mark idx s = .ok () t ∧ PMUPost budget s t := by
  let v1 := BitVec.update (PMOVSSET_EL0.get s.regs) idx (Bit 1#1)
  let a : NativeState := {s with regs := PMOVSSET_EL0.set v1 s.regs}
  have fa := (write_PMOVSSET_EL0 budget s q v1).2.1
  let v2 := BitVec.update (PMOVSCLR_EL0.get a.regs) idx (Bit 1#1)
  let t : NativeState := {a with regs := PMOVSCLR_EL0.set v2 a.regs}
  have ft := (write_PMOVSCLR_EL0 budget a fa.quiet v2).2.1
  refine ⟨t, ?_, fa.trans ft⟩
  simp only [IncrementEventParts.mark, bind_app, read_apply, write_apply]
  rfl

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventTail.increment_event_chain"
  (← IO.getStderr).flush

theorem increment_event_chain (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (lp : BitVec 1) :
    ∃ t, IncrementEventParts.chain idx lp s = .ok () t ∧ PMUPost budget s t := by
  by_cases hpar : BitVec.join1 [integer_access (idx : Int) 0] = 0#1
  · by_cases hn : (idx : Int) + 1 < s.regs.bank_Int .NUM_PMU_COUNTERS
    · by_cases hp : ((! featureValue s .FEAT_PMUv3p5) || (lp == 0#1)) = true
      · obtain ⟨acc, ha⟩ := pmu_event2_acc PMU_EVENT_CHAIN 1 ((idx : Int) + 1) s q.a64 q.nrw (by omega) (by have := q.pmuCountUpper; omega)
        let t : NativeState := {s with regs := {s.regs with PMUEventAccumulator := acc}}
        have ft : PMUPost budget s t := (write_PMUEventAccumulator budget s q acc).2.1
        refine ⟨t, ?_, ft⟩
        simpa [IncrementEventParts.chain, bind_assoc, bind_if, pure_bind, bind_app, if_apply, map_apply, hpar, get_num_counters, hn, HavePMUv3p5, feature_apply, pure_apply, hp] using ha
      · refine ⟨s, ?_, PMUPost.refl budget s q⟩
        simp [IncrementEventParts.chain, bind_assoc, bind_if, pure_bind, bind_app, if_apply, map_apply, hpar, get_num_counters, hn, HavePMUv3p5, feature_apply, pure_apply, hp]
    · refine ⟨s, ?_, PMUPost.refl budget s q⟩
      simp [IncrementEventParts.chain, bind_assoc, bind_if, pure_bind, bind_app, if_apply, map_apply, hpar, get_num_counters, hn, pure_apply]
  · refine ⟨s, ?_, PMUPost.refl budget s q⟩
    simp [IncrementEventParts.chain, bind_assoc, bind_if, pure_bind, bind_app, if_apply, map_apply, hpar, pure_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventTail.increment_event_tail"
  (← IO.getStderr).flush

theorem increment_event_tail (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat)
    (oldValue newValue : Int) (lp : BitVec 1) (width : Int) :
    ∃ t, IncrementEventParts.tail idx oldValue newValue lp width s = .ok () t ∧ PMUPost budget s t := by
  rw [IncrementEventParts.tail_equation]
  simp only [IncrementEventParts.tailCombined]
  split
  · obtain ⟨a, ha, fa⟩ := increment_event_mark budget s q idx
    obtain ⟨t, ht, ft⟩ := increment_event_chain budget a fa.quiet idx lp
    exact ⟨t, by simp only [bind_app, ha, ht], fa.trans ft⟩
  · exact ⟨s, rfl, PMUPost.refl budget s q⟩

#print axioms increment_event_mark
#print axioms increment_event_chain
#print axioms increment_event_tail
end NativeTagCheck.Hooks

-- Source proof structure: IncrementEventRun.lean
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
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.IncrementEventRun.increment_event_counter_total"
  (← IO.getStderr).flush

theorem increment_event_counter_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) (inc : Int) (hn : idx < 31) :
    ∃ t, (AArch64_IncrementEventCounter idx inc : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨⟨oldValue, newValue⟩, a, ha, fa⟩ := increment_event_prefix budget s q idx inc hn
  obtain ⟨lp, width, w, hw, fw, _⟩ := increment_event_middle budget a fa.quiet idx newValue
  obtain ⟨t, ht, ft⟩ := increment_event_tail budget w fw.quiet idx oldValue newValue lp width
  refine ⟨t, ?_, (fa.trans fw).trans ft⟩
  rw [IncrementEventParts.equation]
  simp only [bind_app, ha, hw, ht]
#print axioms increment_event_counter_total
end NativeTagCheck.Hooks

-- Source proof structure: CycleCounterParts.lean
-- GENERATED by gen/gen_cycle_counter_parts.py from actual AArch64_IncrementCycleCounter.
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
namespace NativeTagCheck.Hooks.CycleCounterParts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CycleCounterParts.eligible"
  (← IO.getStderr).flush

def eligible : SailM Bool := do
  let w__7 ← (( do
    if ((← do
         (CountPMUEvents CYCLE_COUNTER_ID)) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  if (((! (HaveAArch32 ())) : Bool) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__1 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                      (pure ((((_get_PMCR_EL0_Type_LC w__1) == 1#1) : Bool))))) : Bool)
             then (pure true)
             else
               (do
                 let w__3 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                 (pure ((((_get_PMCR_EL0_Type_D w__3) == 0#1) : Bool))))) : Bool)
        then (pure true)
        else
          (do
            (HasElapsed64Cycles ())))
    else (pure false) ) : SailM Bool )
  pure w__7

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CycleCounterParts.body"
  (← IO.getStderr).flush

def body : SailM Unit := do
  let w__8 ← (( do readReg PMCCNTR_EL0 ) : SailM (BitVec 64) )
  let old_value : Int := (BitVec.toNat w__8)
  let new_value : Int := (old_value +i 1)
  writeReg PMCCNTR_EL0 (Mk_PMCCNTR_EL0_Type (integer_subrange new_value 63 0))
  let ovflw : Int := 32
  let ovflw ← (( do
    if ((HaveAArch32 ()) : Bool)
    then
      (do
        let w__9 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
        let w__10 : Int :=
          if (((_get_PMCR_EL0_Type_LC w__9) == 1#1) : Bool)
          then 64
          else 32
        (pure ((w__10 : Int))))
    else (pure (64)) ) : SailM Int )
  let ovflw : Int := ovflw
  if (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((64 : Int) -i (ovflw : Int)) +i (1 : Int)))) (integer_subrange
         old_value 64 ovflw)) != (Sail.BitVec.castWidth (integer_subrange new_value 64 ovflw))) : Bool)
  then
    (do
      let w__11 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
      writeReg PMOVSSET_EL0 (Sail.BitVec.updateSubrange w__11 31 31 1#1)
      let w__12 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
      writeReg PMOVSCLR_EL0 (Sail.BitVec.updateSubrange w__12 31 31 1#1))
  else (pure (()))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CycleCounterParts.equation"
  (← IO.getStderr).flush

theorem equation (s : NativeState) : (AArch64_IncrementCycleCounter () : SailM Unit) s =
    (do let active ← eligible
        if active then body else pure () : SailM Unit) s := by
  simp only [AArch64_IncrementCycleCounter, eligible, body, bind_assoc, pure_bind]
  all_goals rfl
#print axioms equation
end NativeTagCheck.Hooks.CycleCounterParts

-- Source proof structure: CycleCounterRun.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
open NativeTagCheck.HookWrites
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CycleCounterRun.elapsed64_total"
  (← IO.getStderr).flush

theorem elapsed64_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ elapsed t, (HasElapsed64Cycles () : SailM Bool) s = .ok elapsed t ∧ PMUPost budget s t := by
  by_cases h : s.regs.bank_Int .__clock_divider = 63
  · let t : NativeState := {s with regs := __clock_divider.set 0 s.regs}
    exact ⟨true, t, by simp [HasElapsed64Cycles, bind_app, map_apply, if_apply, read_apply, h, write_apply, pure_apply]; rfl,
      (write___clock_divider budget s q 0).2.1⟩
  · let value := __clock_divider.get s.regs + 1
    let t : NativeState := {s with regs := __clock_divider.set value s.regs}
    exact ⟨false, t, by simp [HasElapsed64Cycles, bind_app, map_apply, if_apply, read_apply, h, write_apply, pure_apply]; rfl,
      (write___clock_divider budget s q value).2.1⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CycleCounterRun.cycle_counter_eligible_total"
  (← IO.getStderr).flush

theorem cycle_counter_eligible_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ active t, CycleCounterParts.eligible s = .ok active t ∧ PMUPost budget s t := by
  obtain ⟨active, a, ha, hf⟩ := count_pmu_events_query budget s q CYCLE_COUNTER_ID (Or.inl rfl)
  have fa := PMUPost.of_eraseOcc_eq q hf
  obtain ⟨elapsed, t, he, fe⟩ := elapsed64_total budget a fa.quiet
  cases active with
  | false => exact ⟨false, a, by simp [CycleCounterParts.eligible, bind_assoc, pure_bind, bind_app, ha, pure_apply], fa⟩
  | true =>
    by_cases hLC : _get_PMCR_EL0_Type_LC (a.regs.bank_BitVec_64 .PMCR_EL0) = 1#1
    · exact ⟨true, a, by simp [CycleCounterParts.eligible, bind_assoc, pure_bind, bind_app, if_apply, ha, HaveAArch32, read_apply, hLC, pure_apply, map_apply], fa⟩
    · by_cases hD : _get_PMCR_EL0_Type_D (a.regs.bank_BitVec_64 .PMCR_EL0) = 0#1
      · exact ⟨true, a, by simp [CycleCounterParts.eligible, bind_assoc, pure_bind, bind_app, if_apply, ha, HaveAArch32, read_apply, hLC, hD, pure_apply, map_apply], fa⟩
      · exact ⟨elapsed, t, by simp [CycleCounterParts.eligible, bind_assoc, pure_bind, bind_app, if_apply, ha, HaveAArch32, read_apply, hLC, hD, he, pure_apply, map_apply], fa.trans fe⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CycleCounterRun.cycle_counter_body_total"
  (← IO.getStderr).flush

theorem cycle_counter_body_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, CycleCounterParts.body s = .ok () t ∧ PMUPost budget s t := by
  let old : Int := BitVec.toNat (PMCCNTR_EL0.get s.regs)
  let new : Int := old + 1
  let value := Mk_PMCCNTR_EL0_Type (integer_subrange new 63 0)
  let a : NativeState := {s with regs := PMCCNTR_EL0.set value s.regs}
  have fa := (write_PMCCNTR_EL0 budget s q value).2.1
  let v1 := Sail.BitVec.updateSubrange (PMOVSSET_EL0.get a.regs) 31 31 1#1
  let w : NativeState := {a with regs := PMOVSSET_EL0.set v1 a.regs}
  have fw := (write_PMOVSSET_EL0 budget a fa.quiet v1).2.1
  let v2 := Sail.BitVec.updateSubrange (PMOVSCLR_EL0.get w.regs) 31 31 1#1
  let t : NativeState := {w with regs := PMOVSCLR_EL0.set v2 w.regs}
  have ft := (write_PMOVSCLR_EL0 budget w fw.quiet v2).2.1
  by_cases hLC : (_get_PMCR_EL0_Type_LC (PMCR_EL0.get a.regs) == 1#1) = true
  all_goals simp only [a, value, new, old] at hLC
  all_goals simp only [CycleCounterParts.body, bind_app, read_apply, write_apply, HaveAArch32,
    Bool.false_eq_true, reduceIte, pure_apply, hLC]
  all_goals try simp only [if_apply]
  all_goals
    split
    · simp only [bind_app, read_apply, write_apply, pure_apply]
      exact ⟨t, rfl, (fa.trans fw).trans ft⟩
    · exact ⟨a, rfl, fa⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.CycleCounterRun.increment_cycle_counter_total"
  (← IO.getStderr).flush

theorem increment_cycle_counter_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (AArch64_IncrementCycleCounter () : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨active, a, ha, fa⟩ := cycle_counter_eligible_total budget s q
  obtain ⟨t, ht, ft⟩ := cycle_counter_body_total budget a fa.quiet
  rw [CycleCounterParts.equation]
  cases active with
  | false => exact ⟨a, by simp only [bind_app, ha, Bool.false_eq_true, reduceIte, pure_apply], fa⟩
  | true => exact ⟨t, by simp only [bind_app, ha, reduceIte, ht], fa.trans ft⟩
#print axioms elapsed64_total
#print axioms cycle_counter_eligible_total
#print axioms cycle_counter_body_total
#print axioms increment_cycle_counter_total
end NativeTagCheck.Hooks

-- Source proof structure: LoopIndexArithmetic.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace NativeTagCheck.LoopIndexArithmetic

/- The provider's checked conversion is ordinary `toNat` on its nonnegative domain. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.LoopIndexArithmetic.toNatChecked_eq_toNat"
  (← IO.getStderr).flush

theorem toNatChecked_eq_toNat (i : Int) (h0 : 0 ≤ i) :
    Sail.Int.toNatChecked i = i.toNat :=
  Sail.Int.toNatChecked_of_nonneg i h0

/- The exact actual loop bounds imply the checked-index cast, strict bounds
and both Boolean guards. No stronger counter or accumulator guard is added. -/
run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.LoopIndexArithmetic.checked_index_facts"
  (← IO.getStderr).flush

theorem checked_index_facts (i counters : Int)
    (h0 : 0 ≤ i) (hi : i ≤ counters - 1) (hc : counters ≤ 31) :
    let n := Sail.Int.toNatChecked i
    (n : Int) = i ∧ n < 31 ∧ (n : Int) < counters ∧
      ((0 ≤b i) && (i ≤b 32)) = true ∧
      ((0 ≤b i) && (i <b 31)) = true := by
  dsimp only
  rw [toNatChecked_eq_toNat i h0]
  have hcast : (i.toNat : Int) = i := by omega
  have h31 : i < 31 := by omega
  have h32 : i ≤ 32 := by omega
  exact ⟨hcast, by omega, by omega, by simp [h0, h32], by simp [h0, h31]⟩

#print axioms toNatChecked_eq_toNat
#print axioms checked_index_facts

end NativeTagCheck.LoopIndexArithmetic

-- Source proof structure: PMUCycleParts.lean
-- GENERATED by gen/gen_pmu_cycle_parts.py from actual AArch64_PMUCycle.
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
namespace NativeTagCheck.Hooks.PMUCycleParts

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUCycleParts.body"
  (← IO.getStderr).flush

def body (idx : Int) : SailM Unit := do
  ArmFull.assert ((0 ≤b idx) && (idx ≤b 32)) "sail-arm/v8_base.sail:34466.65-34466.66"
  let w__5 ← (( do (CountPMUEvents (Sail.Int.toNatChecked (idx))) ) : SailM Bool
    )
  if (w__5 : Bool)
  then
    (do
      ArmFull.assert ((0 ≤b idx) && (idx <b 31)) "sail-arm/v8_base.sail:34468.68-34468.69"
      let w__6 ← (( do readReg PMUEventAccumulator ) : SailM (Vector Int 31) )
      let accumulated : Int :=
        (GetElem?.getElem! w__6 (Sail.Int.toNatChecked (idx)))
      (AArch64_IncrementEventCounter (Sail.Int.toNatChecked (idx)) accumulated))
  else (pure (()))
  ArmFull.assert ((0 ≤b idx) && (idx <b 31)) "sail-arm/v8_base.sail:34472.64-34472.65"
  let w__7 ← (( do readReg PMUEventAccumulator ) : SailM (Vector Int 31) )
  writeReg PMUEventAccumulator (vectorUpdate w__7 (Sail.Int.toNatChecked (idx)) 0)

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUCycleParts.regular"
  (← IO.getStderr).flush

def regular (counters : Int) : SailM Unit := do
  if ((counters != 0) : Bool)
  then
    (do
      let loop_idx_lower : Nat := 0
      let loop_idx_upper : Int := (counters -i 1)
      (do
        let mut loop_vars := ()
        for idx in [loop_idx_lower:loop_idx_upper:1]i do
          let () := loop_vars
          loop_vars ← do
            body idx
        (pure loop_vars)))
  else (pure (()))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUCycleParts.enabled"
  (← IO.getStderr).flush

def enabled : SailM Unit := do
  (PMUEvent PMU_EVENT_CPU_CYCLES)
  let counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  regular counters
  (AArch64_IncrementCycleCounter ())
  (CheckForPMUOverflow ())

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUCycleParts.combined"
  (← IO.getStderr).flush

def combined : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
         (pure ((((_get_PMCR_EL0_Type_E w__0) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_MDCR_EL2_Type_HPME w__1) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do (ShouldBRBEFreeze ()) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          (BRBEFreeze ()))
      else (pure (())))
  else
    (do
      let w__4 ← (( do (HavePMUv3 ()) ) : SailM Bool )
      if ((! w__4) : Bool)
      then (pure (()))
      else
        (do
          enabled))

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUCycleParts.equation"
  (← IO.getStderr).flush

theorem equation (s : NativeState) : (AArch64_PMUCycle () : SailM Unit) s = combined s := by
  simp only [AArch64_PMUCycle, combined, enabled, regular, body, bind_assoc, bind_if, pure_bind, unit_bind]
  all_goals rfl
#print axioms equation
end NativeTagCheck.Hooks.PMUCycleParts

-- Source proof structure: PMUCycleLoop.lean
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
open NativeTagCheck.HookWrites
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUCycleLoop.PMUPost.counter_count"
  (← IO.getStderr).flush

theorem PMUPost.counter_count {budget : Nat} {s t : NativeState} (f : PMUPost budget s t) :
    t.regs.bank_Int .NUM_PMU_COUNTERS = s.regs.bank_Int .NUM_PMU_COUNTERS := by
  exact frame_pres_E20 (fun r => r.bank_Int .NUM_PMU_COUNTERS)
    (fun r => by simp (disch := decide) only [eraseE20, RegMap.set_ne]) f.frame

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUCycleLoop.reset_acc_total"
  (← IO.getStderr).flush

theorem reset_acc_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Nat) :
    ∃ t, (do let a ← readReg PMUEventAccumulator
             writeReg PMUEventAccumulator (vectorUpdate a idx 0) : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  let v := vectorUpdate (PMUEventAccumulator.get s.regs) idx 0
  let t : NativeState := {s with regs := PMUEventAccumulator.set v s.regs}
  exact ⟨t, by simp only [bind_app, read_apply, write_apply]; rfl,
    (write_PMUEventAccumulator budget s q v).2.1⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUCycleLoop.pmu_cycle_body_total"
  (← IO.getStderr).flush

theorem pmu_cycle_body_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (idx : Int)
    (h0 : 0 ≤ idx) (hN : idx < s.regs.bank_Int .NUM_PMU_COUNTERS) (h31 : idx < 31) :
    ∃ t, PMUCycleParts.body idx s = .ok () t ∧ PMUPost budget s t := by
  let n := Sail.Int.toNatChecked idx
  have hn : (n : Int) = idx := by
    dsimp only [n]
    rw [NativeTagCheck.LoopIndexArithmetic.toNatChecked_eq_toNat idx h0]
    omega
  have hn31 : n < 31 := by omega
  have hB32 : ((0 ≤b idx) && (idx ≤b 32)) = true := by simp; omega
  have hB31 : ((0 ≤b idx) && (idx <b 31)) = true := by simp [h0, h31]
  have hi : CountIndexValid n s := Or.inr (Or.inl (by omega))
  obtain ⟨enabled, a, ha, hf⟩ := count_pmu_events_query budget s q n hi
  have fa := PMUPost.of_eraseOcc_eq q hf
  let inc := GetElem?.getElem! (PMUEventAccumulator.get a.regs) n
  obtain ⟨w, hw, fw⟩ := increment_event_counter_total budget a fa.quiet n inc hn31
  cases enabled with
  | false =>
    obtain ⟨t, ht, ft⟩ := reset_acc_total budget a fa.quiet n
    refine ⟨t, ?_, fa.trans ft⟩
    simpa only [PMUCycleParts.body, bind_assoc, bind_if, pure_bind, bind_app, hB32, hB31,
      assert_true, ha, Bool.false_eq_true, reduceIte, n] using ht
  | true =>
    obtain ⟨t, ht, ft⟩ := reset_acc_total budget w fw.quiet n
    refine ⟨t, ?_, (fa.trans fw).trans ft⟩
    simp only [n, inc] at ha hw ht
    simp only [PMUCycleParts.body, bind_assoc, bind_if, pure_bind, bind_app, hB32, hB31,
      assert_true, ha, reduceIte, read_apply, hw]
    exact ht

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUCycleLoop.pmu_cycle_regular_total"
  (← IO.getStderr).flush

theorem pmu_cycle_regular_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) (counters : Int)
    (hC : s.regs.bank_Int .NUM_PMU_COUNTERS = counters) :
    ∃ t, PMUCycleParts.regular counters s = .ok () t ∧ PMUPost budget s t := by
  let range : IntRange := [0:counters-1:1]i
  let step : Int → Unit → SailM (ForInStep Unit) := fun i _ => do
    PMUCycleParts.body i
    pure (.yield ())
  let I : Unit → NativeState → Prop := fun _ t => PMUPost budget s t
  have hs : I () s := PMUPost.refl budget s q
  have hstep : ∀ i, i ∈ range → ∀ b t, I b t →
      ∃ v u, step i b t = .ok v u ∧ I (stepValue v) u := by
    intro i hi b t ft
    have bounds : 0 ≤ i ∧ i ≤ counters - 1 := by simpa [range, Membership.mem] using hi
    have hNUM : t.regs.bank_Int .NUM_PMU_COUNTERS = counters := ft.counter_count.trans hC
    have hu : counters ≤ 31 := by rw [← hC]; exact q.pmuCountUpper
    obtain ⟨_, hn, hcount, _, _⟩ := NativeTagCheck.LoopIndexArithmetic.checked_index_facts i counters bounds.1 bounds.2 hu
    obtain ⟨u, hb, fb⟩ := pmu_cycle_body_total budget t ft.quiet i bounds.1 (by omega) (by omega)
    exact ⟨.yield (), u, by simp only [step, bind_app, hb, pure_apply], ft.trans fb⟩
  obtain ⟨b, t, ht, ft⟩ := range_forIn_preserves range step I hstep () s hs
  cases b
  by_cases hz : counters = 0
  · exact ⟨s, by simp [PMUCycleParts.regular, hz, pure_apply], PMUPost.refl budget s q⟩
  · refine ⟨t, ?_, ft⟩
    simpa [PMUCycleParts.regular, range, step, hz, bind_app, pure_apply, unit_bind] using ht
#print axioms PMUPost.counter_count
#print axioms reset_acc_total
#print axioms pmu_cycle_body_total
#print axioms pmu_cycle_regular_total
end NativeTagCheck.Hooks

-- Source proof structure: PMUCycleRun.lean
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
namespace NativeTagCheck.Hooks

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUCycleRun.pmu_cycle_enabled_total"
  (← IO.getStderr).flush

theorem pmu_cycle_enabled_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, PMUCycleParts.enabled s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨a, ha, fa⟩ := pmu_event_total budget s q PMU_EVENT_CPU_CYCLES
  obtain ⟨w, hw, fw⟩ := pmu_cycle_regular_total budget a fa.quiet (a.regs.bank_Int .NUM_PMU_COUNTERS) rfl
  obtain ⟨u, hu, fu⟩ := increment_cycle_counter_total budget w fw.quiet
  obtain ⟨t, ht, ft⟩ := pmu_check_overflow_total budget u fu.quiet
  exact ⟨t, by simp only [PMUCycleParts.enabled, bind_app, ha, get_num_counters, hw, hu, ht], ((fa.trans fw).trans fu).trans ft⟩

run_cmd do
  IO.eprintln "CURRENT_DECL NativeTagCheck.Hooks.PMUCycleRun.pmu_cycle_total"
  (← IO.getStderr).flush

theorem pmu_cycle_total (budget : Nat) (s : NativeState)
    (q : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (AArch64_PMUCycle () : SailM Unit) s = .ok () t ∧ PMUPost budget s t := by
  obtain ⟨t, ht, ft⟩ := pmu_cycle_enabled_total budget s q
  by_cases hE : _get_PMCR_EL0_Type_E (s.regs.bank_BitVec_64 .PMCR_EL0) = 0#1
  · by_cases hH : _get_MDCR_EL2_Type_HPME (s.regs.bank_BitVec_64 .MDCR_EL2) = 0#1
    · exact ⟨el0QueryState s, pmu_cycle_off s q.a64 q.el0 q.nrw q.scrRW q.hcrRW q.brbePaused hE hH,
        PMUPost.of_eraseOcc_eq q (by simp [eraseOcc, afterOcc, el0QueryState, Std.ExtHashMap.getD_insert])⟩
    · rw [PMUCycleParts.equation]
      cases hP : featureValue s .FEAT_PMUv3 with
      | false => exact ⟨s, by simp [PMUCycleParts.combined, bind_app, read_pmcr, read_mdcr, hE, hH, HavePMUv3, feature_apply, hP, pure_apply, map_apply], PMUPost.refl budget s q⟩
      | true => exact ⟨t, by simp [PMUCycleParts.combined, bind_app, read_pmcr, read_mdcr, hE, hH, HavePMUv3, feature_apply, hP, pure_apply, map_apply, ht], ft⟩
  · rw [PMUCycleParts.equation]
    cases hP : featureValue s .FEAT_PMUv3 with
    | false => exact ⟨s, by simp [PMUCycleParts.combined, bind_app, read_pmcr, hE, HavePMUv3, feature_apply, hP, pure_apply, map_apply], PMUPost.refl budget s q⟩
    | true => exact ⟨t, by simp [PMUCycleParts.combined, bind_app, read_pmcr, hE, HavePMUv3, feature_apply, hP, pure_apply, map_apply, ht], ft⟩
#print axioms pmu_cycle_enabled_total
#print axioms pmu_cycle_total
end NativeTagCheck.Hooks

namespace NativeTagCheck.Hooks
open ArmBridge.Draft NativeMteTagCheck
theorem delta_of_view {s t : NativeState} (h : choiceView t = choiceView s) : ChoiceDelta s t 0 := by
  unfold choiceView at h
  refine ⟨congrArg (fun view => view.1.1) h, ?_⟩
  simpa only [Nat.add_zero] using congrArg Prod.snd h
theorem pmu_event_choice (budget : Nat) (s : NativeState)
    (quiet : ArmCert.HookQuiet.V0.HookQuiet budget s) (event : BitVec 16) :
    ∃ t, (PMUEvent event : SailM Unit) s = .ok () t ∧
      PMUPost budget s t ∧ ChoiceDelta s t 0 := by
  obtain ⟨t, run, post⟩ := pmu_event_total budget s quiet event
  exact ⟨t, run, post, delta_of_view post.choiceState⟩
theorem pmu_cycle_choice (budget : Nat) (s : NativeState)
    (quiet : ArmCert.HookQuiet.V0.HookQuiet budget s) :
    ∃ t, (AArch64_PMUCycle () : SailM Unit) s = .ok () t ∧
      PMUPost budget s t ∧ ChoiceDelta s t 0 := by
  obtain ⟨t, run, post⟩ := pmu_cycle_total budget s quiet
  exact ⟨t, run, post, delta_of_view post.choiceState⟩
theorem system_counter_choice (budget : Nat) (s : NativeState)
    (quiet : ArmCert.HookQuiet.V0.HookQuiet (budget+1) s) :
    ∃ t, (__UpdateSystemCounter () : SailM Unit) s = .ok () t ∧
      CounterPost budget s t ∧ ChoiceDelta s t 0 := by
  obtain ⟨t, run, post⟩ := system_counter_total budget s quiet
  exact ⟨t, run, post, delta_of_view post.choiceState⟩
#print axioms pmu_event_choice
#print axioms pmu_cycle_choice
#print axioms system_counter_choice
end NativeTagCheck.Hooks
