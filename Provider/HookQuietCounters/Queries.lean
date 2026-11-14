import HookQuietCounters.PMUBody
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.if_apply"
  (← IO.getStderr).flush

theorem if_apply {α β : Type} (p : Prop) [Decidable p] (f g : α → β) (a : α) :
    (if p then f else g) a = if p then f a else g a := by split <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.afterOcc"
  (← IO.getStderr).flush

def afterOcc (site : Nat) (s : NativeState) : NativeState :=
  {s with choiceOcc := s.choiceOcc.insert site (s.choiceOcc.getD site 0 + 1)}

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.occ_apply"
  (← IO.getStderr).flush

theorem occ_apply (site : Nat) (s : NativeState) :
    (occLabel site : SailM ChoiceLabel) s =
      .ok (.occ site (s.choiceOcc.getD site 0)) (afterOcc site s) := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.read_apply"
  (← IO.getStderr).flush

theorem read_apply {α : Type} (r : RegisterRef Regs α) (s : NativeState) :
    (readReg r : SailM α) s = .ok (r.get s.regs) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.unknown_bool"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.scr_gen"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.secure_below"
  (← IO.getStderr).flush

theorem secure_below (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    (IsSecureBelowEL3 () : SailM Bool) s =
      .ok (_get_SCRType_NS (s.regs.bank_BitVec_64 .SCR_EL3) == 0#1) (afterOcc 490 s) := by
  simp only [IsSecureBelowEL3, HaveEL, ↓reduceIte, bind_app, scr_gen s ha, pure_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.el_state_k0"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.el_state0"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.el_state_nonzero"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.el0QueryState"
  (← IO.getStderr).flush

def el0QueryState (s : NativeState) : NativeState :=
  afterOcc 8 (afterOcc 488 (afterOcc 487 (afterOcc 490 s)))

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.el_using0"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.el_using_nonzero"
  (← IO.getStderr).flush

theorem el_using_nonzero (el : BitVec 2) (s : NativeState)
    (ha : featureValue s .FEAT_AA64EL0 = true) (he : el ≠ 0#2) :
    (ELUsingAArch32 el : SailM Bool) s =
      .ok false (afterOcc 488 (afterOcc 487 (afterOcc 490 s))) := by
  simp only [ELUsingAArch32, bind_app, secure_below s ha, el_state_nonzero _ _ _ he]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.branch_record_paused0"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Queries.should_brbe_paused"
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

end HookQuietCounters
