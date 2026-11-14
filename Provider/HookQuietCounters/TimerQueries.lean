import HookQuietCounters.Security
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerQueries.el3QueryState"
  (← IO.getStderr).flush

def el3QueryState (s : NativeState) : NativeState :=
  afterOcc 488 (afterOcc 487 (afterOcc 490 s))

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerQueries.secureEL2QueryState"
  (← IO.getStderr).flush

def secureEL2QueryState (s : NativeState) : NativeState :=
  if featureValue s .FEAT_SEL2 then el3QueryState s else s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerQueries.secure_el2"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerQueries.el2QueryState"
  (← IO.getStderr).flush

def el2QueryState (s : NativeState) : NativeState :=
  if _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1 then
    afterOcc 490 s else secureEL2QueryState (afterOcc 490 s)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.TimerQueries.el2_enabled"
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

end HookQuietCounters
