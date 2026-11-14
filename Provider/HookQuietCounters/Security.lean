import HookQuietCounters.Queries
import ArmCert.HookQuiet.V0.Predicate
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.me_bind_apply"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.me_lift_apply"
  (← IO.getStderr).flush

theorem me_lift_apply {ρ α : Type} (x : SailM α) (s : NativeState) :
    (@ExceptT.run (Sail.Error exception ⊕ ρ) SailM α (monadLift x : SailME ρ α)) s = match x s with
      | .ok a t => .ok (.ok a) t
      | .error e t => .error e t := by
  change EStateM.map Except.ok x s = _
  unfold EStateM.map
  cases x s <;> rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.me_pure_apply"
  (← IO.getStderr).flush

theorem me_pure_apply {ρ α : Type} (a : α) (s : NativeState) :
    (@ExceptT.run (Sail.Error exception ⊕ ρ) SailM α (pure a : SailME ρ α)) s = .ok (.ok a) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.me_map_apply"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.me_run_apply"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.securityNoRMEState"
  (← IO.getStderr).flush

def securityNoRMEState (s : NativeState) : NativeState :=
  afterOcc 488 (afterOcc 487 (afterOcc 490 (afterOcc 503 s)))

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.security_no_rme"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.bit_cases"
  (← IO.getStderr).flush

theorem bit_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  have h : x.toNat = 0 ∨ x.toNat = 1 := by have := x.isLt; omega
  rcases h with h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (BitVec.eq_of_toNat_eq h)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.effectiveNSValue"
  (← IO.getStderr).flush

def effectiveNSValue (s : NativeState) : BitVec 1 :=
  if featureValue s .FEAT_RME && !featureValue s .FEAT_SEL2 then 1#1
  else _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3)

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.effective_ns"
  (← IO.getStderr).flush

theorem effective_ns (s : NativeState) :
    (EffectiveSCR_EL3_NS () : SailM (BitVec 1)) s = .ok (effectiveNSValue s) s := by
  cases hr : featureValue s .FEAT_RME <;>
    cases hs : featureValue s .FEAT_SEL2 <;>
    simp [EffectiveSCR_EL3_NS, HaveSecureState, HaveEL, HaveRME, HaveSecureEL2Ext,
      bind_app, pure_apply, map_apply, feature_apply, read_apply, effectiveNSValue, hr, hs]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.me_throw_apply"
  (← IO.getStderr).flush

theorem me_throw_apply {ρ α : Type} (a : ρ) (s : NativeState) :
    (@ExceptT.run (Sail.Error exception ⊕ ρ) SailM α (ArmFull.SailME.throw a)) s =
      .ok (.error (.inr a)) s := rfl

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.securityRMEValue"
  (← IO.getStderr).flush

def securityRMEValue (s : NativeState) : SecurityState :=
  if _get_SCR_EL3_Type_NSE (s.regs.bank_BitVec_64 .SCR_EL3) == 0#1 then
    if effectiveNSValue s == 0#1 then .SS_Secure else .SS_NonSecure
  else .SS_Realm

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.security_rme"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.securityValue"
  (← IO.getStderr).flush

def securityValue (s : NativeState) : SecurityState :=
  if featureValue s .FEAT_RME then securityRMEValue s
  else if _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) == 1#1
    then .SS_NonSecure else .SS_Secure

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.securityQueryState"
  (← IO.getStderr).flush

def securityQueryState (s : NativeState) : NativeState :=
  if featureValue s .FEAT_RME then afterOcc 503 s else securityNoRMEState s

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.security0_quiet"
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.Security.current_security_quiet"
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

end HookQuietCounters
