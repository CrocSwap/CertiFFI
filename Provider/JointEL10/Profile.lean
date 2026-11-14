import JointEL10.Impl
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
namespace ArmCert.Eval.JointSAT
open S1OuterSetup

/-- J1: EL1&0 stage-1 profile. Exactly the guards consumed by the walk component
    theorems (S1OuterSetup.Context/Ready, S1EntryPathTotal.total cache/txsz/start),
    plus the actual public GetS1TTWParams .ok binding of the context parameters:
    the profile CONTAINS that binding; the J2 witnesses prove it, and it is a
    caller obligation for users of the J4 bridge. No whole-walk success premise. Table topology/encoding is NOT part of this profile; it is
    the per-case Path/Realizes data of the non-vacuity witnesses (J3). -/
structure ProfileEL10 (c : Context) (s : State) : Prop where
  ready : Ready c s
  tlb : s.regs.bank_Bool .__tlb_enabled = false
  el10 : c.regime = .Regime_EL10
  tx : c.wp.txsz = 16#6
  start : c.startlevel = 0
  ps : c.wp.ps = 5#3
  get : ∃ final, AArch64_GetS1TTWParams c.regime c.acc.ss c.va s = .ok c.wp final ∧
    S1Normality.Frame s final
end ArmCert.Eval.JointSAT
