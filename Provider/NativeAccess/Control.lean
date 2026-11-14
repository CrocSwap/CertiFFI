import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option Elab.async false
namespace NativeAccess

-- Actual alignment-control execution, including the overwritten undefined
-- choice and its occurrence counter. This is not an initial-state identity.
drive_spec alignment_host_native, alignment_host_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      (el : s.regs.PSTATE.EL = 0#2)
      (nrw : s.regs.PSTATE.nRW = 0#1)
      (aa64 : s.regs.FeatureImpl[4]! = true)
      (rme : s.regs.FeatureImpl[232]! = false)
      (vhe : s.regs.FeatureImpl[(Sail.Int.toNatChecked (num_of_Feature .FEAT_VHE))]! = true)
      (ns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
      (e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
      (tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1) =>
    ((do let b ← AlignmentEnforced ()
         let u ← get
         pure (b, u.regs, u.mem, u.events)) : SailM _) s

#print axioms alignment_host_complete

structure HostPins (s : SequentialState Regs oracleChoiceSource) : Prop where
  el : s.regs.PSTATE.EL = 0#2
  nrw : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  rme : s.regs.FeatureImpl[232]! = false
  vhe : s.regs.FeatureImpl[54]! = true
  ns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1
  e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1
  tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1

-- The host regime binds A to SCTLR_EL2, including the EL0 VHE alias.
-- The resulting state is existential: the model's choice occurrence changes.
theorem alignment_host_disabled (s : SequentialState Regs oracleChoiceSource) (g : HostPins s)
    (a : _get_SCTLR_EL2_Type_A (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1) :
    ∃ u, (AlignmentEnforced () : SailM Bool) s = .ok false u ∧
      u.regs = s.regs ∧ u.mem = s.mem ∧ u.events = s.events := by
  obtain ⟨u, hu⟩ : ∃ u, alignment_host_native s = .ok (false, s.regs, s.mem, s.events) u := by
    unfold alignment_host_native
    simp only [_get_SCTLR_EL2_Type_A] at a
    have vhe : s.regs.FeatureImpl[54] = true := by simpa using g.vhe
    have ns : Sail.BitVec.extractLsb (Mk_SCRType (s.regs.bank_BitVec_64 .SCR_EL3)) 0 0 = 1#1 := by
      simpa only [Mk_SCRType, _get_SCR_EL3_Type_NS] using g.ns
    simp only [a, vhe, ns, true_and, true_or, ite_true]
    exact ⟨_, rfl⟩
  have hc := (alignment_host_complete s g.el g.nrw g.aa64 g.rme g.vhe g.ns g.e2h g.tge).trans hu
  cases h : (AlignmentEnforced () : SailM Bool) s with
  | ok b t =>
    simp only [bind, Bind.bind, EStateM.bind, h, get, getThe, MonadStateOf.get, EStateM.get,
      pure, EStateM.pure] at hc
    have hv := (EStateM.Result.ok.inj hc).1
    obtain ⟨hb, rest⟩ := Prod.mk.inj hv
    have hr := congrArg Prod.fst rest
    have hm := congrArg (fun p => p.2.1) rest
    have he := congrArg (fun p => p.2.2) rest
    subst b
    exact ⟨t, rfl, hr, hm, he⟩
  | error e t =>
    simp only [bind, Bind.bind, EStateM.bind, h] at hc
    cases hc

#print axioms alignment_host_disabled

/-- The ordinary load/store descriptor restrictions, independent of alignment. -/
structure Plain (acc : AccessDescriptor) : Prop where
  not_gcs : (acc.acctype == AccessType.AccessType_GCS) = false
  rcw : acc.rcw = false
  ls64 : acc.ls64 = false
  exclusive : acc.exclusive = false
  atomicop : acc.atomicop = false
  acqsc : acc.acqsc = false
  acqpc : acc.acqpc = false
  relsc : acc.relsc = false

theorem plain_unaligned_allowed (s : SequentialState Regs oracleChoiceSource) (g : HostPins s)
    (a : _get_SCTLR_EL2_Type_A (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1)
    (acc : AccessDescriptor) (p : Plain acc) (address : BitVec 64) (size : Int) :
    ∃ u, (AArch64_UnalignedAccessFaults acc address size : SailM Bool) s = .ok false u ∧
      u.regs = s.regs ∧ u.mem = s.mem ∧ u.events = s.events := by
  obtain ⟨u, control, regs, mem, events⟩ := alignment_host_disabled s g a
  refine ⟨u, ?_, regs, mem, events⟩
  unfold AArch64_UnalignedAccessFaults
  simp only [bind, Bind.bind, EStateM.bind, control, pure, EStateM.pure, Bool.false_eq_true,
    ite_false, p.not_gcs, p.rcw, p.ls64, p.exclusive, p.atomicop, p.acqsc, p.acqpc, p.relsc,
    Bool.false_or]

/-- Public features that select the frozen model's memory decomposition. -/
structure AccessProfile where
  lse2 : Bool
  lrcpc3 : Bool
  deriving DecidableEq, Repr

def profileOf (s : SequentialState Regs oracleChoiceSource) : AccessProfile :=
  ⟨s.regs.FeatureImpl[111], s.regs.FeatureImpl[190]⟩

/-- Profile binding to the actual state and applicable host SCTLR bank. -/
structure ProfileAt (p : AccessProfile) (s : SequentialState Regs oracleChoiceSource) : Prop where
  lse2 : s.regs.FeatureImpl[111] = p.lse2
  lrcpc3 : s.regs.FeatureImpl[190] = p.lrcpc3
  host : HostPins s
  alignment_disabled : _get_SCTLR_EL2_Type_A (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#1

theorem have_lse2 (s : SequentialState Regs oracleChoiceSource) :
    (HaveLSE2Ext () : SailM Bool) s = .ok s.regs.FeatureImpl[111] s := by rfl

theorem have_lrcpc3 (s : SequentialState Regs oracleChoiceSource) :
    (HaveLRCPC3Ext () : SailM Bool) s = .ok s.regs.FeatureImpl[190] s := by rfl

theorem ProfileAt.lse2_run {p : AccessProfile} {s : SequentialState Regs oracleChoiceSource}
    (h : ProfileAt p s) : (HaveLSE2Ext () : SailM Bool) s = .ok p.lse2 s := by
  rw [have_lse2, h.lse2]

theorem ProfileAt.lrcpc3_run {p : AccessProfile} {s : SequentialState Regs oracleChoiceSource}
    (h : ProfileAt p s) : (HaveLRCPC3Ext () : SailM Bool) s = .ok p.lrcpc3 s := by
  rw [have_lrcpc3, h.lrcpc3]

#print axioms plain_unaligned_allowed
#print axioms have_lse2
#print axioms have_lrcpc3
end NativeAccess
