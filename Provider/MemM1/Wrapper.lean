import ArmFull
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
namespace MemM1.Wrapper
abbrev State := SequentialState Regs oracleChoiceSource

/-- M1-c: AArch64_TranslateAddress for a non-IFETCH access in a profile with SPE sampling off and RME absent,
    given the results of its sub-calls (each discharged separately). The final state differs from the
    CheckDebug result state only in the event log. -/
theorem translate (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : State)
    (R : Regime) (s0 : State) (tsi : TranslationStartInfo) (s1 : State) (ad : AddressDescriptor) (t : State)
    (df : FaultRecord) (t2 : State)
    (hspe : Register.SPESampleInFlight.get s.regs = false)
    (hreg : TranslationRegime acc.el s = .ok R s0)
    (htsi : AArch64_GetTranslationStartInfo R acc.ss acc va size s0 = .ok tsi s1)
    (hfull : AArch64_FullTranslate va acc aligned
      { s1 with events := s1.events.push (.translationStart tsi) } = .ok ad t)
    (hnf : ad.fault.statuscode = .Fault_None)
    (hnotif : acc.acctype ≠ .AccessType_IFETCH)
    (hdbg : AArch64_CheckDebug va acc size t = .ok df t2)
    (hdf : df.statuscode = .Fault_None)
    (hrme : HaveRME () t2 = .ok false t2)
    (hspe2 : Register.SPESampleInFlight.get t2.regs = false) :
    ∃ t3, AArch64_TranslateAddress va acc aligned size s =
        .ok { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 } t3 ∧
      t3.regs = t2.regs ∧ t3.mem = t2.mem := by
  refine ⟨{ t2 with events := t2.events.push (Event.translationEnd
      { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 }) }, ?_, rfl, rfl⟩
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hacc : (acc.acctype != AccessType.AccessType_IFETCH) = true := by
    cases h : acc.acctype <;> first | rfl | exact absurd h hnotif
  have hacc2 : (acc.acctype == AccessType.AccessType_IFETCH) = false := by
    cases h : acc.acctype <;> first | rfl | exact absurd h hnotif
  have hdfn : (df.statuscode != Fault.Fault_None) = false := by rw [hdf]; rfl
  unfold AArch64_TranslateAddress
  simp only [Bind.bind, EStateM.bind, readReg, PreSail.readReg_apply, hspe, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, Pure.pure, EStateM.pure, start_translation,
    ArmFull.ConcurrencyInterfaceV1.sail_translation_start, PreSail.sail_translation_start, PreSail.logEvent,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  simp only [hreg, htsi]
  simp only [hfull, IsFault, hnf, hnn, Bool.not_false, Bool.true_and, hacc, ↓reduceIte, EStateM.bind, EStateM.pure,
    hdbg, hrme, Bool.false_and, Bool.false_eq_true, hdfn, hspe2, hacc2, Bool.false_or, end_translation,
    ArmFull.ConcurrencyInterfaceV1.sail_translation_end, PreSail.sail_translation_end, PreSail.logEvent,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
#print axioms translate
end MemM1.Wrapper
