-- Additive variants of canonical MemM1.Wrapper.translate / MemM1.WitnessIF.translateIF (proofs
-- copied verbatim) exposing the concrete actual final state: the debug successor with the actual
-- translationEnd event pushed (canonical statements hide it behind an existential).
import MemM1.Wrapper
import MemM1.M1CoreIF
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace ArmCertWalk
open S1Normality

-- Same per-declaration budget as the canonical source proofs (Wrapper 400k, WitnessIF 800k).
set_option maxHeartbeats 400000 in
theorem translate_events (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : MemM1.Wrapper.State)
    (R : Regime) (s0 : MemM1.Wrapper.State) (tsi : TranslationStartInfo) (s1 : MemM1.Wrapper.State) (ad : AddressDescriptor) (t : MemM1.Wrapper.State)
    (df : FaultRecord) (t2 : MemM1.Wrapper.State)
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
    AArch64_TranslateAddress va acc aligned size s =
        .ok { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 }
          { t2 with events := t2.events.push (Event.translationEnd
            { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 }) } := by
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
#print axioms translate_events


set_option maxHeartbeats 800000 in
theorem translateIF_events (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (size : Int) (s : MemM1.Wrapper.State)
    (R : Regime) (s0 : MemM1.Wrapper.State) (tsi : TranslationStartInfo) (s1 : MemM1.Wrapper.State) (ad : AddressDescriptor) (t : MemM1.Wrapper.State)
    (df : FaultRecord) (t2 : MemM1.Wrapper.State)
    (hacc : acc.acctype = .AccessType_IFETCH)
    (hreg : TranslationRegime acc.el s = .ok R s0)
    (htsi : AArch64_GetTranslationStartInfo R acc.ss acc va size s0 = .ok tsi s1)
    (hfull : AArch64_FullTranslate va acc aligned
      { s1 with events := s1.events.push (.translationStart tsi) } = .ok ad t)
    (hnf : ad.fault.statuscode = .Fault_None)
    (hrme : HaveRME () t = .ok false t)
    (hdbg : AArch64_CheckDebug va acc size t = .ok df t2) :
    AArch64_TranslateAddress va acc aligned size s =
        .ok { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 }
          { t2 with events := t2.events.push (Event.translationEnd
            { ad with fault := df, vaddress := Sail.BitVec.zeroExtend va 64 }) } := by
  have hnn : (Fault.Fault_None != Fault.Fault_None) = false := rfl
  have hacc1 : (acc.acctype == AccessType.AccessType_IFETCH) = true := by rw [hacc]; rfl
  have hacc2 : (acc.acctype != AccessType.AccessType_IFETCH) = false := by rw [hacc]; rfl
  unfold AArch64_TranslateAddress
  simp only [Bind.bind, EStateM.bind, readReg, PreSail.readReg_apply, hacc1, Bool.true_or, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, start_translation,
    ArmFull.ConcurrencyInterfaceV1.sail_translation_start, PreSail.sail_translation_start, PreSail.logEvent,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  simp only [hreg, htsi]
  simp only [hfull, IsFault, hnf, hnn, Bool.not_false, Bool.true_and, hacc2, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, EStateM.bind, EStateM.pure, hrme, Bool.false_and, hacc1,
    Bool.and_true, hdbg, Bool.true_or, Bool.not_true, end_translation,
    ArmFull.ConcurrencyInterfaceV1.sail_translation_end, PreSail.sail_translation_end, PreSail.logEvent,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
#print axioms translateIF_events

end ArmCertWalk
