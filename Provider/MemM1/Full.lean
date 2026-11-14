import MemM1.NoFault
import Walk.S1EL10PermsCallees
import GetEntry.PrefixCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
namespace MemM1.Full
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality MemM1.NoFault

/-- M1-c (FullTranslate, EL2&0 regime): no stage 2; the result is the S1Translate output address descriptor. -/
theorem full (va : BitVec 64) (acc : AccessDescriptor) (aligned : Bool) (s : State)
    (P : AddressDescriptor → State → Prop)
    (hP : ∀ ad t u, P ad t → Frame t u → P ad u)
    (hss : acc.ss = .SS_NonSecure)
    (hR : ∀ t, Frame s t → ∃ u, TranslationRegime acc.el t = .ok .Regime_EL20 u ∧ Frame t u)
    (hS1 : ∀ f t, Frame s t → f.statuscode = .Fault_None →
      ∃ fr ipa u, AArch64_S1Translate f .Regime_EL20 va aligned acc t = .ok (fr, ipa) u ∧
        fr.statuscode = .Fault_None ∧ P ipa u) :
    ∃ ipa u, AArch64_FullTranslate va acc aligned s = .ok ipa u ∧ P ipa u := by
  rcases occ_normal 1623 s with ⟨l1, s1, h1, f1⟩
  rcases S1EntryCalleesExtra.bool_normal l1 s1 with ⟨b1, s2, h2, f2⟩
  have f02 := frame_trans f1 f2
  rcases hR s2 f02 with ⟨s2', h3, f2'⟩
  rcases nofault acc s2' with ⟨nf, s3, h4, hnf, f3⟩
  have f03 := frame_trans (frame_trans f02 f2') f3
  rcases occ_normal 1624 s3 with ⟨l2, s4, h5, f4⟩
  rcases addr l2 s4 with ⟨a0, s5, h6, f5⟩
  have f05 := frame_trans (frame_trans f03 f4) f5
  rcases hS1 nf s5 f05 hnf with ⟨fr, ipa, u, h7, hfr, hPu⟩
  rcases S1EL10PermsCallees.el2_normal u with ⟨e2, u1, h8, fu1⟩
  have hfrn : (fr.statuscode != Fault.Fault_None) = false := by rw [hfr]; rfl
  have hrealm : (acc.ss == SecurityState.SS_Realm) = false := by rw [hss]; rfl
  have hreg : (Regime.Regime_EL20 == Regime.Regime_EL10) = false := rfl
  refine ⟨ipa, u1, ?_, hP ipa u u1 hPu fu1⟩
  unfold AArch64_FullTranslate
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, h1, h2, h3, h4, h5, h6, h7, hfrn,
    Bool.false_eq_true, ↓reduceIte, h8, hrealm, implies, hreg, ArmFull.assert]
  rfl

#print axioms full
end MemM1.Full
