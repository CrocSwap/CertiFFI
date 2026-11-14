import M1a.J3c
import Pilot.ObservationSimp
import Walk.S1EL10PermsCallees
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a.Fetch
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

drive_spec exrec_native, exrec_eq : fun (l : ChoiceLabel) (s : State) => undefined_ExceptionRecord l () s
drive_spec bool_native, bool_eq : fun (l : ChoiceLabel) (s : State) => undefined_bool_at l () s

theorem exrec_normal (l : ChoiceLabel) : Normal (undefined_ExceptionRecord l ()) := by
  intro s
  refine ⟨_, _, rfl, ?_⟩
  exact ⟨rfl, rfl, rfl⟩

theorem bool_normal (l : ChoiceLabel) : Normal (undefined_bool_at l ()) := by
  intro s; rw [bool_eq]; observe_simp [Frame, bool_native]
  cases h : oracleChoiceSource.chooseAt Primitive.bool l s.choiceState
  · exact Or.inl ⟨s, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
  · exact Or.inr ⟨s, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

theorem pc_slice (x : BitVec 64) :
    BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb x (Int.toNatChecked 63) 0) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Sail.BitVec.extractLsb, BitVec.castWidth, Int.toNatChecked, BitVec.getLsbD_extractLsb]
  omega

theorem pca (s : State) (hA : Sail.BitVec.extractLsb s.regs._PC 1 0 = 0#2) :
    AArch64_CheckPCAlignment () s = .ok () s := by
  simp [AArch64_CheckPCAlignment, pc_slice, ThisInstrAddr, readReg, PreSail.readReg_apply, hA,
    ArmFull.assert, PreSail.assert, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem cis (s : State) (hIL : s.regs.PSTATE.IL = 0#1) :
    ∃ t, AArch64_CheckIllegalState () s = .ok () t ∧ Frame s t := by
  rcases exrec_normal (.site 2402) s with ⟨e1, s1, h1, f1⟩
  rcases bool_normal (.site 2403) s1 with ⟨b, s2, h2, f2⟩
  rcases S1EL10PermsCallees.int_normal (.site 2404) s2 with ⟨i, s3, h3, f3⟩
  have hp : s3.regs.PSTATE.IL = 0#1 := by rw [f3.1, f2.1, f1.1]; exact hIL
  refine ⟨s3, ?_, ⟨f3.1.trans (f2.1.trans f1.1), f3.2.1.trans (f2.2.1.trans f1.2.1),
    f3.2.2.trans (f2.2.2.trans f1.2.2)⟩⟩
  simp [AArch64_CheckIllegalState, Bind.bind, EStateM.bind, h1, h2, h3, readReg,
    PreSail.readReg_apply, hp, Pure.pure, EStateM.pure]

#print axioms pca
#print axioms cis
end ArmCert.Eval.M1a.Fetch
