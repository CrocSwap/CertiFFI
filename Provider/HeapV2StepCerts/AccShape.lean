-- Memory (certiffi (c3)): the ACTUAL GPR descriptor of the memory classes has the plan's
-- DataShape (SDK AccGPR.create, plus contiguous = first = false read off nadg_native).
import MemM1.AccGPR
import ArmCertTranslateModel.ClosedTable
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
namespace HeapV2StepCerts.AccShape
open MemM1.AccGPR

theorem nadg_cf (s : MemM1.AccGPR.State) (acc : AccessDescriptor) (t : MemM1.AccGPR.State)
    (h : MemM1.AccGPR.nadg_native s = .ok acc t) : acc.contiguous = false ∧ acc.first = false := by
  delta MemM1.AccGPR.nadg_native at h
  injection h with ha ht
  subst ha
  exact ⟨rfl, rfl⟩

theorem create' (s : State) (memop : ArmFull.MemOp) (nontemporal tagchecked : Bool)
    (hmemop : memop = .MemOp_LOAD ∨ memop = .MemOp_STORE)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hEL : s.regs.PSTATE.EL = 0#2)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hTME : s.regs.FeatureImpl[227] = false) :
    ∃ acc t, CreateAccDescGPR memop nontemporal false tagchecked s = .ok acc t ∧
      MemM1.Witness.Acc0 acc ∧ MemM1.MemReadD2.AccDR2 acc ∧ MemM1.MemWriteD5.AccDWT acc ∧
      acc.read = (memop == .MemOp_LOAD) ∧ acc.write = (memop == .MemOp_STORE) ∧
      acc.tagchecked = tagchecked ∧ S1Normality.Frame s t ∧
      ArmCert.Translate.Model.DataShape (memop == .MemOp_STORE) acc := by
  have hn : NewAccDesc .AccessType_GPR s = nadg_native s :=
    nadg_eq s hNoRME hA64 hEL3A64 hNoEL3A32 hEL
  have hf := nadg_frame s hEL
  cases hr : nadg_native s with
  | error e t => rw [hr] at hf; exact hf.elim
  | ok a0 t0 =>
    rw [hr] at hf
    rcases nadg_fields s a0 t0 hEL hNS hr with ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩
    have q12 : a0.contiguous = false ∧ a0.first = false := nadg_cf s a0 t0 hr
    have ht : HaveTME () t0 = .ok false t0 := tme_off t0 (by rw [hf.1]; exact hTME)
    let acc : AccessDescriptor :=
      { a0 with
        el := EL0
        nontemporal := nontemporal
        read := (memop == .MemOp_LOAD)
        write := (memop == .MemOp_STORE)
        pan := true
        tagchecked := tagchecked
        transactional := false }
    have hc : CreateAccDescGPR memop nontemporal false tagchecked s = .ok acc t0 := by
      unfold CreateAccDescGPR
      simp only [Bind.bind, EStateM.bind, hn, hr, Bool.not_false, ↓reduceIte, Pure.pure, EStateM.pure, ht,
        Bool.false_eq_true]
      rfl
    have hA0 : MemM1.Witness.Acc0 acc := ⟨q1, rfl, q2, q3, q4, rfl, q5, q6⟩
    have rw' : (memop == .MemOp_LOAD) = !(memop == .MemOp_STORE) := by
      rcases hmemop with h | h <;> subst h <;> rfl
    exact ⟨acc, t0, hc, hA0, ⟨q2, rfl, q7, q8, q9, q10, q11⟩, ⟨hA0, q7, q8, q9, q10, q11⟩, rfl, rfl, rfl,
      ⟨hf.1, hf.2.1, hf.2.2.1⟩,
      ⟨q2, rfl, q1, rw', rfl, q3, rfl, q5, q12.1, q6, q12.2, q4⟩⟩

#print axioms create'
end HeapV2StepCerts.AccShape
