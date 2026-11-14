import MemM1.AccIF
import MemM1.MemReadD2
import MemM1.MemWriteD5
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.AccGPR
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

/-! `CreateAccDescGPR memop nontemporal false tagchecked` (unprivileged GPR load/store) at EL0:
`NewAccDesc AccessType_GPR` (MPAM leg: GenMPAMatEL GPR 0, InD = false, covered by eval's S2MPAM*
summaries), el := EL0, nontemporal, read := memop == LOAD, write := memop == STORE, pan := true,
tagchecked, transactional := (HaveTME && TSTATE.depth > 0) = false when FEAT_TME (bit 227) is off. -/

attribute [-step_summary] S2MPAMMap.complete S2MPAMFields.partidComplete S2MPAMFields.pmgComplete
  S2MPAMCombine.complete
drive_spec gmg_native, gmgEq : fun (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) => GenMPAMatEL .AccessType_GPR 0#2 s
attribute [step_summary] gmgEq

drive_spec nadg_native, nadg_eq : fun (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hEL : s.regs.PSTATE.EL = 0#2) =>
  NewAccDesc .AccessType_GPR s

theorem nadg_frame (s : State) (hEL : s.regs.PSTATE.EL = 0#2) :
    S1AccDescFrame.Frame s (nadg_native s) := by
  observe_simp [S1AccDescFrame.Frame, nadg_native]

theorem nadg_fields (s : State) (acc : AccessDescriptor) (t : State)
    (hEL : s.regs.PSTATE.EL = 0#2)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (h : nadg_native s = .ok acc t) :
    acc.ss = .SS_NonSecure ∧ acc.acctype = .AccessType_GPR ∧ acc.tagaccess = false ∧
      acc.ls64 = false ∧ acc.nonfault = false ∧ acc.firstfault = false ∧
      acc.exclusive = false ∧ acc.atomicop = false ∧ acc.acqsc = false ∧ acc.acqpc = false ∧
      acc.relsc = false := by
  delta nadg_native at h
  injection h with ha ht
  subst ha
  have hns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) = 1#1 := hNS
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  show (if (_get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) == 1#1) = true then
    SecurityState.SS_NonSecure else SecurityState.SS_Secure) = _
  rw [hns]
  rfl

/-- FEAT_TME is bit 227 of FeatureImpl. -/
theorem tme_off (s : State) (h : s.regs.FeatureImpl[227] = false) : HaveTME () s = .ok false s := by
  have h' : (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_TME)]! = false := h
  show EStateM.Result.ok (Register.FeatureImpl.get s.regs)[Int.toNatChecked (num_of_Feature Feature.FEAT_TME)]! s = _
  rw [h']

/-- **AccGPR.create**: the actual `CreateAccDescGPR memop nontemporal false tagchecked` (unprivileged)
    at EL0 (AArch64 EL0, EL3 AArch64-only, RME off, SCR_EL3.NS = 1, FEAT_TME off) returns an access
    with `Acc0`, `AccDR2` (read side), `AccDWT` (write side), `read = (memop == LOAD)`,
    `write = (memop == STORE)`, `tagchecked = tagchecked`, and changes neither registers, memory
    nor events (only choice bookkeeping). -/
theorem create (s : State) (memop : ArmFull.MemOp) (nontemporal tagchecked : Bool)
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
      acc.tagchecked = tagchecked ∧ Frame s t := by
  have hn : NewAccDesc .AccessType_GPR s = nadg_native s :=
    nadg_eq s hNoRME hA64 hEL3A64 hNoEL3A32 hEL
  have hf := nadg_frame s hEL
  cases hr : nadg_native s with
  | error e t => rw [hr] at hf; exact hf.elim
  | ok a0 t0 =>
    rw [hr] at hf
    rcases nadg_fields s a0 t0 hEL hNS hr with ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩
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
    exact ⟨acc, t0, hc, hA0, ⟨q2, rfl, q7, q8, q9, q10, q11⟩, ⟨hA0, q7, q8, q9, q10, q11⟩, rfl, rfl, rfl,
      hf.1, hf.2.1, hf.2.2.1⟩

#print axioms nadg_frame
#print axioms nadg_fields
#print axioms tme_off
#print axioms create
end MemM1.AccGPR
