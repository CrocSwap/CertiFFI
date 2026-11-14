import MemM1.M1CoreIF
import MemM1.AccIFp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace MemM1.AccIF
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

/-! `CreateAccDescIFetch ()` = `NewAccDesc AccessType_IFETCH`: acctype := IFETCH,
el := PSTATE.EL, ss := SecurityStateAtEL PSTATE.EL, every flag (ls64, transactional, nonfault,
firstfault, tagaccess, read, write, pan, ...) := false, mpam := GenMPAMcurEL IFETCH
(= GenMPAMatEL IFETCH PSTATE.EL, InD = true). -/

attribute [-step_summary] S2MPAMMap.complete S2MPAMFields.partidComplete S2MPAMFields.pmgComplete
  S2MPAMCombine.complete
drive_spec gm_native, gmEq : fun (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false) => GenMPAMatEL .AccessType_IFETCH 0#2 s
attribute [step_summary] gmEq

drive_spec nad_native, nad_eq : fun (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hEL : s.regs.PSTATE.EL = 0#2) =>
  NewAccDesc .AccessType_IFETCH s

theorem nad_frame (s : State) (hEL : s.regs.PSTATE.EL = 0#2) :
    S1AccDescFrame.Frame s (nad_native s) := by
  observe_simp [S1AccDescFrame.Frame, nad_native]

theorem nad_fields (s : State) (acc : AccessDescriptor) (t : State)
    (hEL : s.regs.PSTATE.EL = 0#2)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (h : nad_native s = .ok acc t) :
    MemM1.WitnessIF.AccIF acc ∧ acc.el = s.regs.PSTATE.EL ∧ acc.tagaccess = false ∧
      acc.read = false ∧ acc.write = false ∧ acc.pan = false := by
  delta nad_native at h
  injection h with ha ht
  subst ha
  have hns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) = 1#1 := hNS
  refine ⟨⟨?_, hEL, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
  show (if (_get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) == 1#1) = true then
    SecurityState.SS_NonSecure else SecurityState.SS_Secure) = _
  rw [hns]
  rfl

/-- Part 1 of M-a: the actual `CreateAccDescIFetch ()` at EL0 (AArch64 EL0, EL3 AArch64-only,
    RME off, SCR_EL3.NS = 1) returns an access satisfying `AccIF` (acctype IFETCH, el = PSTATE.EL
    = 0, ss = NonSecure, ls64/transactional/nonfault/firstfault/tagaccess/read/write/pan all
    false), and touches neither registers, memory nor events (only choice bookkeeping). -/
theorem create (s : State)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hA64 : s.regs.PSTATE.nRW = 0#1)
    (hEL3A64 : s.regs.FeatureImpl[7] = true)
    (hNoEL3A32 : s.regs.FeatureImpl[3] = false)
    (hEL : s.regs.PSTATE.EL = 0#2)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1) :
    ∃ acc t, CreateAccDescIFetch () s = .ok acc t ∧ MemM1.WitnessIF.AccIF acc ∧
      acc.el = s.regs.PSTATE.EL ∧ acc.tagaccess = false ∧ acc.read = false ∧
      acc.write = false ∧ acc.pan = false ∧ Frame s t := by
  have hc : CreateAccDescIFetch () s = nad_native s := nad_eq s hNoRME hA64 hEL3A64 hNoEL3A32 hEL
  have hf := nad_frame s hEL
  cases hr : nad_native s with
  | error e t => rw [hr] at hf; exact hf.elim
  | ok acc t =>
    rw [hr] at hf
    rcases nad_fields s acc t hEL hNS hr with ⟨hA, a1, a2, a3, a4, a5⟩
    exact ⟨acc, t, hc.trans hr, hA, a1, a2, a3, a4, a5, hf.1, hf.2.1, hf.2.2.1⟩

#print axioms nad_frame
#print axioms nad_fields
#print axioms create

end MemM1.AccIF
