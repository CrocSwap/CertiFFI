import CryptoMem.MemCore
import MemM1.MemReadDBE
import CryptoMem.Tac
import CryptoMem.Tac2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
namespace CryptoMem.PairNative
abbrev State := SequentialState Regs oracleChoiceSource
open S1Normality

theorem spread (s : State) (hEL : s.regs.PSTATE.EL = 0#2) : SP_read () s = .ok s.regs.SP_EL0 s := by
  have rdP : (readReg PSTATE : SailM ProcState) s = .ok s.regs.PSTATE s := rfl
  have rdS : (readReg SP_EL0 : SailM (BitVec 64)) s = .ok s.regs.SP_EL0 s := rfl
  unfold SP_read
  simp only [bind, EStateM.bind, rdP]
  by_cases h : s.regs.PSTATE.SP = 0#1
  · simp [h, rdS]
  · simp [h, hEL, rdP, rdS, EL0, EStateM.bind]

drive_spec cspa_native, cspa_eq : fun (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2) (hnRW : s.regs.PSTATE.nRW = 0#1)
    (hR : s.regs.FeatureImpl[232] = false) (hVHE : s.regs.FeatureImpl[54] = true)
    (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hE2H : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1)
    (hTGE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1) =>
  SCTLR_read__1 () s

theorem sctlr_ok (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2) (hnRW : s.regs.PSTATE.nRW = 0#1)
    (hR : s.regs.FeatureImpl[232] = false) (hVHE : s.regs.FeatureImpl[54] = true)
    (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hE2H : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1)
    (hTGE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1) :
    ∃ v t, SCTLR_read__1 () s = .ok v t ∧ Frame s t := by
  rw [cspa_eq s hEL hnRW hR hVHE hAA hNS hE2H hTGE]
  observe_simp [Frame, cspa_native]
  first
    | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
    | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
    | (refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩; simp)

theorem cspa_ok (s : State)
    (hEL : s.regs.PSTATE.EL = 0#2) (hnRW : s.regs.PSTATE.nRW = 0#1)
    (hR : s.regs.FeatureImpl[232] = false) (hVHE : s.regs.FeatureImpl[54] = true)
    (hAA : s.regs.FeatureImpl[4] = true)
    (hNS : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.SCR_EL3) 0 0 = 1#1)
    (hE2H : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 34 34 = 1#1)
    (hTGE : Sail.BitVec.extractLsb (s.regs.bank_BitVec_64 Bank_BitVec_64.HCR_EL2) 27 27 = 1#1)
    (hsp : s.regs.SP_EL0.toNat % 16 = 0) :
    ∃ t, Functions.CheckSPAlignment () s = .ok () t ∧ Frame s t := by
  unfold Functions.CheckSPAlignment
  simp only [bind, EStateM.bind, spread s hEL]
  simp (config := {decide := true}) only [PreSail.internal_pick_at,
    PreSail.chooseAt, PreSail.choose, PreSail.occLabel, PreSail.undefined_bool_at, PreSail.undefined_bitvector_at,
    undefined_bool, modifyGet, Functor.map, EStateM.map, MonadStateOf.modifyGet,
    EStateM.modifyGet, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, bind, EStateM.bind]
  have rdP : ∀ st : State, (readReg PSTATE : SailM ProcState) st = .ok st.regs.PSTATE st := fun _ => rfl
  simp only [rdP, hEL]
  simp (config := {decide := true}) only [EL0, beq_self_eq_true, ite_true]
  simp only [EStateM.bind]
  name_app_state SCTLR_read__1 2 as u
  obtain ⟨v, t, hs, hf⟩ := sctlr_ok u (by subst hu; exact hEL) (by subst hu; exact hnRW) (by subst hu; exact hR)
    (by subst hu; exact hVHE) (by subst hu; exact hAA) (by subst hu; exact hNS) (by subst hu; exact hE2H)
    (by subst hu; exact hTGE)
  have hA : Align_bits s.regs.SP_EL0 16 = s.regs.SP_EL0 := by
    unfold Align_bits
    apply BitVec.eq_of_toNat_eq
    simp [Slice_int, Align_int, BitVec.toNatInt, BitVec.castWidth, BitVec.length]
    have he : fdiv_int (↑s.regs.SP_EL0.toNat) 16 * 16 = (↑s.regs.SP_EL0.toNat : Int) := by
      unfold fdiv_int
      first
        | (rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; omega)
        | (simp [Int.fdiv]; omega)
        | omega
    rw [he]
    simp [get_slice_int]
    exact s.regs.SP_EL0.isLt
  simp only [EStateM.bind, hs, EStateM.pure, hA, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false]
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨t, rfl, ?_, ?_, ?_⟩
  · rw [h1]; subst hu; rfl
  · rw [h2]; subst hu; rfl
  · rw [h3]; subst hu; rfl

#print axioms spread
#print axioms cspa_eq
#print axioms sctlr_ok
#print axioms cspa_ok
end CryptoMem.PairNative
