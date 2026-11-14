import CryptoMem.LdstPairDecode
import ArmFull.Fn.M1468
import ArmFull.Fn.M1423
import ArmFull.Fn.M1424
import ArmFull.Fn.M1425
import ArmFull.Fn.M1426
import ArmFull.Fn.M1427
import ArmFull.Fn.M1428
import ArmFull.Fn.M1429
import ArmFull.Fn.M1430
import ArmFull.Fn.M1431
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
namespace ArmCertMem.Disp
variable (real : Type) [Sail.SailReal real]

theorem disp_stp_gen_h0 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 22 21) : BitVec 2) = 2#2) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h0b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 22 21) : BitVec 2) == 2#2) = false := by
  have := disp_stp_gen_h0 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h1 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 22 21) : BitVec 2) = 3#2) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h1b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 22 21) : BitVec 2) == 3#2) = false := by
  have := disp_stp_gen_h1 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h2 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 22 22) : BitVec 1) = 0#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_stp_gen_h3 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 22 22) : BitVec 1) = 0#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_stp_gen_h4 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 25 25) : BitVec 1) = 0#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_stp_gen_h5 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 27 25) : BitVec 3) = 4#3 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h6 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 27 27) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_stp_gen_h7 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 28 25) : BitVec 4) = 4#4 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h8 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 28 25) : BitVec 4) = 4#4 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h9 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 28 25) : BitVec 4) = 4#4 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h10 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 28 25) : BitVec 4) = 4#4 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h11 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 28 26) : BitVec 3) = 2#3 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h12 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 28 26) : BitVec 3) = 2#3 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h13 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) = 137183#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h13b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) == 137183#20) = false := by
  have := disp_stp_gen_h13 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h14 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) = 137215#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h14b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) == 137215#20) = false := by
  have := disp_stp_gen_h14 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h15 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) = 141279#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h15b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) == 141279#20) = false := by
  have := disp_stp_gen_h15 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h16 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) = 141311#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h16b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) == 141311#20) = false := by
  have := disp_stp_gen_h16 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h17 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) = 145375#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h17b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) == 145375#20) = false := by
  have := disp_stp_gen_h17 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h18 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) = 145407#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h18b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) == 145407#20) = false := by
  have := disp_stp_gen_h18 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h19 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) = 213089#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 16) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h19b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) == 213089#20) = false := by
  have := disp_stp_gen_h19 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h20 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) = 217185#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h20b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) == 217185#20) = false := by
  have := disp_stp_gen_h20 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h21 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) = 417794#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h21b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) == 417794#20) = false := by
  have := disp_stp_gen_h21 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h22 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) = 421890#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h22b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) == 421890#20) = false := by
  have := disp_stp_gen_h22 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h23 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) = 929776#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h23b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 10) : BitVec 20) == 929776#20) = false := by
  have := disp_stp_gen_h23 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h24 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) = 49152#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h24b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) == 49152#18) = false := by
  have := disp_stp_gen_h24 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h25 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) = 49156#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h25b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) == 49156#18) = false := by
  have := disp_stp_gen_h25 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h26 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) = 49160#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h26b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) == 49160#18) = false := by
  have := disp_stp_gen_h26 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h27 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) = 50176#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h27b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) == 50176#18) = false := by
  have := disp_stp_gen_h27 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h28 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) = 50180#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h28b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) == 50180#18) = false := by
  have := disp_stp_gen_h28 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h29 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) = 50184#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h29b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) == 50184#18) = false := by
  have := disp_stp_gen_h29 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h30 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) = 54284#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h30b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) == 54284#18) = false := by
  have := disp_stp_gen_h30 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h31 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) = 54286#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h31b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) == 54286#18) = false := by
  have := disp_stp_gen_h31 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h32 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) = 54796#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h32b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) == 54796#18) = false := by
  have := disp_stp_gen_h32 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h33 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) = 54798#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h33b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 12) : BitVec 18) == 54798#18) = false := by
  have := disp_stp_gen_h33 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h34 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 15) : BitVec 15) = 4350#15) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h34b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 15) : BitVec 15) == 4350#15) = false := by
  have := disp_stp_gen_h34 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h35 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 15) : BitVec 15) = 4351#15) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h35b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 15) : BitVec 15) == 4351#15) = false := by
  have := disp_stp_gen_h35 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h36 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) = 3072#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h36b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) == 3072#14) = false := by
  have := disp_stp_gen_h36 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h37 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) = 3136#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h37b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) == 3136#14) = false := by
  have := disp_stp_gen_h37 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h38 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) = 3328#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h38b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) == 3328#14) = false := by
  have := disp_stp_gen_h38 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h39 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) = 3360#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h39b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) == 3360#14) = false := by
  have := disp_stp_gen_h39 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h40 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) = 3392#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h40b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) == 3392#14) = false := by
  have := disp_stp_gen_h40 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h41 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) = 3424#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h41b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 16) : BitVec 14) == 3424#14) = false := by
  have := disp_stp_gen_h41 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h42 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 64#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h42b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 64#9) = false := by
  have := disp_stp_gen_h42 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h43 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 65#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h43b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 65#9) = false := by
  have := disp_stp_gen_h43 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h44 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 100#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h44b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 100#9) = false := by
  have := disp_stp_gen_h44 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h45 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 102#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h45b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 102#9) = false := by
  have := disp_stp_gen_h45 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h46 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 108#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h46b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 108#9) = false := by
  have := disp_stp_gen_h46 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h47 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 109#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h47b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 109#9) = false := by
  have := disp_stp_gen_h47 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h48 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 110#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h48b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 110#9) = false := by
  have := disp_stp_gen_h48 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h49 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 111#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h49b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 111#9) = false := by
  have := disp_stp_gen_h49 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h50 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 200#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h50b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 200#9) = false := by
  have := disp_stp_gen_h50 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h51 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 202#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h51b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 202#9) = false := by
  have := disp_stp_gen_h51 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h52 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 206#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h52b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 206#9) = false := by
  have := disp_stp_gen_h52 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h53 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 238#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h53b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 238#9) = false := by
  have := disp_stp_gen_h53 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h54 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 448#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h54b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 448#9) = false := by
  have := disp_stp_gen_h54 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h55 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 449#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h55b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 449#9) = false := by
  have := disp_stp_gen_h55 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h56 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 450#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h56b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 450#9) = false := by
  have := disp_stp_gen_h56 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h57 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) = 451#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h57b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 21) : BitVec 9) == 451#9) = false := by
  have := disp_stp_gen_h57 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h58 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 22) : BitVec 8) = 164#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h59 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 22) : BitVec 8) = 164#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h60 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 22) : BitVec 8) = 164#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h61 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 22) : BitVec 8) = 164#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h62 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 22) : BitVec 8) = 164#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h63 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 22) : BitVec 8) = 164#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h64 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 22) : BitVec 8) = 164#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h65 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 22) : BitVec 8) = 164#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h66 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 22) : BitVec 8) = 164#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h67 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 22) : BitVec 8) = 164#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h68 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 23) : BitVec 7) = 82#7 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h69 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 23) : BitVec 7) = 82#7 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h70 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h71 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h72 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h73 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h74 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h75 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h76 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h77 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 30 22) : BitVec 9) = 164#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h78 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 30 22) : BitVec 9) = 164#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h79 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 30 22) : BitVec 9) = 164#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h80 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 30 22) : BitVec 9) = 164#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h81 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 30 22) : BitVec 9) = 164#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h82 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 30 22) : BitVec 9) = 164#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h83 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 30 22) : BitVec 9) = 164#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h84 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 30 22) : BitVec 9) = 164#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h85 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 137183#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h85b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 137183#22) = false := by
  have := disp_stp_gen_h85 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h86 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 137215#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h86b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 137215#22) = false := by
  have := disp_stp_gen_h86 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h87 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 141279#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h87b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 141279#22) = false := by
  have := disp_stp_gen_h87 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h88 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 141311#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h88b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 141311#22) = false := by
  have := disp_stp_gen_h88 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h89 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 145375#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h89b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 145375#22) = false := by
  have := disp_stp_gen_h89 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h90 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 145407#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h90b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 145407#22) = false := by
  have := disp_stp_gen_h90 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h91 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 929776#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h91b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 929776#22) = false := by
  have := disp_stp_gen_h91 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h92 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 1185759#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h92b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 1185759#22) = false := by
  have := disp_stp_gen_h92 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h93 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 1185791#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h93b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 1185791#22) = false := by
  have := disp_stp_gen_h93 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h94 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 1189855#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h94b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 1189855#22) = false := by
  have := disp_stp_gen_h94 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h95 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 1189887#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h95b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 1189887#22) = false := by
  have := disp_stp_gen_h95 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h96 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 1193951#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h96b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 1193951#22) = false := by
  have := disp_stp_gen_h96 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h97 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 1193983#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h97b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 1193983#22) = false := by
  have := disp_stp_gen_h97 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h98 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 1978352#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h98b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 1978352#22) = false := by
  have := disp_stp_gen_h98 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h99 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 3557315#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 18) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h99b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 3557315#22) = false := by
  have := disp_stp_gen_h99 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h100 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 3557319#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 18) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h100b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 3557319#22) = false := by
  have := disp_stp_gen_h100 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h101 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 3557376#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 18) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h101b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 3557376#22) = false := by
  have := disp_stp_gen_h101 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h102 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 3565568#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h102b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 3565568#22) = false := by
  have := disp_stp_gen_h102 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h103 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 3569664#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h103b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 3569664#22) = false := by
  have := disp_stp_gen_h103 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h104 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 4067300#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h104b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 4067300#22) = false := by
  have := disp_stp_gen_h104 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h105 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) = 4067316#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h105b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 10) : BitVec 22) == 4067316#22) = false := by
  have := disp_stp_gen_h105 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h106 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 64#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h106b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 64#11) = false := by
  have := disp_stp_gen_h106 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h107 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 200#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h107b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 200#11) = false := by
  have := disp_stp_gen_h107 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h108 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 202#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h108b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 202#11) = false := by
  have := disp_stp_gen_h108 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h109 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 448#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h109b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 448#11) = false := by
  have := disp_stp_gen_h109 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h110 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 449#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h110b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 449#11) = false := by
  have := disp_stp_gen_h110 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h111 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 450#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h111b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 450#11) = false := by
  have := disp_stp_gen_h111 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h112 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 451#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h112b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 451#11) = false := by
  have := disp_stp_gen_h112 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h113 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 576#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h113b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 576#11) = false := by
  have := disp_stp_gen_h113 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h114 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 712#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h114b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 712#11) = false := by
  have := disp_stp_gen_h114 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h115 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 714#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h115b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 714#11) = false := by
  have := disp_stp_gen_h115 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h116 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 960#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h116b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 960#11) = false := by
  have := disp_stp_gen_h116 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h117 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 961#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h117b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 961#11) = false := by
  have := disp_stp_gen_h117 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h118 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 962#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h118b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 962#11) = false := by
  have := disp_stp_gen_h118 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h119 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 963#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h119b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 963#11) = false := by
  have := disp_stp_gen_h119 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h120 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 1228#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h120b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 1228#11) = false := by
  have := disp_stp_gen_h120 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h121 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 1476#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h121b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 1476#11) = false := by
  have := disp_stp_gen_h121 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h122 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 1477#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h122b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 1477#11) = false := by
  have := disp_stp_gen_h122 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h123 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 1737#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h123b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 1737#11) = false := by
  have := disp_stp_gen_h123 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h124 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 1739#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h124b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 1739#11) = false := by
  have := disp_stp_gen_h124 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h125 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 1741#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h125b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 1741#11) = false := by
  have := disp_stp_gen_h125 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h126 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 1743#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h126b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 1743#11) = false := by
  have := disp_stp_gen_h126 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h127 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 1985#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h127b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 1985#11) = false := by
  have := disp_stp_gen_h127 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h128 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 1988#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h128b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 1988#11) = false := by
  have := disp_stp_gen_h128 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h129 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) = 1989#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_stp_gen_h129b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 21) : BitVec 11) == 1989#11) = false := by
  have := disp_stp_gen_h129 imm7 Rt2 Rn Rt
  simpa using this

theorem disp_stp_gen_h130 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h131 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h132 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h133 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h134 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h135 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h136 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h137 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h138 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h139 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h140 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h141 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 22) : BitVec 10) = 676#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h142 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h143 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h144 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h145 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h146 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h147 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h148 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h149 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h150 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h151 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h152 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h153 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h154 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h155 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h156 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_stp_gen_h157 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_stp_gen_h158 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_stp_gen_h159 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 0 5 = Rt := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    bv_field

theorem disp_stp_gen_h160 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 5 5 = Rn := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    bv_field

theorem disp_stp_gen_h161 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 10 5 = Rt2 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    bv_field

theorem disp_stp_gen_h162 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 15 7 = imm7 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    bv_field

theorem disp_stp_gen_h163 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 22 1 = 0#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_stp_gen_h164 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 22 2 = 0#2 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_stp_gen_h165 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 23 1 = 0#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_stp_gen_h166 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 30 1 = 0#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_stp_gen_h167 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) 30 2 = 2#2 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_stp_gen (pc : Int) (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rn : BitVec 5) (Rt : BitVec 5) :
    __DecodeA64 (real := real) pc (CryptoMem.LdstPair.ldstPairOffWord 2#2 0#1 imm7 Rt2 Rn Rt) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 617))
      if c = true then (do writeReg Register.SEE 617; decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  try simp (config := {decide := true}) only [disp_stp_gen_h0, disp_stp_gen_h0b, disp_stp_gen_h1, disp_stp_gen_h1b, disp_stp_gen_h2, disp_stp_gen_h3, disp_stp_gen_h4, disp_stp_gen_h5, disp_stp_gen_h6, disp_stp_gen_h7, disp_stp_gen_h8, disp_stp_gen_h9, disp_stp_gen_h10, disp_stp_gen_h11, disp_stp_gen_h12, disp_stp_gen_h13, disp_stp_gen_h13b, disp_stp_gen_h14, disp_stp_gen_h14b, disp_stp_gen_h15, disp_stp_gen_h15b, disp_stp_gen_h16, disp_stp_gen_h16b, disp_stp_gen_h17, disp_stp_gen_h17b, disp_stp_gen_h18, disp_stp_gen_h18b, disp_stp_gen_h19, disp_stp_gen_h19b, disp_stp_gen_h20, disp_stp_gen_h20b, disp_stp_gen_h21, disp_stp_gen_h21b, disp_stp_gen_h22, disp_stp_gen_h22b, disp_stp_gen_h23, disp_stp_gen_h23b, disp_stp_gen_h24, disp_stp_gen_h24b, disp_stp_gen_h25, disp_stp_gen_h25b, disp_stp_gen_h26, disp_stp_gen_h26b, disp_stp_gen_h27, disp_stp_gen_h27b, disp_stp_gen_h28, disp_stp_gen_h28b, disp_stp_gen_h29, disp_stp_gen_h29b, disp_stp_gen_h30, disp_stp_gen_h30b, disp_stp_gen_h31, disp_stp_gen_h31b, disp_stp_gen_h32, disp_stp_gen_h32b, disp_stp_gen_h33, disp_stp_gen_h33b, disp_stp_gen_h34, disp_stp_gen_h34b, disp_stp_gen_h35, disp_stp_gen_h35b, disp_stp_gen_h36, disp_stp_gen_h36b, disp_stp_gen_h37, disp_stp_gen_h37b, disp_stp_gen_h38, disp_stp_gen_h38b, disp_stp_gen_h39, disp_stp_gen_h39b, disp_stp_gen_h40, disp_stp_gen_h40b, disp_stp_gen_h41, disp_stp_gen_h41b, disp_stp_gen_h42, disp_stp_gen_h42b, disp_stp_gen_h43, disp_stp_gen_h43b, disp_stp_gen_h44, disp_stp_gen_h44b, disp_stp_gen_h45, disp_stp_gen_h45b, disp_stp_gen_h46, disp_stp_gen_h46b, disp_stp_gen_h47, disp_stp_gen_h47b, disp_stp_gen_h48, disp_stp_gen_h48b, disp_stp_gen_h49, disp_stp_gen_h49b, disp_stp_gen_h50, disp_stp_gen_h50b, disp_stp_gen_h51, disp_stp_gen_h51b, disp_stp_gen_h52, disp_stp_gen_h52b, disp_stp_gen_h53, disp_stp_gen_h53b, disp_stp_gen_h54, disp_stp_gen_h54b, disp_stp_gen_h55, disp_stp_gen_h55b, disp_stp_gen_h56, disp_stp_gen_h56b, disp_stp_gen_h57, disp_stp_gen_h57b, disp_stp_gen_h58, disp_stp_gen_h59, disp_stp_gen_h60, disp_stp_gen_h61, disp_stp_gen_h62, disp_stp_gen_h63, disp_stp_gen_h64, disp_stp_gen_h65, disp_stp_gen_h66, disp_stp_gen_h67, disp_stp_gen_h68, disp_stp_gen_h69, disp_stp_gen_h70, disp_stp_gen_h71, disp_stp_gen_h72, disp_stp_gen_h73, disp_stp_gen_h74, disp_stp_gen_h75, disp_stp_gen_h76, disp_stp_gen_h77, disp_stp_gen_h78, disp_stp_gen_h79, disp_stp_gen_h80, disp_stp_gen_h81, disp_stp_gen_h82, disp_stp_gen_h83, disp_stp_gen_h84, disp_stp_gen_h85, disp_stp_gen_h85b, disp_stp_gen_h86, disp_stp_gen_h86b, disp_stp_gen_h87, disp_stp_gen_h87b, disp_stp_gen_h88, disp_stp_gen_h88b, disp_stp_gen_h89, disp_stp_gen_h89b, disp_stp_gen_h90, disp_stp_gen_h90b, disp_stp_gen_h91, disp_stp_gen_h91b, disp_stp_gen_h92, disp_stp_gen_h92b, disp_stp_gen_h93, disp_stp_gen_h93b, disp_stp_gen_h94, disp_stp_gen_h94b, disp_stp_gen_h95, disp_stp_gen_h95b, disp_stp_gen_h96, disp_stp_gen_h96b, disp_stp_gen_h97, disp_stp_gen_h97b, disp_stp_gen_h98, disp_stp_gen_h98b, disp_stp_gen_h99, disp_stp_gen_h99b, disp_stp_gen_h100, disp_stp_gen_h100b, disp_stp_gen_h101, disp_stp_gen_h101b, disp_stp_gen_h102, disp_stp_gen_h102b, disp_stp_gen_h103, disp_stp_gen_h103b, disp_stp_gen_h104, disp_stp_gen_h104b, disp_stp_gen_h105, disp_stp_gen_h105b, disp_stp_gen_h106, disp_stp_gen_h106b, disp_stp_gen_h107, disp_stp_gen_h107b, disp_stp_gen_h108, disp_stp_gen_h108b, disp_stp_gen_h109, disp_stp_gen_h109b, disp_stp_gen_h110, disp_stp_gen_h110b, disp_stp_gen_h111, disp_stp_gen_h111b, disp_stp_gen_h112, disp_stp_gen_h112b, disp_stp_gen_h113, disp_stp_gen_h113b, disp_stp_gen_h114, disp_stp_gen_h114b, disp_stp_gen_h115, disp_stp_gen_h115b, disp_stp_gen_h116, disp_stp_gen_h116b, disp_stp_gen_h117, disp_stp_gen_h117b, disp_stp_gen_h118, disp_stp_gen_h118b, disp_stp_gen_h119, disp_stp_gen_h119b, disp_stp_gen_h120, disp_stp_gen_h120b, disp_stp_gen_h121, disp_stp_gen_h121b, disp_stp_gen_h122, disp_stp_gen_h122b, disp_stp_gen_h123, disp_stp_gen_h123b, disp_stp_gen_h124, disp_stp_gen_h124b, disp_stp_gen_h125, disp_stp_gen_h125b, disp_stp_gen_h126, disp_stp_gen_h126b, disp_stp_gen_h127, disp_stp_gen_h127b, disp_stp_gen_h128, disp_stp_gen_h128b, disp_stp_gen_h129, disp_stp_gen_h129b, disp_stp_gen_h130, disp_stp_gen_h131, disp_stp_gen_h132, disp_stp_gen_h133, disp_stp_gen_h134, disp_stp_gen_h135, disp_stp_gen_h136, disp_stp_gen_h137, disp_stp_gen_h138, disp_stp_gen_h139, disp_stp_gen_h140, disp_stp_gen_h141, disp_stp_gen_h142, disp_stp_gen_h143, disp_stp_gen_h144, disp_stp_gen_h145, disp_stp_gen_h146, disp_stp_gen_h147, disp_stp_gen_h148, disp_stp_gen_h149, disp_stp_gen_h150, disp_stp_gen_h151, disp_stp_gen_h152, disp_stp_gen_h153, disp_stp_gen_h154, disp_stp_gen_h155, disp_stp_gen_h156, disp_stp_gen_h157, disp_stp_gen_h158, disp_stp_gen_h159, disp_stp_gen_h160, disp_stp_gen_h161, disp_stp_gen_h162, disp_stp_gen_h163, disp_stp_gen_h164, disp_stp_gen_h165, disp_stp_gen_h166, disp_stp_gen_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore
  try simp (config := {decide := true}) only [disp_stp_gen_h0, disp_stp_gen_h0b, disp_stp_gen_h1, disp_stp_gen_h1b, disp_stp_gen_h2, disp_stp_gen_h3, disp_stp_gen_h4, disp_stp_gen_h5, disp_stp_gen_h6, disp_stp_gen_h7, disp_stp_gen_h8, disp_stp_gen_h9, disp_stp_gen_h10, disp_stp_gen_h11, disp_stp_gen_h12, disp_stp_gen_h13, disp_stp_gen_h13b, disp_stp_gen_h14, disp_stp_gen_h14b, disp_stp_gen_h15, disp_stp_gen_h15b, disp_stp_gen_h16, disp_stp_gen_h16b, disp_stp_gen_h17, disp_stp_gen_h17b, disp_stp_gen_h18, disp_stp_gen_h18b, disp_stp_gen_h19, disp_stp_gen_h19b, disp_stp_gen_h20, disp_stp_gen_h20b, disp_stp_gen_h21, disp_stp_gen_h21b, disp_stp_gen_h22, disp_stp_gen_h22b, disp_stp_gen_h23, disp_stp_gen_h23b, disp_stp_gen_h24, disp_stp_gen_h24b, disp_stp_gen_h25, disp_stp_gen_h25b, disp_stp_gen_h26, disp_stp_gen_h26b, disp_stp_gen_h27, disp_stp_gen_h27b, disp_stp_gen_h28, disp_stp_gen_h28b, disp_stp_gen_h29, disp_stp_gen_h29b, disp_stp_gen_h30, disp_stp_gen_h30b, disp_stp_gen_h31, disp_stp_gen_h31b, disp_stp_gen_h32, disp_stp_gen_h32b, disp_stp_gen_h33, disp_stp_gen_h33b, disp_stp_gen_h34, disp_stp_gen_h34b, disp_stp_gen_h35, disp_stp_gen_h35b, disp_stp_gen_h36, disp_stp_gen_h36b, disp_stp_gen_h37, disp_stp_gen_h37b, disp_stp_gen_h38, disp_stp_gen_h38b, disp_stp_gen_h39, disp_stp_gen_h39b, disp_stp_gen_h40, disp_stp_gen_h40b, disp_stp_gen_h41, disp_stp_gen_h41b, disp_stp_gen_h42, disp_stp_gen_h42b, disp_stp_gen_h43, disp_stp_gen_h43b, disp_stp_gen_h44, disp_stp_gen_h44b, disp_stp_gen_h45, disp_stp_gen_h45b, disp_stp_gen_h46, disp_stp_gen_h46b, disp_stp_gen_h47, disp_stp_gen_h47b, disp_stp_gen_h48, disp_stp_gen_h48b, disp_stp_gen_h49, disp_stp_gen_h49b, disp_stp_gen_h50, disp_stp_gen_h50b, disp_stp_gen_h51, disp_stp_gen_h51b, disp_stp_gen_h52, disp_stp_gen_h52b, disp_stp_gen_h53, disp_stp_gen_h53b, disp_stp_gen_h54, disp_stp_gen_h54b, disp_stp_gen_h55, disp_stp_gen_h55b, disp_stp_gen_h56, disp_stp_gen_h56b, disp_stp_gen_h57, disp_stp_gen_h57b, disp_stp_gen_h58, disp_stp_gen_h59, disp_stp_gen_h60, disp_stp_gen_h61, disp_stp_gen_h62, disp_stp_gen_h63, disp_stp_gen_h64, disp_stp_gen_h65, disp_stp_gen_h66, disp_stp_gen_h67, disp_stp_gen_h68, disp_stp_gen_h69, disp_stp_gen_h70, disp_stp_gen_h71, disp_stp_gen_h72, disp_stp_gen_h73, disp_stp_gen_h74, disp_stp_gen_h75, disp_stp_gen_h76, disp_stp_gen_h77, disp_stp_gen_h78, disp_stp_gen_h79, disp_stp_gen_h80, disp_stp_gen_h81, disp_stp_gen_h82, disp_stp_gen_h83, disp_stp_gen_h84, disp_stp_gen_h85, disp_stp_gen_h85b, disp_stp_gen_h86, disp_stp_gen_h86b, disp_stp_gen_h87, disp_stp_gen_h87b, disp_stp_gen_h88, disp_stp_gen_h88b, disp_stp_gen_h89, disp_stp_gen_h89b, disp_stp_gen_h90, disp_stp_gen_h90b, disp_stp_gen_h91, disp_stp_gen_h91b, disp_stp_gen_h92, disp_stp_gen_h92b, disp_stp_gen_h93, disp_stp_gen_h93b, disp_stp_gen_h94, disp_stp_gen_h94b, disp_stp_gen_h95, disp_stp_gen_h95b, disp_stp_gen_h96, disp_stp_gen_h96b, disp_stp_gen_h97, disp_stp_gen_h97b, disp_stp_gen_h98, disp_stp_gen_h98b, disp_stp_gen_h99, disp_stp_gen_h99b, disp_stp_gen_h100, disp_stp_gen_h100b, disp_stp_gen_h101, disp_stp_gen_h101b, disp_stp_gen_h102, disp_stp_gen_h102b, disp_stp_gen_h103, disp_stp_gen_h103b, disp_stp_gen_h104, disp_stp_gen_h104b, disp_stp_gen_h105, disp_stp_gen_h105b, disp_stp_gen_h106, disp_stp_gen_h106b, disp_stp_gen_h107, disp_stp_gen_h107b, disp_stp_gen_h108, disp_stp_gen_h108b, disp_stp_gen_h109, disp_stp_gen_h109b, disp_stp_gen_h110, disp_stp_gen_h110b, disp_stp_gen_h111, disp_stp_gen_h111b, disp_stp_gen_h112, disp_stp_gen_h112b, disp_stp_gen_h113, disp_stp_gen_h113b, disp_stp_gen_h114, disp_stp_gen_h114b, disp_stp_gen_h115, disp_stp_gen_h115b, disp_stp_gen_h116, disp_stp_gen_h116b, disp_stp_gen_h117, disp_stp_gen_h117b, disp_stp_gen_h118, disp_stp_gen_h118b, disp_stp_gen_h119, disp_stp_gen_h119b, disp_stp_gen_h120, disp_stp_gen_h120b, disp_stp_gen_h121, disp_stp_gen_h121b, disp_stp_gen_h122, disp_stp_gen_h122b, disp_stp_gen_h123, disp_stp_gen_h123b, disp_stp_gen_h124, disp_stp_gen_h124b, disp_stp_gen_h125, disp_stp_gen_h125b, disp_stp_gen_h126, disp_stp_gen_h126b, disp_stp_gen_h127, disp_stp_gen_h127b, disp_stp_gen_h128, disp_stp_gen_h128b, disp_stp_gen_h129, disp_stp_gen_h129b, disp_stp_gen_h130, disp_stp_gen_h131, disp_stp_gen_h132, disp_stp_gen_h133, disp_stp_gen_h134, disp_stp_gen_h135, disp_stp_gen_h136, disp_stp_gen_h137, disp_stp_gen_h138, disp_stp_gen_h139, disp_stp_gen_h140, disp_stp_gen_h141, disp_stp_gen_h142, disp_stp_gen_h143, disp_stp_gen_h144, disp_stp_gen_h145, disp_stp_gen_h146, disp_stp_gen_h147, disp_stp_gen_h148, disp_stp_gen_h149, disp_stp_gen_h150, disp_stp_gen_h151, disp_stp_gen_h152, disp_stp_gen_h153, disp_stp_gen_h154, disp_stp_gen_h155, disp_stp_gen_h156, disp_stp_gen_h157, disp_stp_gen_h158, disp_stp_gen_h159, disp_stp_gen_h160, disp_stp_gen_h161, disp_stp_gen_h162, disp_stp_gen_h163, disp_stp_gen_h164, disp_stp_gen_h165, disp_stp_gen_h166, disp_stp_gen_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg0
  try simp (config := {decide := true}) only [disp_stp_gen_h0, disp_stp_gen_h0b, disp_stp_gen_h1, disp_stp_gen_h1b, disp_stp_gen_h2, disp_stp_gen_h3, disp_stp_gen_h4, disp_stp_gen_h5, disp_stp_gen_h6, disp_stp_gen_h7, disp_stp_gen_h8, disp_stp_gen_h9, disp_stp_gen_h10, disp_stp_gen_h11, disp_stp_gen_h12, disp_stp_gen_h13, disp_stp_gen_h13b, disp_stp_gen_h14, disp_stp_gen_h14b, disp_stp_gen_h15, disp_stp_gen_h15b, disp_stp_gen_h16, disp_stp_gen_h16b, disp_stp_gen_h17, disp_stp_gen_h17b, disp_stp_gen_h18, disp_stp_gen_h18b, disp_stp_gen_h19, disp_stp_gen_h19b, disp_stp_gen_h20, disp_stp_gen_h20b, disp_stp_gen_h21, disp_stp_gen_h21b, disp_stp_gen_h22, disp_stp_gen_h22b, disp_stp_gen_h23, disp_stp_gen_h23b, disp_stp_gen_h24, disp_stp_gen_h24b, disp_stp_gen_h25, disp_stp_gen_h25b, disp_stp_gen_h26, disp_stp_gen_h26b, disp_stp_gen_h27, disp_stp_gen_h27b, disp_stp_gen_h28, disp_stp_gen_h28b, disp_stp_gen_h29, disp_stp_gen_h29b, disp_stp_gen_h30, disp_stp_gen_h30b, disp_stp_gen_h31, disp_stp_gen_h31b, disp_stp_gen_h32, disp_stp_gen_h32b, disp_stp_gen_h33, disp_stp_gen_h33b, disp_stp_gen_h34, disp_stp_gen_h34b, disp_stp_gen_h35, disp_stp_gen_h35b, disp_stp_gen_h36, disp_stp_gen_h36b, disp_stp_gen_h37, disp_stp_gen_h37b, disp_stp_gen_h38, disp_stp_gen_h38b, disp_stp_gen_h39, disp_stp_gen_h39b, disp_stp_gen_h40, disp_stp_gen_h40b, disp_stp_gen_h41, disp_stp_gen_h41b, disp_stp_gen_h42, disp_stp_gen_h42b, disp_stp_gen_h43, disp_stp_gen_h43b, disp_stp_gen_h44, disp_stp_gen_h44b, disp_stp_gen_h45, disp_stp_gen_h45b, disp_stp_gen_h46, disp_stp_gen_h46b, disp_stp_gen_h47, disp_stp_gen_h47b, disp_stp_gen_h48, disp_stp_gen_h48b, disp_stp_gen_h49, disp_stp_gen_h49b, disp_stp_gen_h50, disp_stp_gen_h50b, disp_stp_gen_h51, disp_stp_gen_h51b, disp_stp_gen_h52, disp_stp_gen_h52b, disp_stp_gen_h53, disp_stp_gen_h53b, disp_stp_gen_h54, disp_stp_gen_h54b, disp_stp_gen_h55, disp_stp_gen_h55b, disp_stp_gen_h56, disp_stp_gen_h56b, disp_stp_gen_h57, disp_stp_gen_h57b, disp_stp_gen_h58, disp_stp_gen_h59, disp_stp_gen_h60, disp_stp_gen_h61, disp_stp_gen_h62, disp_stp_gen_h63, disp_stp_gen_h64, disp_stp_gen_h65, disp_stp_gen_h66, disp_stp_gen_h67, disp_stp_gen_h68, disp_stp_gen_h69, disp_stp_gen_h70, disp_stp_gen_h71, disp_stp_gen_h72, disp_stp_gen_h73, disp_stp_gen_h74, disp_stp_gen_h75, disp_stp_gen_h76, disp_stp_gen_h77, disp_stp_gen_h78, disp_stp_gen_h79, disp_stp_gen_h80, disp_stp_gen_h81, disp_stp_gen_h82, disp_stp_gen_h83, disp_stp_gen_h84, disp_stp_gen_h85, disp_stp_gen_h85b, disp_stp_gen_h86, disp_stp_gen_h86b, disp_stp_gen_h87, disp_stp_gen_h87b, disp_stp_gen_h88, disp_stp_gen_h88b, disp_stp_gen_h89, disp_stp_gen_h89b, disp_stp_gen_h90, disp_stp_gen_h90b, disp_stp_gen_h91, disp_stp_gen_h91b, disp_stp_gen_h92, disp_stp_gen_h92b, disp_stp_gen_h93, disp_stp_gen_h93b, disp_stp_gen_h94, disp_stp_gen_h94b, disp_stp_gen_h95, disp_stp_gen_h95b, disp_stp_gen_h96, disp_stp_gen_h96b, disp_stp_gen_h97, disp_stp_gen_h97b, disp_stp_gen_h98, disp_stp_gen_h98b, disp_stp_gen_h99, disp_stp_gen_h99b, disp_stp_gen_h100, disp_stp_gen_h100b, disp_stp_gen_h101, disp_stp_gen_h101b, disp_stp_gen_h102, disp_stp_gen_h102b, disp_stp_gen_h103, disp_stp_gen_h103b, disp_stp_gen_h104, disp_stp_gen_h104b, disp_stp_gen_h105, disp_stp_gen_h105b, disp_stp_gen_h106, disp_stp_gen_h106b, disp_stp_gen_h107, disp_stp_gen_h107b, disp_stp_gen_h108, disp_stp_gen_h108b, disp_stp_gen_h109, disp_stp_gen_h109b, disp_stp_gen_h110, disp_stp_gen_h110b, disp_stp_gen_h111, disp_stp_gen_h111b, disp_stp_gen_h112, disp_stp_gen_h112b, disp_stp_gen_h113, disp_stp_gen_h113b, disp_stp_gen_h114, disp_stp_gen_h114b, disp_stp_gen_h115, disp_stp_gen_h115b, disp_stp_gen_h116, disp_stp_gen_h116b, disp_stp_gen_h117, disp_stp_gen_h117b, disp_stp_gen_h118, disp_stp_gen_h118b, disp_stp_gen_h119, disp_stp_gen_h119b, disp_stp_gen_h120, disp_stp_gen_h120b, disp_stp_gen_h121, disp_stp_gen_h121b, disp_stp_gen_h122, disp_stp_gen_h122b, disp_stp_gen_h123, disp_stp_gen_h123b, disp_stp_gen_h124, disp_stp_gen_h124b, disp_stp_gen_h125, disp_stp_gen_h125b, disp_stp_gen_h126, disp_stp_gen_h126b, disp_stp_gen_h127, disp_stp_gen_h127b, disp_stp_gen_h128, disp_stp_gen_h128b, disp_stp_gen_h129, disp_stp_gen_h129b, disp_stp_gen_h130, disp_stp_gen_h131, disp_stp_gen_h132, disp_stp_gen_h133, disp_stp_gen_h134, disp_stp_gen_h135, disp_stp_gen_h136, disp_stp_gen_h137, disp_stp_gen_h138, disp_stp_gen_h139, disp_stp_gen_h140, disp_stp_gen_h141, disp_stp_gen_h142, disp_stp_gen_h143, disp_stp_gen_h144, disp_stp_gen_h145, disp_stp_gen_h146, disp_stp_gen_h147, disp_stp_gen_h148, disp_stp_gen_h149, disp_stp_gen_h150, disp_stp_gen_h151, disp_stp_gen_h152, disp_stp_gen_h153, disp_stp_gen_h154, disp_stp_gen_h155, disp_stp_gen_h156, disp_stp_gen_h157, disp_stp_gen_h158, disp_stp_gen_h159, disp_stp_gen_h160, disp_stp_gen_h161, disp_stp_gen_h162, disp_stp_gen_h163, disp_stp_gen_h164, disp_stp_gen_h165, disp_stp_gen_h166, disp_stp_gen_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg1
  try simp (config := {decide := true}) only [disp_stp_gen_h0, disp_stp_gen_h0b, disp_stp_gen_h1, disp_stp_gen_h1b, disp_stp_gen_h2, disp_stp_gen_h3, disp_stp_gen_h4, disp_stp_gen_h5, disp_stp_gen_h6, disp_stp_gen_h7, disp_stp_gen_h8, disp_stp_gen_h9, disp_stp_gen_h10, disp_stp_gen_h11, disp_stp_gen_h12, disp_stp_gen_h13, disp_stp_gen_h13b, disp_stp_gen_h14, disp_stp_gen_h14b, disp_stp_gen_h15, disp_stp_gen_h15b, disp_stp_gen_h16, disp_stp_gen_h16b, disp_stp_gen_h17, disp_stp_gen_h17b, disp_stp_gen_h18, disp_stp_gen_h18b, disp_stp_gen_h19, disp_stp_gen_h19b, disp_stp_gen_h20, disp_stp_gen_h20b, disp_stp_gen_h21, disp_stp_gen_h21b, disp_stp_gen_h22, disp_stp_gen_h22b, disp_stp_gen_h23, disp_stp_gen_h23b, disp_stp_gen_h24, disp_stp_gen_h24b, disp_stp_gen_h25, disp_stp_gen_h25b, disp_stp_gen_h26, disp_stp_gen_h26b, disp_stp_gen_h27, disp_stp_gen_h27b, disp_stp_gen_h28, disp_stp_gen_h28b, disp_stp_gen_h29, disp_stp_gen_h29b, disp_stp_gen_h30, disp_stp_gen_h30b, disp_stp_gen_h31, disp_stp_gen_h31b, disp_stp_gen_h32, disp_stp_gen_h32b, disp_stp_gen_h33, disp_stp_gen_h33b, disp_stp_gen_h34, disp_stp_gen_h34b, disp_stp_gen_h35, disp_stp_gen_h35b, disp_stp_gen_h36, disp_stp_gen_h36b, disp_stp_gen_h37, disp_stp_gen_h37b, disp_stp_gen_h38, disp_stp_gen_h38b, disp_stp_gen_h39, disp_stp_gen_h39b, disp_stp_gen_h40, disp_stp_gen_h40b, disp_stp_gen_h41, disp_stp_gen_h41b, disp_stp_gen_h42, disp_stp_gen_h42b, disp_stp_gen_h43, disp_stp_gen_h43b, disp_stp_gen_h44, disp_stp_gen_h44b, disp_stp_gen_h45, disp_stp_gen_h45b, disp_stp_gen_h46, disp_stp_gen_h46b, disp_stp_gen_h47, disp_stp_gen_h47b, disp_stp_gen_h48, disp_stp_gen_h48b, disp_stp_gen_h49, disp_stp_gen_h49b, disp_stp_gen_h50, disp_stp_gen_h50b, disp_stp_gen_h51, disp_stp_gen_h51b, disp_stp_gen_h52, disp_stp_gen_h52b, disp_stp_gen_h53, disp_stp_gen_h53b, disp_stp_gen_h54, disp_stp_gen_h54b, disp_stp_gen_h55, disp_stp_gen_h55b, disp_stp_gen_h56, disp_stp_gen_h56b, disp_stp_gen_h57, disp_stp_gen_h57b, disp_stp_gen_h58, disp_stp_gen_h59, disp_stp_gen_h60, disp_stp_gen_h61, disp_stp_gen_h62, disp_stp_gen_h63, disp_stp_gen_h64, disp_stp_gen_h65, disp_stp_gen_h66, disp_stp_gen_h67, disp_stp_gen_h68, disp_stp_gen_h69, disp_stp_gen_h70, disp_stp_gen_h71, disp_stp_gen_h72, disp_stp_gen_h73, disp_stp_gen_h74, disp_stp_gen_h75, disp_stp_gen_h76, disp_stp_gen_h77, disp_stp_gen_h78, disp_stp_gen_h79, disp_stp_gen_h80, disp_stp_gen_h81, disp_stp_gen_h82, disp_stp_gen_h83, disp_stp_gen_h84, disp_stp_gen_h85, disp_stp_gen_h85b, disp_stp_gen_h86, disp_stp_gen_h86b, disp_stp_gen_h87, disp_stp_gen_h87b, disp_stp_gen_h88, disp_stp_gen_h88b, disp_stp_gen_h89, disp_stp_gen_h89b, disp_stp_gen_h90, disp_stp_gen_h90b, disp_stp_gen_h91, disp_stp_gen_h91b, disp_stp_gen_h92, disp_stp_gen_h92b, disp_stp_gen_h93, disp_stp_gen_h93b, disp_stp_gen_h94, disp_stp_gen_h94b, disp_stp_gen_h95, disp_stp_gen_h95b, disp_stp_gen_h96, disp_stp_gen_h96b, disp_stp_gen_h97, disp_stp_gen_h97b, disp_stp_gen_h98, disp_stp_gen_h98b, disp_stp_gen_h99, disp_stp_gen_h99b, disp_stp_gen_h100, disp_stp_gen_h100b, disp_stp_gen_h101, disp_stp_gen_h101b, disp_stp_gen_h102, disp_stp_gen_h102b, disp_stp_gen_h103, disp_stp_gen_h103b, disp_stp_gen_h104, disp_stp_gen_h104b, disp_stp_gen_h105, disp_stp_gen_h105b, disp_stp_gen_h106, disp_stp_gen_h106b, disp_stp_gen_h107, disp_stp_gen_h107b, disp_stp_gen_h108, disp_stp_gen_h108b, disp_stp_gen_h109, disp_stp_gen_h109b, disp_stp_gen_h110, disp_stp_gen_h110b, disp_stp_gen_h111, disp_stp_gen_h111b, disp_stp_gen_h112, disp_stp_gen_h112b, disp_stp_gen_h113, disp_stp_gen_h113b, disp_stp_gen_h114, disp_stp_gen_h114b, disp_stp_gen_h115, disp_stp_gen_h115b, disp_stp_gen_h116, disp_stp_gen_h116b, disp_stp_gen_h117, disp_stp_gen_h117b, disp_stp_gen_h118, disp_stp_gen_h118b, disp_stp_gen_h119, disp_stp_gen_h119b, disp_stp_gen_h120, disp_stp_gen_h120b, disp_stp_gen_h121, disp_stp_gen_h121b, disp_stp_gen_h122, disp_stp_gen_h122b, disp_stp_gen_h123, disp_stp_gen_h123b, disp_stp_gen_h124, disp_stp_gen_h124b, disp_stp_gen_h125, disp_stp_gen_h125b, disp_stp_gen_h126, disp_stp_gen_h126b, disp_stp_gen_h127, disp_stp_gen_h127b, disp_stp_gen_h128, disp_stp_gen_h128b, disp_stp_gen_h129, disp_stp_gen_h129b, disp_stp_gen_h130, disp_stp_gen_h131, disp_stp_gen_h132, disp_stp_gen_h133, disp_stp_gen_h134, disp_stp_gen_h135, disp_stp_gen_h136, disp_stp_gen_h137, disp_stp_gen_h138, disp_stp_gen_h139, disp_stp_gen_h140, disp_stp_gen_h141, disp_stp_gen_h142, disp_stp_gen_h143, disp_stp_gen_h144, disp_stp_gen_h145, disp_stp_gen_h146, disp_stp_gen_h147, disp_stp_gen_h148, disp_stp_gen_h149, disp_stp_gen_h150, disp_stp_gen_h151, disp_stp_gen_h152, disp_stp_gen_h153, disp_stp_gen_h154, disp_stp_gen_h155, disp_stp_gen_h156, disp_stp_gen_h157, disp_stp_gen_h158, disp_stp_gen_h159, disp_stp_gen_h160, disp_stp_gen_h161, disp_stp_gen_h162, disp_stp_gen_h163, disp_stp_gen_h164, disp_stp_gen_h165, disp_stp_gen_h166, disp_stp_gen_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg2
  try simp (config := {decide := true}) only [disp_stp_gen_h0, disp_stp_gen_h0b, disp_stp_gen_h1, disp_stp_gen_h1b, disp_stp_gen_h2, disp_stp_gen_h3, disp_stp_gen_h4, disp_stp_gen_h5, disp_stp_gen_h6, disp_stp_gen_h7, disp_stp_gen_h8, disp_stp_gen_h9, disp_stp_gen_h10, disp_stp_gen_h11, disp_stp_gen_h12, disp_stp_gen_h13, disp_stp_gen_h13b, disp_stp_gen_h14, disp_stp_gen_h14b, disp_stp_gen_h15, disp_stp_gen_h15b, disp_stp_gen_h16, disp_stp_gen_h16b, disp_stp_gen_h17, disp_stp_gen_h17b, disp_stp_gen_h18, disp_stp_gen_h18b, disp_stp_gen_h19, disp_stp_gen_h19b, disp_stp_gen_h20, disp_stp_gen_h20b, disp_stp_gen_h21, disp_stp_gen_h21b, disp_stp_gen_h22, disp_stp_gen_h22b, disp_stp_gen_h23, disp_stp_gen_h23b, disp_stp_gen_h24, disp_stp_gen_h24b, disp_stp_gen_h25, disp_stp_gen_h25b, disp_stp_gen_h26, disp_stp_gen_h26b, disp_stp_gen_h27, disp_stp_gen_h27b, disp_stp_gen_h28, disp_stp_gen_h28b, disp_stp_gen_h29, disp_stp_gen_h29b, disp_stp_gen_h30, disp_stp_gen_h30b, disp_stp_gen_h31, disp_stp_gen_h31b, disp_stp_gen_h32, disp_stp_gen_h32b, disp_stp_gen_h33, disp_stp_gen_h33b, disp_stp_gen_h34, disp_stp_gen_h34b, disp_stp_gen_h35, disp_stp_gen_h35b, disp_stp_gen_h36, disp_stp_gen_h36b, disp_stp_gen_h37, disp_stp_gen_h37b, disp_stp_gen_h38, disp_stp_gen_h38b, disp_stp_gen_h39, disp_stp_gen_h39b, disp_stp_gen_h40, disp_stp_gen_h40b, disp_stp_gen_h41, disp_stp_gen_h41b, disp_stp_gen_h42, disp_stp_gen_h42b, disp_stp_gen_h43, disp_stp_gen_h43b, disp_stp_gen_h44, disp_stp_gen_h44b, disp_stp_gen_h45, disp_stp_gen_h45b, disp_stp_gen_h46, disp_stp_gen_h46b, disp_stp_gen_h47, disp_stp_gen_h47b, disp_stp_gen_h48, disp_stp_gen_h48b, disp_stp_gen_h49, disp_stp_gen_h49b, disp_stp_gen_h50, disp_stp_gen_h50b, disp_stp_gen_h51, disp_stp_gen_h51b, disp_stp_gen_h52, disp_stp_gen_h52b, disp_stp_gen_h53, disp_stp_gen_h53b, disp_stp_gen_h54, disp_stp_gen_h54b, disp_stp_gen_h55, disp_stp_gen_h55b, disp_stp_gen_h56, disp_stp_gen_h56b, disp_stp_gen_h57, disp_stp_gen_h57b, disp_stp_gen_h58, disp_stp_gen_h59, disp_stp_gen_h60, disp_stp_gen_h61, disp_stp_gen_h62, disp_stp_gen_h63, disp_stp_gen_h64, disp_stp_gen_h65, disp_stp_gen_h66, disp_stp_gen_h67, disp_stp_gen_h68, disp_stp_gen_h69, disp_stp_gen_h70, disp_stp_gen_h71, disp_stp_gen_h72, disp_stp_gen_h73, disp_stp_gen_h74, disp_stp_gen_h75, disp_stp_gen_h76, disp_stp_gen_h77, disp_stp_gen_h78, disp_stp_gen_h79, disp_stp_gen_h80, disp_stp_gen_h81, disp_stp_gen_h82, disp_stp_gen_h83, disp_stp_gen_h84, disp_stp_gen_h85, disp_stp_gen_h85b, disp_stp_gen_h86, disp_stp_gen_h86b, disp_stp_gen_h87, disp_stp_gen_h87b, disp_stp_gen_h88, disp_stp_gen_h88b, disp_stp_gen_h89, disp_stp_gen_h89b, disp_stp_gen_h90, disp_stp_gen_h90b, disp_stp_gen_h91, disp_stp_gen_h91b, disp_stp_gen_h92, disp_stp_gen_h92b, disp_stp_gen_h93, disp_stp_gen_h93b, disp_stp_gen_h94, disp_stp_gen_h94b, disp_stp_gen_h95, disp_stp_gen_h95b, disp_stp_gen_h96, disp_stp_gen_h96b, disp_stp_gen_h97, disp_stp_gen_h97b, disp_stp_gen_h98, disp_stp_gen_h98b, disp_stp_gen_h99, disp_stp_gen_h99b, disp_stp_gen_h100, disp_stp_gen_h100b, disp_stp_gen_h101, disp_stp_gen_h101b, disp_stp_gen_h102, disp_stp_gen_h102b, disp_stp_gen_h103, disp_stp_gen_h103b, disp_stp_gen_h104, disp_stp_gen_h104b, disp_stp_gen_h105, disp_stp_gen_h105b, disp_stp_gen_h106, disp_stp_gen_h106b, disp_stp_gen_h107, disp_stp_gen_h107b, disp_stp_gen_h108, disp_stp_gen_h108b, disp_stp_gen_h109, disp_stp_gen_h109b, disp_stp_gen_h110, disp_stp_gen_h110b, disp_stp_gen_h111, disp_stp_gen_h111b, disp_stp_gen_h112, disp_stp_gen_h112b, disp_stp_gen_h113, disp_stp_gen_h113b, disp_stp_gen_h114, disp_stp_gen_h114b, disp_stp_gen_h115, disp_stp_gen_h115b, disp_stp_gen_h116, disp_stp_gen_h116b, disp_stp_gen_h117, disp_stp_gen_h117b, disp_stp_gen_h118, disp_stp_gen_h118b, disp_stp_gen_h119, disp_stp_gen_h119b, disp_stp_gen_h120, disp_stp_gen_h120b, disp_stp_gen_h121, disp_stp_gen_h121b, disp_stp_gen_h122, disp_stp_gen_h122b, disp_stp_gen_h123, disp_stp_gen_h123b, disp_stp_gen_h124, disp_stp_gen_h124b, disp_stp_gen_h125, disp_stp_gen_h125b, disp_stp_gen_h126, disp_stp_gen_h126b, disp_stp_gen_h127, disp_stp_gen_h127b, disp_stp_gen_h128, disp_stp_gen_h128b, disp_stp_gen_h129, disp_stp_gen_h129b, disp_stp_gen_h130, disp_stp_gen_h131, disp_stp_gen_h132, disp_stp_gen_h133, disp_stp_gen_h134, disp_stp_gen_h135, disp_stp_gen_h136, disp_stp_gen_h137, disp_stp_gen_h138, disp_stp_gen_h139, disp_stp_gen_h140, disp_stp_gen_h141, disp_stp_gen_h142, disp_stp_gen_h143, disp_stp_gen_h144, disp_stp_gen_h145, disp_stp_gen_h146, disp_stp_gen_h147, disp_stp_gen_h148, disp_stp_gen_h149, disp_stp_gen_h150, disp_stp_gen_h151, disp_stp_gen_h152, disp_stp_gen_h153, disp_stp_gen_h154, disp_stp_gen_h155, disp_stp_gen_h156, disp_stp_gen_h157, disp_stp_gen_h158, disp_stp_gen_h159, disp_stp_gen_h160, disp_stp_gen_h161, disp_stp_gen_h162, disp_stp_gen_h163, disp_stp_gen_h164, disp_stp_gen_h165, disp_stp_gen_h166, disp_stp_gen_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg3
  try simp (config := {decide := true}) only [disp_stp_gen_h0, disp_stp_gen_h0b, disp_stp_gen_h1, disp_stp_gen_h1b, disp_stp_gen_h2, disp_stp_gen_h3, disp_stp_gen_h4, disp_stp_gen_h5, disp_stp_gen_h6, disp_stp_gen_h7, disp_stp_gen_h8, disp_stp_gen_h9, disp_stp_gen_h10, disp_stp_gen_h11, disp_stp_gen_h12, disp_stp_gen_h13, disp_stp_gen_h13b, disp_stp_gen_h14, disp_stp_gen_h14b, disp_stp_gen_h15, disp_stp_gen_h15b, disp_stp_gen_h16, disp_stp_gen_h16b, disp_stp_gen_h17, disp_stp_gen_h17b, disp_stp_gen_h18, disp_stp_gen_h18b, disp_stp_gen_h19, disp_stp_gen_h19b, disp_stp_gen_h20, disp_stp_gen_h20b, disp_stp_gen_h21, disp_stp_gen_h21b, disp_stp_gen_h22, disp_stp_gen_h22b, disp_stp_gen_h23, disp_stp_gen_h23b, disp_stp_gen_h24, disp_stp_gen_h24b, disp_stp_gen_h25, disp_stp_gen_h25b, disp_stp_gen_h26, disp_stp_gen_h26b, disp_stp_gen_h27, disp_stp_gen_h27b, disp_stp_gen_h28, disp_stp_gen_h28b, disp_stp_gen_h29, disp_stp_gen_h29b, disp_stp_gen_h30, disp_stp_gen_h30b, disp_stp_gen_h31, disp_stp_gen_h31b, disp_stp_gen_h32, disp_stp_gen_h32b, disp_stp_gen_h33, disp_stp_gen_h33b, disp_stp_gen_h34, disp_stp_gen_h34b, disp_stp_gen_h35, disp_stp_gen_h35b, disp_stp_gen_h36, disp_stp_gen_h36b, disp_stp_gen_h37, disp_stp_gen_h37b, disp_stp_gen_h38, disp_stp_gen_h38b, disp_stp_gen_h39, disp_stp_gen_h39b, disp_stp_gen_h40, disp_stp_gen_h40b, disp_stp_gen_h41, disp_stp_gen_h41b, disp_stp_gen_h42, disp_stp_gen_h42b, disp_stp_gen_h43, disp_stp_gen_h43b, disp_stp_gen_h44, disp_stp_gen_h44b, disp_stp_gen_h45, disp_stp_gen_h45b, disp_stp_gen_h46, disp_stp_gen_h46b, disp_stp_gen_h47, disp_stp_gen_h47b, disp_stp_gen_h48, disp_stp_gen_h48b, disp_stp_gen_h49, disp_stp_gen_h49b, disp_stp_gen_h50, disp_stp_gen_h50b, disp_stp_gen_h51, disp_stp_gen_h51b, disp_stp_gen_h52, disp_stp_gen_h52b, disp_stp_gen_h53, disp_stp_gen_h53b, disp_stp_gen_h54, disp_stp_gen_h54b, disp_stp_gen_h55, disp_stp_gen_h55b, disp_stp_gen_h56, disp_stp_gen_h56b, disp_stp_gen_h57, disp_stp_gen_h57b, disp_stp_gen_h58, disp_stp_gen_h59, disp_stp_gen_h60, disp_stp_gen_h61, disp_stp_gen_h62, disp_stp_gen_h63, disp_stp_gen_h64, disp_stp_gen_h65, disp_stp_gen_h66, disp_stp_gen_h67, disp_stp_gen_h68, disp_stp_gen_h69, disp_stp_gen_h70, disp_stp_gen_h71, disp_stp_gen_h72, disp_stp_gen_h73, disp_stp_gen_h74, disp_stp_gen_h75, disp_stp_gen_h76, disp_stp_gen_h77, disp_stp_gen_h78, disp_stp_gen_h79, disp_stp_gen_h80, disp_stp_gen_h81, disp_stp_gen_h82, disp_stp_gen_h83, disp_stp_gen_h84, disp_stp_gen_h85, disp_stp_gen_h85b, disp_stp_gen_h86, disp_stp_gen_h86b, disp_stp_gen_h87, disp_stp_gen_h87b, disp_stp_gen_h88, disp_stp_gen_h88b, disp_stp_gen_h89, disp_stp_gen_h89b, disp_stp_gen_h90, disp_stp_gen_h90b, disp_stp_gen_h91, disp_stp_gen_h91b, disp_stp_gen_h92, disp_stp_gen_h92b, disp_stp_gen_h93, disp_stp_gen_h93b, disp_stp_gen_h94, disp_stp_gen_h94b, disp_stp_gen_h95, disp_stp_gen_h95b, disp_stp_gen_h96, disp_stp_gen_h96b, disp_stp_gen_h97, disp_stp_gen_h97b, disp_stp_gen_h98, disp_stp_gen_h98b, disp_stp_gen_h99, disp_stp_gen_h99b, disp_stp_gen_h100, disp_stp_gen_h100b, disp_stp_gen_h101, disp_stp_gen_h101b, disp_stp_gen_h102, disp_stp_gen_h102b, disp_stp_gen_h103, disp_stp_gen_h103b, disp_stp_gen_h104, disp_stp_gen_h104b, disp_stp_gen_h105, disp_stp_gen_h105b, disp_stp_gen_h106, disp_stp_gen_h106b, disp_stp_gen_h107, disp_stp_gen_h107b, disp_stp_gen_h108, disp_stp_gen_h108b, disp_stp_gen_h109, disp_stp_gen_h109b, disp_stp_gen_h110, disp_stp_gen_h110b, disp_stp_gen_h111, disp_stp_gen_h111b, disp_stp_gen_h112, disp_stp_gen_h112b, disp_stp_gen_h113, disp_stp_gen_h113b, disp_stp_gen_h114, disp_stp_gen_h114b, disp_stp_gen_h115, disp_stp_gen_h115b, disp_stp_gen_h116, disp_stp_gen_h116b, disp_stp_gen_h117, disp_stp_gen_h117b, disp_stp_gen_h118, disp_stp_gen_h118b, disp_stp_gen_h119, disp_stp_gen_h119b, disp_stp_gen_h120, disp_stp_gen_h120b, disp_stp_gen_h121, disp_stp_gen_h121b, disp_stp_gen_h122, disp_stp_gen_h122b, disp_stp_gen_h123, disp_stp_gen_h123b, disp_stp_gen_h124, disp_stp_gen_h124b, disp_stp_gen_h125, disp_stp_gen_h125b, disp_stp_gen_h126, disp_stp_gen_h126b, disp_stp_gen_h127, disp_stp_gen_h127b, disp_stp_gen_h128, disp_stp_gen_h128b, disp_stp_gen_h129, disp_stp_gen_h129b, disp_stp_gen_h130, disp_stp_gen_h131, disp_stp_gen_h132, disp_stp_gen_h133, disp_stp_gen_h134, disp_stp_gen_h135, disp_stp_gen_h136, disp_stp_gen_h137, disp_stp_gen_h138, disp_stp_gen_h139, disp_stp_gen_h140, disp_stp_gen_h141, disp_stp_gen_h142, disp_stp_gen_h143, disp_stp_gen_h144, disp_stp_gen_h145, disp_stp_gen_h146, disp_stp_gen_h147, disp_stp_gen_h148, disp_stp_gen_h149, disp_stp_gen_h150, disp_stp_gen_h151, disp_stp_gen_h152, disp_stp_gen_h153, disp_stp_gen_h154, disp_stp_gen_h155, disp_stp_gen_h156, disp_stp_gen_h157, disp_stp_gen_h158, disp_stp_gen_h159, disp_stp_gen_h160, disp_stp_gen_h161, disp_stp_gen_h162, disp_stp_gen_h163, disp_stp_gen_h164, disp_stp_gen_h165, disp_stp_gen_h166, disp_stp_gen_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg4
  try simp (config := {decide := true}) only [disp_stp_gen_h0, disp_stp_gen_h0b, disp_stp_gen_h1, disp_stp_gen_h1b, disp_stp_gen_h2, disp_stp_gen_h3, disp_stp_gen_h4, disp_stp_gen_h5, disp_stp_gen_h6, disp_stp_gen_h7, disp_stp_gen_h8, disp_stp_gen_h9, disp_stp_gen_h10, disp_stp_gen_h11, disp_stp_gen_h12, disp_stp_gen_h13, disp_stp_gen_h13b, disp_stp_gen_h14, disp_stp_gen_h14b, disp_stp_gen_h15, disp_stp_gen_h15b, disp_stp_gen_h16, disp_stp_gen_h16b, disp_stp_gen_h17, disp_stp_gen_h17b, disp_stp_gen_h18, disp_stp_gen_h18b, disp_stp_gen_h19, disp_stp_gen_h19b, disp_stp_gen_h20, disp_stp_gen_h20b, disp_stp_gen_h21, disp_stp_gen_h21b, disp_stp_gen_h22, disp_stp_gen_h22b, disp_stp_gen_h23, disp_stp_gen_h23b, disp_stp_gen_h24, disp_stp_gen_h24b, disp_stp_gen_h25, disp_stp_gen_h25b, disp_stp_gen_h26, disp_stp_gen_h26b, disp_stp_gen_h27, disp_stp_gen_h27b, disp_stp_gen_h28, disp_stp_gen_h28b, disp_stp_gen_h29, disp_stp_gen_h29b, disp_stp_gen_h30, disp_stp_gen_h30b, disp_stp_gen_h31, disp_stp_gen_h31b, disp_stp_gen_h32, disp_stp_gen_h32b, disp_stp_gen_h33, disp_stp_gen_h33b, disp_stp_gen_h34, disp_stp_gen_h34b, disp_stp_gen_h35, disp_stp_gen_h35b, disp_stp_gen_h36, disp_stp_gen_h36b, disp_stp_gen_h37, disp_stp_gen_h37b, disp_stp_gen_h38, disp_stp_gen_h38b, disp_stp_gen_h39, disp_stp_gen_h39b, disp_stp_gen_h40, disp_stp_gen_h40b, disp_stp_gen_h41, disp_stp_gen_h41b, disp_stp_gen_h42, disp_stp_gen_h42b, disp_stp_gen_h43, disp_stp_gen_h43b, disp_stp_gen_h44, disp_stp_gen_h44b, disp_stp_gen_h45, disp_stp_gen_h45b, disp_stp_gen_h46, disp_stp_gen_h46b, disp_stp_gen_h47, disp_stp_gen_h47b, disp_stp_gen_h48, disp_stp_gen_h48b, disp_stp_gen_h49, disp_stp_gen_h49b, disp_stp_gen_h50, disp_stp_gen_h50b, disp_stp_gen_h51, disp_stp_gen_h51b, disp_stp_gen_h52, disp_stp_gen_h52b, disp_stp_gen_h53, disp_stp_gen_h53b, disp_stp_gen_h54, disp_stp_gen_h54b, disp_stp_gen_h55, disp_stp_gen_h55b, disp_stp_gen_h56, disp_stp_gen_h56b, disp_stp_gen_h57, disp_stp_gen_h57b, disp_stp_gen_h58, disp_stp_gen_h59, disp_stp_gen_h60, disp_stp_gen_h61, disp_stp_gen_h62, disp_stp_gen_h63, disp_stp_gen_h64, disp_stp_gen_h65, disp_stp_gen_h66, disp_stp_gen_h67, disp_stp_gen_h68, disp_stp_gen_h69, disp_stp_gen_h70, disp_stp_gen_h71, disp_stp_gen_h72, disp_stp_gen_h73, disp_stp_gen_h74, disp_stp_gen_h75, disp_stp_gen_h76, disp_stp_gen_h77, disp_stp_gen_h78, disp_stp_gen_h79, disp_stp_gen_h80, disp_stp_gen_h81, disp_stp_gen_h82, disp_stp_gen_h83, disp_stp_gen_h84, disp_stp_gen_h85, disp_stp_gen_h85b, disp_stp_gen_h86, disp_stp_gen_h86b, disp_stp_gen_h87, disp_stp_gen_h87b, disp_stp_gen_h88, disp_stp_gen_h88b, disp_stp_gen_h89, disp_stp_gen_h89b, disp_stp_gen_h90, disp_stp_gen_h90b, disp_stp_gen_h91, disp_stp_gen_h91b, disp_stp_gen_h92, disp_stp_gen_h92b, disp_stp_gen_h93, disp_stp_gen_h93b, disp_stp_gen_h94, disp_stp_gen_h94b, disp_stp_gen_h95, disp_stp_gen_h95b, disp_stp_gen_h96, disp_stp_gen_h96b, disp_stp_gen_h97, disp_stp_gen_h97b, disp_stp_gen_h98, disp_stp_gen_h98b, disp_stp_gen_h99, disp_stp_gen_h99b, disp_stp_gen_h100, disp_stp_gen_h100b, disp_stp_gen_h101, disp_stp_gen_h101b, disp_stp_gen_h102, disp_stp_gen_h102b, disp_stp_gen_h103, disp_stp_gen_h103b, disp_stp_gen_h104, disp_stp_gen_h104b, disp_stp_gen_h105, disp_stp_gen_h105b, disp_stp_gen_h106, disp_stp_gen_h106b, disp_stp_gen_h107, disp_stp_gen_h107b, disp_stp_gen_h108, disp_stp_gen_h108b, disp_stp_gen_h109, disp_stp_gen_h109b, disp_stp_gen_h110, disp_stp_gen_h110b, disp_stp_gen_h111, disp_stp_gen_h111b, disp_stp_gen_h112, disp_stp_gen_h112b, disp_stp_gen_h113, disp_stp_gen_h113b, disp_stp_gen_h114, disp_stp_gen_h114b, disp_stp_gen_h115, disp_stp_gen_h115b, disp_stp_gen_h116, disp_stp_gen_h116b, disp_stp_gen_h117, disp_stp_gen_h117b, disp_stp_gen_h118, disp_stp_gen_h118b, disp_stp_gen_h119, disp_stp_gen_h119b, disp_stp_gen_h120, disp_stp_gen_h120b, disp_stp_gen_h121, disp_stp_gen_h121b, disp_stp_gen_h122, disp_stp_gen_h122b, disp_stp_gen_h123, disp_stp_gen_h123b, disp_stp_gen_h124, disp_stp_gen_h124b, disp_stp_gen_h125, disp_stp_gen_h125b, disp_stp_gen_h126, disp_stp_gen_h126b, disp_stp_gen_h127, disp_stp_gen_h127b, disp_stp_gen_h128, disp_stp_gen_h128b, disp_stp_gen_h129, disp_stp_gen_h129b, disp_stp_gen_h130, disp_stp_gen_h131, disp_stp_gen_h132, disp_stp_gen_h133, disp_stp_gen_h134, disp_stp_gen_h135, disp_stp_gen_h136, disp_stp_gen_h137, disp_stp_gen_h138, disp_stp_gen_h139, disp_stp_gen_h140, disp_stp_gen_h141, disp_stp_gen_h142, disp_stp_gen_h143, disp_stp_gen_h144, disp_stp_gen_h145, disp_stp_gen_h146, disp_stp_gen_h147, disp_stp_gen_h148, disp_stp_gen_h149, disp_stp_gen_h150, disp_stp_gen_h151, disp_stp_gen_h152, disp_stp_gen_h153, disp_stp_gen_h154, disp_stp_gen_h155, disp_stp_gen_h156, disp_stp_gen_h157, disp_stp_gen_h158, disp_stp_gen_h159, disp_stp_gen_h160, disp_stp_gen_h161, disp_stp_gen_h162, disp_stp_gen_h163, disp_stp_gen_h164, disp_stp_gen_h165, disp_stp_gen_h166, disp_stp_gen_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg5
  try simp (config := {decide := true}) only [disp_stp_gen_h0, disp_stp_gen_h0b, disp_stp_gen_h1, disp_stp_gen_h1b, disp_stp_gen_h2, disp_stp_gen_h3, disp_stp_gen_h4, disp_stp_gen_h5, disp_stp_gen_h6, disp_stp_gen_h7, disp_stp_gen_h8, disp_stp_gen_h9, disp_stp_gen_h10, disp_stp_gen_h11, disp_stp_gen_h12, disp_stp_gen_h13, disp_stp_gen_h13b, disp_stp_gen_h14, disp_stp_gen_h14b, disp_stp_gen_h15, disp_stp_gen_h15b, disp_stp_gen_h16, disp_stp_gen_h16b, disp_stp_gen_h17, disp_stp_gen_h17b, disp_stp_gen_h18, disp_stp_gen_h18b, disp_stp_gen_h19, disp_stp_gen_h19b, disp_stp_gen_h20, disp_stp_gen_h20b, disp_stp_gen_h21, disp_stp_gen_h21b, disp_stp_gen_h22, disp_stp_gen_h22b, disp_stp_gen_h23, disp_stp_gen_h23b, disp_stp_gen_h24, disp_stp_gen_h24b, disp_stp_gen_h25, disp_stp_gen_h25b, disp_stp_gen_h26, disp_stp_gen_h26b, disp_stp_gen_h27, disp_stp_gen_h27b, disp_stp_gen_h28, disp_stp_gen_h28b, disp_stp_gen_h29, disp_stp_gen_h29b, disp_stp_gen_h30, disp_stp_gen_h30b, disp_stp_gen_h31, disp_stp_gen_h31b, disp_stp_gen_h32, disp_stp_gen_h32b, disp_stp_gen_h33, disp_stp_gen_h33b, disp_stp_gen_h34, disp_stp_gen_h34b, disp_stp_gen_h35, disp_stp_gen_h35b, disp_stp_gen_h36, disp_stp_gen_h36b, disp_stp_gen_h37, disp_stp_gen_h37b, disp_stp_gen_h38, disp_stp_gen_h38b, disp_stp_gen_h39, disp_stp_gen_h39b, disp_stp_gen_h40, disp_stp_gen_h40b, disp_stp_gen_h41, disp_stp_gen_h41b, disp_stp_gen_h42, disp_stp_gen_h42b, disp_stp_gen_h43, disp_stp_gen_h43b, disp_stp_gen_h44, disp_stp_gen_h44b, disp_stp_gen_h45, disp_stp_gen_h45b, disp_stp_gen_h46, disp_stp_gen_h46b, disp_stp_gen_h47, disp_stp_gen_h47b, disp_stp_gen_h48, disp_stp_gen_h48b, disp_stp_gen_h49, disp_stp_gen_h49b, disp_stp_gen_h50, disp_stp_gen_h50b, disp_stp_gen_h51, disp_stp_gen_h51b, disp_stp_gen_h52, disp_stp_gen_h52b, disp_stp_gen_h53, disp_stp_gen_h53b, disp_stp_gen_h54, disp_stp_gen_h54b, disp_stp_gen_h55, disp_stp_gen_h55b, disp_stp_gen_h56, disp_stp_gen_h56b, disp_stp_gen_h57, disp_stp_gen_h57b, disp_stp_gen_h58, disp_stp_gen_h59, disp_stp_gen_h60, disp_stp_gen_h61, disp_stp_gen_h62, disp_stp_gen_h63, disp_stp_gen_h64, disp_stp_gen_h65, disp_stp_gen_h66, disp_stp_gen_h67, disp_stp_gen_h68, disp_stp_gen_h69, disp_stp_gen_h70, disp_stp_gen_h71, disp_stp_gen_h72, disp_stp_gen_h73, disp_stp_gen_h74, disp_stp_gen_h75, disp_stp_gen_h76, disp_stp_gen_h77, disp_stp_gen_h78, disp_stp_gen_h79, disp_stp_gen_h80, disp_stp_gen_h81, disp_stp_gen_h82, disp_stp_gen_h83, disp_stp_gen_h84, disp_stp_gen_h85, disp_stp_gen_h85b, disp_stp_gen_h86, disp_stp_gen_h86b, disp_stp_gen_h87, disp_stp_gen_h87b, disp_stp_gen_h88, disp_stp_gen_h88b, disp_stp_gen_h89, disp_stp_gen_h89b, disp_stp_gen_h90, disp_stp_gen_h90b, disp_stp_gen_h91, disp_stp_gen_h91b, disp_stp_gen_h92, disp_stp_gen_h92b, disp_stp_gen_h93, disp_stp_gen_h93b, disp_stp_gen_h94, disp_stp_gen_h94b, disp_stp_gen_h95, disp_stp_gen_h95b, disp_stp_gen_h96, disp_stp_gen_h96b, disp_stp_gen_h97, disp_stp_gen_h97b, disp_stp_gen_h98, disp_stp_gen_h98b, disp_stp_gen_h99, disp_stp_gen_h99b, disp_stp_gen_h100, disp_stp_gen_h100b, disp_stp_gen_h101, disp_stp_gen_h101b, disp_stp_gen_h102, disp_stp_gen_h102b, disp_stp_gen_h103, disp_stp_gen_h103b, disp_stp_gen_h104, disp_stp_gen_h104b, disp_stp_gen_h105, disp_stp_gen_h105b, disp_stp_gen_h106, disp_stp_gen_h106b, disp_stp_gen_h107, disp_stp_gen_h107b, disp_stp_gen_h108, disp_stp_gen_h108b, disp_stp_gen_h109, disp_stp_gen_h109b, disp_stp_gen_h110, disp_stp_gen_h110b, disp_stp_gen_h111, disp_stp_gen_h111b, disp_stp_gen_h112, disp_stp_gen_h112b, disp_stp_gen_h113, disp_stp_gen_h113b, disp_stp_gen_h114, disp_stp_gen_h114b, disp_stp_gen_h115, disp_stp_gen_h115b, disp_stp_gen_h116, disp_stp_gen_h116b, disp_stp_gen_h117, disp_stp_gen_h117b, disp_stp_gen_h118, disp_stp_gen_h118b, disp_stp_gen_h119, disp_stp_gen_h119b, disp_stp_gen_h120, disp_stp_gen_h120b, disp_stp_gen_h121, disp_stp_gen_h121b, disp_stp_gen_h122, disp_stp_gen_h122b, disp_stp_gen_h123, disp_stp_gen_h123b, disp_stp_gen_h124, disp_stp_gen_h124b, disp_stp_gen_h125, disp_stp_gen_h125b, disp_stp_gen_h126, disp_stp_gen_h126b, disp_stp_gen_h127, disp_stp_gen_h127b, disp_stp_gen_h128, disp_stp_gen_h128b, disp_stp_gen_h129, disp_stp_gen_h129b, disp_stp_gen_h130, disp_stp_gen_h131, disp_stp_gen_h132, disp_stp_gen_h133, disp_stp_gen_h134, disp_stp_gen_h135, disp_stp_gen_h136, disp_stp_gen_h137, disp_stp_gen_h138, disp_stp_gen_h139, disp_stp_gen_h140, disp_stp_gen_h141, disp_stp_gen_h142, disp_stp_gen_h143, disp_stp_gen_h144, disp_stp_gen_h145, disp_stp_gen_h146, disp_stp_gen_h147, disp_stp_gen_h148, disp_stp_gen_h149, disp_stp_gen_h150, disp_stp_gen_h151, disp_stp_gen_h152, disp_stp_gen_h153, disp_stp_gen_h154, disp_stp_gen_h155, disp_stp_gen_h156, disp_stp_gen_h157, disp_stp_gen_h158, disp_stp_gen_h159, disp_stp_gen_h160, disp_stp_gen_h161, disp_stp_gen_h162, disp_stp_gen_h163, disp_stp_gen_h164, disp_stp_gen_h165, disp_stp_gen_h166, disp_stp_gen_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg6
  try simp (config := {decide := true}) only [disp_stp_gen_h0, disp_stp_gen_h0b, disp_stp_gen_h1, disp_stp_gen_h1b, disp_stp_gen_h2, disp_stp_gen_h3, disp_stp_gen_h4, disp_stp_gen_h5, disp_stp_gen_h6, disp_stp_gen_h7, disp_stp_gen_h8, disp_stp_gen_h9, disp_stp_gen_h10, disp_stp_gen_h11, disp_stp_gen_h12, disp_stp_gen_h13, disp_stp_gen_h13b, disp_stp_gen_h14, disp_stp_gen_h14b, disp_stp_gen_h15, disp_stp_gen_h15b, disp_stp_gen_h16, disp_stp_gen_h16b, disp_stp_gen_h17, disp_stp_gen_h17b, disp_stp_gen_h18, disp_stp_gen_h18b, disp_stp_gen_h19, disp_stp_gen_h19b, disp_stp_gen_h20, disp_stp_gen_h20b, disp_stp_gen_h21, disp_stp_gen_h21b, disp_stp_gen_h22, disp_stp_gen_h22b, disp_stp_gen_h23, disp_stp_gen_h23b, disp_stp_gen_h24, disp_stp_gen_h24b, disp_stp_gen_h25, disp_stp_gen_h25b, disp_stp_gen_h26, disp_stp_gen_h26b, disp_stp_gen_h27, disp_stp_gen_h27b, disp_stp_gen_h28, disp_stp_gen_h28b, disp_stp_gen_h29, disp_stp_gen_h29b, disp_stp_gen_h30, disp_stp_gen_h30b, disp_stp_gen_h31, disp_stp_gen_h31b, disp_stp_gen_h32, disp_stp_gen_h32b, disp_stp_gen_h33, disp_stp_gen_h33b, disp_stp_gen_h34, disp_stp_gen_h34b, disp_stp_gen_h35, disp_stp_gen_h35b, disp_stp_gen_h36, disp_stp_gen_h36b, disp_stp_gen_h37, disp_stp_gen_h37b, disp_stp_gen_h38, disp_stp_gen_h38b, disp_stp_gen_h39, disp_stp_gen_h39b, disp_stp_gen_h40, disp_stp_gen_h40b, disp_stp_gen_h41, disp_stp_gen_h41b, disp_stp_gen_h42, disp_stp_gen_h42b, disp_stp_gen_h43, disp_stp_gen_h43b, disp_stp_gen_h44, disp_stp_gen_h44b, disp_stp_gen_h45, disp_stp_gen_h45b, disp_stp_gen_h46, disp_stp_gen_h46b, disp_stp_gen_h47, disp_stp_gen_h47b, disp_stp_gen_h48, disp_stp_gen_h48b, disp_stp_gen_h49, disp_stp_gen_h49b, disp_stp_gen_h50, disp_stp_gen_h50b, disp_stp_gen_h51, disp_stp_gen_h51b, disp_stp_gen_h52, disp_stp_gen_h52b, disp_stp_gen_h53, disp_stp_gen_h53b, disp_stp_gen_h54, disp_stp_gen_h54b, disp_stp_gen_h55, disp_stp_gen_h55b, disp_stp_gen_h56, disp_stp_gen_h56b, disp_stp_gen_h57, disp_stp_gen_h57b, disp_stp_gen_h58, disp_stp_gen_h59, disp_stp_gen_h60, disp_stp_gen_h61, disp_stp_gen_h62, disp_stp_gen_h63, disp_stp_gen_h64, disp_stp_gen_h65, disp_stp_gen_h66, disp_stp_gen_h67, disp_stp_gen_h68, disp_stp_gen_h69, disp_stp_gen_h70, disp_stp_gen_h71, disp_stp_gen_h72, disp_stp_gen_h73, disp_stp_gen_h74, disp_stp_gen_h75, disp_stp_gen_h76, disp_stp_gen_h77, disp_stp_gen_h78, disp_stp_gen_h79, disp_stp_gen_h80, disp_stp_gen_h81, disp_stp_gen_h82, disp_stp_gen_h83, disp_stp_gen_h84, disp_stp_gen_h85, disp_stp_gen_h85b, disp_stp_gen_h86, disp_stp_gen_h86b, disp_stp_gen_h87, disp_stp_gen_h87b, disp_stp_gen_h88, disp_stp_gen_h88b, disp_stp_gen_h89, disp_stp_gen_h89b, disp_stp_gen_h90, disp_stp_gen_h90b, disp_stp_gen_h91, disp_stp_gen_h91b, disp_stp_gen_h92, disp_stp_gen_h92b, disp_stp_gen_h93, disp_stp_gen_h93b, disp_stp_gen_h94, disp_stp_gen_h94b, disp_stp_gen_h95, disp_stp_gen_h95b, disp_stp_gen_h96, disp_stp_gen_h96b, disp_stp_gen_h97, disp_stp_gen_h97b, disp_stp_gen_h98, disp_stp_gen_h98b, disp_stp_gen_h99, disp_stp_gen_h99b, disp_stp_gen_h100, disp_stp_gen_h100b, disp_stp_gen_h101, disp_stp_gen_h101b, disp_stp_gen_h102, disp_stp_gen_h102b, disp_stp_gen_h103, disp_stp_gen_h103b, disp_stp_gen_h104, disp_stp_gen_h104b, disp_stp_gen_h105, disp_stp_gen_h105b, disp_stp_gen_h106, disp_stp_gen_h106b, disp_stp_gen_h107, disp_stp_gen_h107b, disp_stp_gen_h108, disp_stp_gen_h108b, disp_stp_gen_h109, disp_stp_gen_h109b, disp_stp_gen_h110, disp_stp_gen_h110b, disp_stp_gen_h111, disp_stp_gen_h111b, disp_stp_gen_h112, disp_stp_gen_h112b, disp_stp_gen_h113, disp_stp_gen_h113b, disp_stp_gen_h114, disp_stp_gen_h114b, disp_stp_gen_h115, disp_stp_gen_h115b, disp_stp_gen_h116, disp_stp_gen_h116b, disp_stp_gen_h117, disp_stp_gen_h117b, disp_stp_gen_h118, disp_stp_gen_h118b, disp_stp_gen_h119, disp_stp_gen_h119b, disp_stp_gen_h120, disp_stp_gen_h120b, disp_stp_gen_h121, disp_stp_gen_h121b, disp_stp_gen_h122, disp_stp_gen_h122b, disp_stp_gen_h123, disp_stp_gen_h123b, disp_stp_gen_h124, disp_stp_gen_h124b, disp_stp_gen_h125, disp_stp_gen_h125b, disp_stp_gen_h126, disp_stp_gen_h126b, disp_stp_gen_h127, disp_stp_gen_h127b, disp_stp_gen_h128, disp_stp_gen_h128b, disp_stp_gen_h129, disp_stp_gen_h129b, disp_stp_gen_h130, disp_stp_gen_h131, disp_stp_gen_h132, disp_stp_gen_h133, disp_stp_gen_h134, disp_stp_gen_h135, disp_stp_gen_h136, disp_stp_gen_h137, disp_stp_gen_h138, disp_stp_gen_h139, disp_stp_gen_h140, disp_stp_gen_h141, disp_stp_gen_h142, disp_stp_gen_h143, disp_stp_gen_h144, disp_stp_gen_h145, disp_stp_gen_h146, disp_stp_gen_h147, disp_stp_gen_h148, disp_stp_gen_h149, disp_stp_gen_h150, disp_stp_gen_h151, disp_stp_gen_h152, disp_stp_gen_h153, disp_stp_gen_h154, disp_stp_gen_h155, disp_stp_gen_h156, disp_stp_gen_h157, disp_stp_gen_h158, disp_stp_gen_h159, disp_stp_gen_h160, disp_stp_gen_h161, disp_stp_gen_h162, disp_stp_gen_h163, disp_stp_gen_h164, disp_stp_gen_h165, disp_stp_gen_h166, disp_stp_gen_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg7
  try simp (config := {decide := true}) only [disp_stp_gen_h0, disp_stp_gen_h0b, disp_stp_gen_h1, disp_stp_gen_h1b, disp_stp_gen_h2, disp_stp_gen_h3, disp_stp_gen_h4, disp_stp_gen_h5, disp_stp_gen_h6, disp_stp_gen_h7, disp_stp_gen_h8, disp_stp_gen_h9, disp_stp_gen_h10, disp_stp_gen_h11, disp_stp_gen_h12, disp_stp_gen_h13, disp_stp_gen_h13b, disp_stp_gen_h14, disp_stp_gen_h14b, disp_stp_gen_h15, disp_stp_gen_h15b, disp_stp_gen_h16, disp_stp_gen_h16b, disp_stp_gen_h17, disp_stp_gen_h17b, disp_stp_gen_h18, disp_stp_gen_h18b, disp_stp_gen_h19, disp_stp_gen_h19b, disp_stp_gen_h20, disp_stp_gen_h20b, disp_stp_gen_h21, disp_stp_gen_h21b, disp_stp_gen_h22, disp_stp_gen_h22b, disp_stp_gen_h23, disp_stp_gen_h23b, disp_stp_gen_h24, disp_stp_gen_h24b, disp_stp_gen_h25, disp_stp_gen_h25b, disp_stp_gen_h26, disp_stp_gen_h26b, disp_stp_gen_h27, disp_stp_gen_h27b, disp_stp_gen_h28, disp_stp_gen_h28b, disp_stp_gen_h29, disp_stp_gen_h29b, disp_stp_gen_h30, disp_stp_gen_h30b, disp_stp_gen_h31, disp_stp_gen_h31b, disp_stp_gen_h32, disp_stp_gen_h32b, disp_stp_gen_h33, disp_stp_gen_h33b, disp_stp_gen_h34, disp_stp_gen_h34b, disp_stp_gen_h35, disp_stp_gen_h35b, disp_stp_gen_h36, disp_stp_gen_h36b, disp_stp_gen_h37, disp_stp_gen_h37b, disp_stp_gen_h38, disp_stp_gen_h38b, disp_stp_gen_h39, disp_stp_gen_h39b, disp_stp_gen_h40, disp_stp_gen_h40b, disp_stp_gen_h41, disp_stp_gen_h41b, disp_stp_gen_h42, disp_stp_gen_h42b, disp_stp_gen_h43, disp_stp_gen_h43b, disp_stp_gen_h44, disp_stp_gen_h44b, disp_stp_gen_h45, disp_stp_gen_h45b, disp_stp_gen_h46, disp_stp_gen_h46b, disp_stp_gen_h47, disp_stp_gen_h47b, disp_stp_gen_h48, disp_stp_gen_h48b, disp_stp_gen_h49, disp_stp_gen_h49b, disp_stp_gen_h50, disp_stp_gen_h50b, disp_stp_gen_h51, disp_stp_gen_h51b, disp_stp_gen_h52, disp_stp_gen_h52b, disp_stp_gen_h53, disp_stp_gen_h53b, disp_stp_gen_h54, disp_stp_gen_h54b, disp_stp_gen_h55, disp_stp_gen_h55b, disp_stp_gen_h56, disp_stp_gen_h56b, disp_stp_gen_h57, disp_stp_gen_h57b, disp_stp_gen_h58, disp_stp_gen_h59, disp_stp_gen_h60, disp_stp_gen_h61, disp_stp_gen_h62, disp_stp_gen_h63, disp_stp_gen_h64, disp_stp_gen_h65, disp_stp_gen_h66, disp_stp_gen_h67, disp_stp_gen_h68, disp_stp_gen_h69, disp_stp_gen_h70, disp_stp_gen_h71, disp_stp_gen_h72, disp_stp_gen_h73, disp_stp_gen_h74, disp_stp_gen_h75, disp_stp_gen_h76, disp_stp_gen_h77, disp_stp_gen_h78, disp_stp_gen_h79, disp_stp_gen_h80, disp_stp_gen_h81, disp_stp_gen_h82, disp_stp_gen_h83, disp_stp_gen_h84, disp_stp_gen_h85, disp_stp_gen_h85b, disp_stp_gen_h86, disp_stp_gen_h86b, disp_stp_gen_h87, disp_stp_gen_h87b, disp_stp_gen_h88, disp_stp_gen_h88b, disp_stp_gen_h89, disp_stp_gen_h89b, disp_stp_gen_h90, disp_stp_gen_h90b, disp_stp_gen_h91, disp_stp_gen_h91b, disp_stp_gen_h92, disp_stp_gen_h92b, disp_stp_gen_h93, disp_stp_gen_h93b, disp_stp_gen_h94, disp_stp_gen_h94b, disp_stp_gen_h95, disp_stp_gen_h95b, disp_stp_gen_h96, disp_stp_gen_h96b, disp_stp_gen_h97, disp_stp_gen_h97b, disp_stp_gen_h98, disp_stp_gen_h98b, disp_stp_gen_h99, disp_stp_gen_h99b, disp_stp_gen_h100, disp_stp_gen_h100b, disp_stp_gen_h101, disp_stp_gen_h101b, disp_stp_gen_h102, disp_stp_gen_h102b, disp_stp_gen_h103, disp_stp_gen_h103b, disp_stp_gen_h104, disp_stp_gen_h104b, disp_stp_gen_h105, disp_stp_gen_h105b, disp_stp_gen_h106, disp_stp_gen_h106b, disp_stp_gen_h107, disp_stp_gen_h107b, disp_stp_gen_h108, disp_stp_gen_h108b, disp_stp_gen_h109, disp_stp_gen_h109b, disp_stp_gen_h110, disp_stp_gen_h110b, disp_stp_gen_h111, disp_stp_gen_h111b, disp_stp_gen_h112, disp_stp_gen_h112b, disp_stp_gen_h113, disp_stp_gen_h113b, disp_stp_gen_h114, disp_stp_gen_h114b, disp_stp_gen_h115, disp_stp_gen_h115b, disp_stp_gen_h116, disp_stp_gen_h116b, disp_stp_gen_h117, disp_stp_gen_h117b, disp_stp_gen_h118, disp_stp_gen_h118b, disp_stp_gen_h119, disp_stp_gen_h119b, disp_stp_gen_h120, disp_stp_gen_h120b, disp_stp_gen_h121, disp_stp_gen_h121b, disp_stp_gen_h122, disp_stp_gen_h122b, disp_stp_gen_h123, disp_stp_gen_h123b, disp_stp_gen_h124, disp_stp_gen_h124b, disp_stp_gen_h125, disp_stp_gen_h125b, disp_stp_gen_h126, disp_stp_gen_h126b, disp_stp_gen_h127, disp_stp_gen_h127b, disp_stp_gen_h128, disp_stp_gen_h128b, disp_stp_gen_h129, disp_stp_gen_h129b, disp_stp_gen_h130, disp_stp_gen_h131, disp_stp_gen_h132, disp_stp_gen_h133, disp_stp_gen_h134, disp_stp_gen_h135, disp_stp_gen_h136, disp_stp_gen_h137, disp_stp_gen_h138, disp_stp_gen_h139, disp_stp_gen_h140, disp_stp_gen_h141, disp_stp_gen_h142, disp_stp_gen_h143, disp_stp_gen_h144, disp_stp_gen_h145, disp_stp_gen_h146, disp_stp_gen_h147, disp_stp_gen_h148, disp_stp_gen_h149, disp_stp_gen_h150, disp_stp_gen_h151, disp_stp_gen_h152, disp_stp_gen_h153, disp_stp_gen_h154, disp_stp_gen_h155, disp_stp_gen_h156, disp_stp_gen_h157, disp_stp_gen_h158, disp_stp_gen_h159, disp_stp_gen_h160, disp_stp_gen_h161, disp_stp_gen_h162, disp_stp_gen_h163, disp_stp_gen_h164, disp_stp_gen_h165, disp_stp_gen_h166, disp_stp_gen_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg8
  try simp (config := {decide := true}) only [disp_stp_gen_h0, disp_stp_gen_h0b, disp_stp_gen_h1, disp_stp_gen_h1b, disp_stp_gen_h2, disp_stp_gen_h3, disp_stp_gen_h4, disp_stp_gen_h5, disp_stp_gen_h6, disp_stp_gen_h7, disp_stp_gen_h8, disp_stp_gen_h9, disp_stp_gen_h10, disp_stp_gen_h11, disp_stp_gen_h12, disp_stp_gen_h13, disp_stp_gen_h13b, disp_stp_gen_h14, disp_stp_gen_h14b, disp_stp_gen_h15, disp_stp_gen_h15b, disp_stp_gen_h16, disp_stp_gen_h16b, disp_stp_gen_h17, disp_stp_gen_h17b, disp_stp_gen_h18, disp_stp_gen_h18b, disp_stp_gen_h19, disp_stp_gen_h19b, disp_stp_gen_h20, disp_stp_gen_h20b, disp_stp_gen_h21, disp_stp_gen_h21b, disp_stp_gen_h22, disp_stp_gen_h22b, disp_stp_gen_h23, disp_stp_gen_h23b, disp_stp_gen_h24, disp_stp_gen_h24b, disp_stp_gen_h25, disp_stp_gen_h25b, disp_stp_gen_h26, disp_stp_gen_h26b, disp_stp_gen_h27, disp_stp_gen_h27b, disp_stp_gen_h28, disp_stp_gen_h28b, disp_stp_gen_h29, disp_stp_gen_h29b, disp_stp_gen_h30, disp_stp_gen_h30b, disp_stp_gen_h31, disp_stp_gen_h31b, disp_stp_gen_h32, disp_stp_gen_h32b, disp_stp_gen_h33, disp_stp_gen_h33b, disp_stp_gen_h34, disp_stp_gen_h34b, disp_stp_gen_h35, disp_stp_gen_h35b, disp_stp_gen_h36, disp_stp_gen_h36b, disp_stp_gen_h37, disp_stp_gen_h37b, disp_stp_gen_h38, disp_stp_gen_h38b, disp_stp_gen_h39, disp_stp_gen_h39b, disp_stp_gen_h40, disp_stp_gen_h40b, disp_stp_gen_h41, disp_stp_gen_h41b, disp_stp_gen_h42, disp_stp_gen_h42b, disp_stp_gen_h43, disp_stp_gen_h43b, disp_stp_gen_h44, disp_stp_gen_h44b, disp_stp_gen_h45, disp_stp_gen_h45b, disp_stp_gen_h46, disp_stp_gen_h46b, disp_stp_gen_h47, disp_stp_gen_h47b, disp_stp_gen_h48, disp_stp_gen_h48b, disp_stp_gen_h49, disp_stp_gen_h49b, disp_stp_gen_h50, disp_stp_gen_h50b, disp_stp_gen_h51, disp_stp_gen_h51b, disp_stp_gen_h52, disp_stp_gen_h52b, disp_stp_gen_h53, disp_stp_gen_h53b, disp_stp_gen_h54, disp_stp_gen_h54b, disp_stp_gen_h55, disp_stp_gen_h55b, disp_stp_gen_h56, disp_stp_gen_h56b, disp_stp_gen_h57, disp_stp_gen_h57b, disp_stp_gen_h58, disp_stp_gen_h59, disp_stp_gen_h60, disp_stp_gen_h61, disp_stp_gen_h62, disp_stp_gen_h63, disp_stp_gen_h64, disp_stp_gen_h65, disp_stp_gen_h66, disp_stp_gen_h67, disp_stp_gen_h68, disp_stp_gen_h69, disp_stp_gen_h70, disp_stp_gen_h71, disp_stp_gen_h72, disp_stp_gen_h73, disp_stp_gen_h74, disp_stp_gen_h75, disp_stp_gen_h76, disp_stp_gen_h77, disp_stp_gen_h78, disp_stp_gen_h79, disp_stp_gen_h80, disp_stp_gen_h81, disp_stp_gen_h82, disp_stp_gen_h83, disp_stp_gen_h84, disp_stp_gen_h85, disp_stp_gen_h85b, disp_stp_gen_h86, disp_stp_gen_h86b, disp_stp_gen_h87, disp_stp_gen_h87b, disp_stp_gen_h88, disp_stp_gen_h88b, disp_stp_gen_h89, disp_stp_gen_h89b, disp_stp_gen_h90, disp_stp_gen_h90b, disp_stp_gen_h91, disp_stp_gen_h91b, disp_stp_gen_h92, disp_stp_gen_h92b, disp_stp_gen_h93, disp_stp_gen_h93b, disp_stp_gen_h94, disp_stp_gen_h94b, disp_stp_gen_h95, disp_stp_gen_h95b, disp_stp_gen_h96, disp_stp_gen_h96b, disp_stp_gen_h97, disp_stp_gen_h97b, disp_stp_gen_h98, disp_stp_gen_h98b, disp_stp_gen_h99, disp_stp_gen_h99b, disp_stp_gen_h100, disp_stp_gen_h100b, disp_stp_gen_h101, disp_stp_gen_h101b, disp_stp_gen_h102, disp_stp_gen_h102b, disp_stp_gen_h103, disp_stp_gen_h103b, disp_stp_gen_h104, disp_stp_gen_h104b, disp_stp_gen_h105, disp_stp_gen_h105b, disp_stp_gen_h106, disp_stp_gen_h106b, disp_stp_gen_h107, disp_stp_gen_h107b, disp_stp_gen_h108, disp_stp_gen_h108b, disp_stp_gen_h109, disp_stp_gen_h109b, disp_stp_gen_h110, disp_stp_gen_h110b, disp_stp_gen_h111, disp_stp_gen_h111b, disp_stp_gen_h112, disp_stp_gen_h112b, disp_stp_gen_h113, disp_stp_gen_h113b, disp_stp_gen_h114, disp_stp_gen_h114b, disp_stp_gen_h115, disp_stp_gen_h115b, disp_stp_gen_h116, disp_stp_gen_h116b, disp_stp_gen_h117, disp_stp_gen_h117b, disp_stp_gen_h118, disp_stp_gen_h118b, disp_stp_gen_h119, disp_stp_gen_h119b, disp_stp_gen_h120, disp_stp_gen_h120b, disp_stp_gen_h121, disp_stp_gen_h121b, disp_stp_gen_h122, disp_stp_gen_h122b, disp_stp_gen_h123, disp_stp_gen_h123b, disp_stp_gen_h124, disp_stp_gen_h124b, disp_stp_gen_h125, disp_stp_gen_h125b, disp_stp_gen_h126, disp_stp_gen_h126b, disp_stp_gen_h127, disp_stp_gen_h127b, disp_stp_gen_h128, disp_stp_gen_h128b, disp_stp_gen_h129, disp_stp_gen_h129b, disp_stp_gen_h130, disp_stp_gen_h131, disp_stp_gen_h132, disp_stp_gen_h133, disp_stp_gen_h134, disp_stp_gen_h135, disp_stp_gen_h136, disp_stp_gen_h137, disp_stp_gen_h138, disp_stp_gen_h139, disp_stp_gen_h140, disp_stp_gen_h141, disp_stp_gen_h142, disp_stp_gen_h143, disp_stp_gen_h144, disp_stp_gen_h145, disp_stp_gen_h146, disp_stp_gen_h147, disp_stp_gen_h148, disp_stp_gen_h149, disp_stp_gen_h150, disp_stp_gen_h151, disp_stp_gen_h152, disp_stp_gen_h153, disp_stp_gen_h154, disp_stp_gen_h155, disp_stp_gen_h156, disp_stp_gen_h157, disp_stp_gen_h158, disp_stp_gen_h159, disp_stp_gen_h160, disp_stp_gen_h161, disp_stp_gen_h162, disp_stp_gen_h163, disp_stp_gen_h164, disp_stp_gen_h165, disp_stp_gen_h166, disp_stp_gen_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

  -- crux workspace addition: the segmented LoadStore decoder leaves a Bool-continuation bind; fold it.
  congr 1
  funext x
  split
  · simp only [bind_assoc, pure_bind, Bool.false_eq_true, ite_false, bind_pure_unit]
  · simp only [pure_bind, ite_true]

#print axioms disp_stp_gen
end ArmCertMem.Disp
