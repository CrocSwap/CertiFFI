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

theorem disp_ldp_sp_h0 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 22 21) : BitVec 2) = 0#2) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h0b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 22 21) : BitVec 2) == 0#2) = false := by
  have := disp_ldp_sp_h0 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h1 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 22 21) : BitVec 2) = 1#2) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h1b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 22 21) : BitVec 2) == 1#2) = false := by
  have := disp_ldp_sp_h1 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h2 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 22 22) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldp_sp_h3 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 22 22) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldp_sp_h4 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 25 25) : BitVec 1) = 0#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldp_sp_h5 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 27 25) : BitVec 3) = 4#3 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h6 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 27 27) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldp_sp_h7 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 28 25) : BitVec 4) = 4#4 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h8 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 28 25) : BitVec 4) = 4#4 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h9 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 28 25) : BitVec 4) = 4#4 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h10 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 28 25) : BitVec 4) = 4#4 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h11 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 28 26) : BitVec 3) = 2#3 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h12 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 28 26) : BitVec 3) = 2#3 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h13 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) = 137183#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h13b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) == 137183#20) = false := by
  have := disp_ldp_sp_h13 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h14 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) = 137215#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h14b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) == 137215#20) = false := by
  have := disp_ldp_sp_h14 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h15 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) = 141279#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h15b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) == 141279#20) = false := by
  have := disp_ldp_sp_h15 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h16 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) = 141311#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h16b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) == 141311#20) = false := by
  have := disp_ldp_sp_h16 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h17 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) = 145375#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h17b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) == 145375#20) = false := by
  have := disp_ldp_sp_h17 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h18 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) = 145407#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h18b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) == 145407#20) = false := by
  have := disp_ldp_sp_h18 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h19 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) = 213089#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h19b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) == 213089#20) = false := by
  have := disp_ldp_sp_h19 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h20 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) = 217185#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 16) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h20b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) == 217185#20) = false := by
  have := disp_ldp_sp_h20 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h21 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) = 417794#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h21b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) == 417794#20) = false := by
  have := disp_ldp_sp_h21 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h22 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) = 421890#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h22b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) == 421890#20) = false := by
  have := disp_ldp_sp_h22 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h23 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) = 929776#20) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h23b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 10) : BitVec 20) == 929776#20) = false := by
  have := disp_ldp_sp_h23 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h24 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) = 49152#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h24b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) == 49152#18) = false := by
  have := disp_ldp_sp_h24 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h25 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) = 49156#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h25b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) == 49156#18) = false := by
  have := disp_ldp_sp_h25 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h26 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) = 49160#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h26b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) == 49160#18) = false := by
  have := disp_ldp_sp_h26 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h27 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) = 50176#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h27b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) == 50176#18) = false := by
  have := disp_ldp_sp_h27 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h28 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) = 50180#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h28b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) == 50180#18) = false := by
  have := disp_ldp_sp_h28 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h29 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) = 50184#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h29b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) == 50184#18) = false := by
  have := disp_ldp_sp_h29 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h30 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) = 54284#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h30b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) == 54284#18) = false := by
  have := disp_ldp_sp_h30 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h31 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) = 54286#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h31b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) == 54286#18) = false := by
  have := disp_ldp_sp_h31 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h32 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) = 54796#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h32b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) == 54796#18) = false := by
  have := disp_ldp_sp_h32 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h33 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) = 54798#18) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h33b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 12) : BitVec 18) == 54798#18) = false := by
  have := disp_ldp_sp_h33 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h34 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 15) : BitVec 15) = 4350#15) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h34b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 15) : BitVec 15) == 4350#15) = false := by
  have := disp_ldp_sp_h34 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h35 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 15) : BitVec 15) = 4351#15) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h35b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 15) : BitVec 15) == 4351#15) = false := by
  have := disp_ldp_sp_h35 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h36 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) = 3072#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h36b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) == 3072#14) = false := by
  have := disp_ldp_sp_h36 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h37 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) = 3136#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h37b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) == 3136#14) = false := by
  have := disp_ldp_sp_h37 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h38 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) = 3328#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h38b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) == 3328#14) = false := by
  have := disp_ldp_sp_h38 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h39 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) = 3360#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h39b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) == 3360#14) = false := by
  have := disp_ldp_sp_h39 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h40 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) = 3392#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h40b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) == 3392#14) = false := by
  have := disp_ldp_sp_h40 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h41 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) = 3424#14) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h41b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 16) : BitVec 14) == 3424#14) = false := by
  have := disp_ldp_sp_h41 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h42 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 64#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h42b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 64#9) = false := by
  have := disp_ldp_sp_h42 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h43 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 65#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h43b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 65#9) = false := by
  have := disp_ldp_sp_h43 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h44 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 100#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h44b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 100#9) = false := by
  have := disp_ldp_sp_h44 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h45 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 102#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h45b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 102#9) = false := by
  have := disp_ldp_sp_h45 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h46 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 108#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h46b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 108#9) = false := by
  have := disp_ldp_sp_h46 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h47 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 109#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h47b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 109#9) = false := by
  have := disp_ldp_sp_h47 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h48 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 110#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h48b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 110#9) = false := by
  have := disp_ldp_sp_h48 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h49 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 111#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h49b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 111#9) = false := by
  have := disp_ldp_sp_h49 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h50 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 200#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h50b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 200#9) = false := by
  have := disp_ldp_sp_h50 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h51 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 202#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h51b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 202#9) = false := by
  have := disp_ldp_sp_h51 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h52 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 206#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h52b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 206#9) = false := by
  have := disp_ldp_sp_h52 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h53 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 238#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h53b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 238#9) = false := by
  have := disp_ldp_sp_h53 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h54 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 448#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h54b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 448#9) = false := by
  have := disp_ldp_sp_h54 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h55 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 449#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h55b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 449#9) = false := by
  have := disp_ldp_sp_h55 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h56 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 450#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h56b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 450#9) = false := by
  have := disp_ldp_sp_h56 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h57 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) = 451#9) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h57b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 21) : BitVec 9) == 451#9) = false := by
  have := disp_ldp_sp_h57 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h58 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 22) : BitVec 8) = 165#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h59 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 22) : BitVec 8) = 165#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h60 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 22) : BitVec 8) = 165#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h61 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 22) : BitVec 8) = 165#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h62 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 22) : BitVec 8) = 165#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h63 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 22) : BitVec 8) = 165#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h64 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 22) : BitVec 8) = 165#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h65 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 22) : BitVec 8) = 165#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h66 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 22) : BitVec 8) = 165#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h67 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 22) : BitVec 8) = 165#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h68 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 23) : BitVec 7) = 82#7 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h69 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 23) : BitVec 7) = 82#7 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h70 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h71 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h72 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h73 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h74 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h75 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h76 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 29 24) : BitVec 6) = 41#6 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h77 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 30 22) : BitVec 9) = 165#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h78 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 30 22) : BitVec 9) = 165#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h79 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 30 22) : BitVec 9) = 165#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h80 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 30 22) : BitVec 9) = 165#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h81 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 30 22) : BitVec 9) = 165#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h82 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 30 22) : BitVec 9) = 165#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h83 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 30 22) : BitVec 9) = 165#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h84 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 30 22) : BitVec 9) = 165#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h85 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 137183#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h85b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 137183#22) = false := by
  have := disp_ldp_sp_h85 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h86 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 137215#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h86b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 137215#22) = false := by
  have := disp_ldp_sp_h86 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h87 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 141279#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h87b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 141279#22) = false := by
  have := disp_ldp_sp_h87 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h88 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 141311#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h88b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 141311#22) = false := by
  have := disp_ldp_sp_h88 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h89 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 145375#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h89b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 145375#22) = false := by
  have := disp_ldp_sp_h89 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h90 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 145407#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h90b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 145407#22) = false := by
  have := disp_ldp_sp_h90 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h91 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 929776#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h91b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 929776#22) = false := by
  have := disp_ldp_sp_h91 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h92 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 1185759#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h92b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 1185759#22) = false := by
  have := disp_ldp_sp_h92 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h93 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 1185791#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h93b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 1185791#22) = false := by
  have := disp_ldp_sp_h93 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h94 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 1189855#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h94b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 1189855#22) = false := by
  have := disp_ldp_sp_h94 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h95 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 1189887#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h95b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 1189887#22) = false := by
  have := disp_ldp_sp_h95 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h96 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 1193951#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h96b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 1193951#22) = false := by
  have := disp_ldp_sp_h96 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h97 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 1193983#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h97b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 1193983#22) = false := by
  have := disp_ldp_sp_h97 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h98 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 1978352#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h98b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 1978352#22) = false := by
  have := disp_ldp_sp_h98 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h99 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 3557315#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h99b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 3557315#22) = false := by
  have := disp_ldp_sp_h99 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h100 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 3557319#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h100b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 3557319#22) = false := by
  have := disp_ldp_sp_h100 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h101 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 3557376#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h101b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 3557376#22) = false := by
  have := disp_ldp_sp_h101 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h102 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 3565568#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h102b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 3565568#22) = false := by
  have := disp_ldp_sp_h102 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h103 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 3569664#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h103b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 3569664#22) = false := by
  have := disp_ldp_sp_h103 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h104 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 4067300#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h104b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 4067300#22) = false := by
  have := disp_ldp_sp_h104 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h105 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) = 4067316#22) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h105b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 10) : BitVec 22) == 4067316#22) = false := by
  have := disp_ldp_sp_h105 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h106 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 64#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h106b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 64#11) = false := by
  have := disp_ldp_sp_h106 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h107 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 200#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h107b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 200#11) = false := by
  have := disp_ldp_sp_h107 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h108 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 202#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h108b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 202#11) = false := by
  have := disp_ldp_sp_h108 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h109 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 448#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h109b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 448#11) = false := by
  have := disp_ldp_sp_h109 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h110 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 449#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h110b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 449#11) = false := by
  have := disp_ldp_sp_h110 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h111 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 450#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h111b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 450#11) = false := by
  have := disp_ldp_sp_h111 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h112 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 451#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h112b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 451#11) = false := by
  have := disp_ldp_sp_h112 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h113 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 576#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h113b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 576#11) = false := by
  have := disp_ldp_sp_h113 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h114 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 712#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h114b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 712#11) = false := by
  have := disp_ldp_sp_h114 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h115 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 714#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h115b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 714#11) = false := by
  have := disp_ldp_sp_h115 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h116 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 960#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h116b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 960#11) = false := by
  have := disp_ldp_sp_h116 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h117 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 961#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h117b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 961#11) = false := by
  have := disp_ldp_sp_h117 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h118 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 962#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h118b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 962#11) = false := by
  have := disp_ldp_sp_h118 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h119 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 963#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h119b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 963#11) = false := by
  have := disp_ldp_sp_h119 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h120 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 1228#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h120b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 1228#11) = false := by
  have := disp_ldp_sp_h120 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h121 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 1476#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h121b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 1476#11) = false := by
  have := disp_ldp_sp_h121 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h122 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 1477#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h122b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 1477#11) = false := by
  have := disp_ldp_sp_h122 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h123 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 1737#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h123b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 1737#11) = false := by
  have := disp_ldp_sp_h123 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h124 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 1739#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h124b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 1739#11) = false := by
  have := disp_ldp_sp_h124 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h125 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 1741#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h125b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 1741#11) = false := by
  have := disp_ldp_sp_h125 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h126 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 1743#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h126b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 1743#11) = false := by
  have := disp_ldp_sp_h126 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h127 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 1985#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h127b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 1985#11) = false := by
  have := disp_ldp_sp_h127 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h128 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 1988#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h128b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 1988#11) = false := by
  have := disp_ldp_sp_h128 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h129 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) = 1989#11) := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldp_sp_h129b (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 21) : BitVec 11) == 1989#11) = false := by
  have := disp_ldp_sp_h129 imm7 Rt2 Rt
  simpa using this

theorem disp_ldp_sp_h130 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h131 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h132 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h133 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h134 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h135 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h136 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h137 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h138 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h139 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h140 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h141 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 22) : BitVec 10) = 677#10 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h142 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h143 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h144 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h145 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h146 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h147 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h148 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h149 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 23) : BitVec 9) = 338#9 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h150 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h151 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h152 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h153 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h154 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h155 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h156 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 24) : BitVec 8) = 169#8 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h157 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldp_sp_h158 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 31 31) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldp_sp_h159 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 0 5 = Rt := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    bv_field

theorem disp_ldp_sp_h160 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 5 5 = 31#5 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem disp_ldp_sp_h161 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 10 5 = Rt2 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    bv_field

theorem disp_ldp_sp_h162 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 15 7 = imm7 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    bv_field

theorem disp_ldp_sp_h163 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 22 1 = 1#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldp_sp_h164 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 22 2 = 1#2 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldp_sp_h165 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 23 1 = 0#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldp_sp_h166 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 30 1 = 0#1 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldp_sp_h167 (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) 30 2 = 2#2 := by
    unfold CryptoMem.LdstPair.ldstPairOffWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldp_sp (pc : Int) (imm7 : BitVec 7) (Rt2 : BitVec 5) (Rt : BitVec 5) :
    __DecodeA64 (real := real) pc (CryptoMem.LdstPair.ldstPairOffWord 2#2 1#1 imm7 Rt2 31#5 Rt) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 611))
      if c = true then (do writeReg Register.SEE 611; decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  try simp (config := {decide := true}) only [disp_ldp_sp_h0, disp_ldp_sp_h0b, disp_ldp_sp_h1, disp_ldp_sp_h1b, disp_ldp_sp_h2, disp_ldp_sp_h3, disp_ldp_sp_h4, disp_ldp_sp_h5, disp_ldp_sp_h6, disp_ldp_sp_h7, disp_ldp_sp_h8, disp_ldp_sp_h9, disp_ldp_sp_h10, disp_ldp_sp_h11, disp_ldp_sp_h12, disp_ldp_sp_h13, disp_ldp_sp_h13b, disp_ldp_sp_h14, disp_ldp_sp_h14b, disp_ldp_sp_h15, disp_ldp_sp_h15b, disp_ldp_sp_h16, disp_ldp_sp_h16b, disp_ldp_sp_h17, disp_ldp_sp_h17b, disp_ldp_sp_h18, disp_ldp_sp_h18b, disp_ldp_sp_h19, disp_ldp_sp_h19b, disp_ldp_sp_h20, disp_ldp_sp_h20b, disp_ldp_sp_h21, disp_ldp_sp_h21b, disp_ldp_sp_h22, disp_ldp_sp_h22b, disp_ldp_sp_h23, disp_ldp_sp_h23b, disp_ldp_sp_h24, disp_ldp_sp_h24b, disp_ldp_sp_h25, disp_ldp_sp_h25b, disp_ldp_sp_h26, disp_ldp_sp_h26b, disp_ldp_sp_h27, disp_ldp_sp_h27b, disp_ldp_sp_h28, disp_ldp_sp_h28b, disp_ldp_sp_h29, disp_ldp_sp_h29b, disp_ldp_sp_h30, disp_ldp_sp_h30b, disp_ldp_sp_h31, disp_ldp_sp_h31b, disp_ldp_sp_h32, disp_ldp_sp_h32b, disp_ldp_sp_h33, disp_ldp_sp_h33b, disp_ldp_sp_h34, disp_ldp_sp_h34b, disp_ldp_sp_h35, disp_ldp_sp_h35b, disp_ldp_sp_h36, disp_ldp_sp_h36b, disp_ldp_sp_h37, disp_ldp_sp_h37b, disp_ldp_sp_h38, disp_ldp_sp_h38b, disp_ldp_sp_h39, disp_ldp_sp_h39b, disp_ldp_sp_h40, disp_ldp_sp_h40b, disp_ldp_sp_h41, disp_ldp_sp_h41b, disp_ldp_sp_h42, disp_ldp_sp_h42b, disp_ldp_sp_h43, disp_ldp_sp_h43b, disp_ldp_sp_h44, disp_ldp_sp_h44b, disp_ldp_sp_h45, disp_ldp_sp_h45b, disp_ldp_sp_h46, disp_ldp_sp_h46b, disp_ldp_sp_h47, disp_ldp_sp_h47b, disp_ldp_sp_h48, disp_ldp_sp_h48b, disp_ldp_sp_h49, disp_ldp_sp_h49b, disp_ldp_sp_h50, disp_ldp_sp_h50b, disp_ldp_sp_h51, disp_ldp_sp_h51b, disp_ldp_sp_h52, disp_ldp_sp_h52b, disp_ldp_sp_h53, disp_ldp_sp_h53b, disp_ldp_sp_h54, disp_ldp_sp_h54b, disp_ldp_sp_h55, disp_ldp_sp_h55b, disp_ldp_sp_h56, disp_ldp_sp_h56b, disp_ldp_sp_h57, disp_ldp_sp_h57b, disp_ldp_sp_h58, disp_ldp_sp_h59, disp_ldp_sp_h60, disp_ldp_sp_h61, disp_ldp_sp_h62, disp_ldp_sp_h63, disp_ldp_sp_h64, disp_ldp_sp_h65, disp_ldp_sp_h66, disp_ldp_sp_h67, disp_ldp_sp_h68, disp_ldp_sp_h69, disp_ldp_sp_h70, disp_ldp_sp_h71, disp_ldp_sp_h72, disp_ldp_sp_h73, disp_ldp_sp_h74, disp_ldp_sp_h75, disp_ldp_sp_h76, disp_ldp_sp_h77, disp_ldp_sp_h78, disp_ldp_sp_h79, disp_ldp_sp_h80, disp_ldp_sp_h81, disp_ldp_sp_h82, disp_ldp_sp_h83, disp_ldp_sp_h84, disp_ldp_sp_h85, disp_ldp_sp_h85b, disp_ldp_sp_h86, disp_ldp_sp_h86b, disp_ldp_sp_h87, disp_ldp_sp_h87b, disp_ldp_sp_h88, disp_ldp_sp_h88b, disp_ldp_sp_h89, disp_ldp_sp_h89b, disp_ldp_sp_h90, disp_ldp_sp_h90b, disp_ldp_sp_h91, disp_ldp_sp_h91b, disp_ldp_sp_h92, disp_ldp_sp_h92b, disp_ldp_sp_h93, disp_ldp_sp_h93b, disp_ldp_sp_h94, disp_ldp_sp_h94b, disp_ldp_sp_h95, disp_ldp_sp_h95b, disp_ldp_sp_h96, disp_ldp_sp_h96b, disp_ldp_sp_h97, disp_ldp_sp_h97b, disp_ldp_sp_h98, disp_ldp_sp_h98b, disp_ldp_sp_h99, disp_ldp_sp_h99b, disp_ldp_sp_h100, disp_ldp_sp_h100b, disp_ldp_sp_h101, disp_ldp_sp_h101b, disp_ldp_sp_h102, disp_ldp_sp_h102b, disp_ldp_sp_h103, disp_ldp_sp_h103b, disp_ldp_sp_h104, disp_ldp_sp_h104b, disp_ldp_sp_h105, disp_ldp_sp_h105b, disp_ldp_sp_h106, disp_ldp_sp_h106b, disp_ldp_sp_h107, disp_ldp_sp_h107b, disp_ldp_sp_h108, disp_ldp_sp_h108b, disp_ldp_sp_h109, disp_ldp_sp_h109b, disp_ldp_sp_h110, disp_ldp_sp_h110b, disp_ldp_sp_h111, disp_ldp_sp_h111b, disp_ldp_sp_h112, disp_ldp_sp_h112b, disp_ldp_sp_h113, disp_ldp_sp_h113b, disp_ldp_sp_h114, disp_ldp_sp_h114b, disp_ldp_sp_h115, disp_ldp_sp_h115b, disp_ldp_sp_h116, disp_ldp_sp_h116b, disp_ldp_sp_h117, disp_ldp_sp_h117b, disp_ldp_sp_h118, disp_ldp_sp_h118b, disp_ldp_sp_h119, disp_ldp_sp_h119b, disp_ldp_sp_h120, disp_ldp_sp_h120b, disp_ldp_sp_h121, disp_ldp_sp_h121b, disp_ldp_sp_h122, disp_ldp_sp_h122b, disp_ldp_sp_h123, disp_ldp_sp_h123b, disp_ldp_sp_h124, disp_ldp_sp_h124b, disp_ldp_sp_h125, disp_ldp_sp_h125b, disp_ldp_sp_h126, disp_ldp_sp_h126b, disp_ldp_sp_h127, disp_ldp_sp_h127b, disp_ldp_sp_h128, disp_ldp_sp_h128b, disp_ldp_sp_h129, disp_ldp_sp_h129b, disp_ldp_sp_h130, disp_ldp_sp_h131, disp_ldp_sp_h132, disp_ldp_sp_h133, disp_ldp_sp_h134, disp_ldp_sp_h135, disp_ldp_sp_h136, disp_ldp_sp_h137, disp_ldp_sp_h138, disp_ldp_sp_h139, disp_ldp_sp_h140, disp_ldp_sp_h141, disp_ldp_sp_h142, disp_ldp_sp_h143, disp_ldp_sp_h144, disp_ldp_sp_h145, disp_ldp_sp_h146, disp_ldp_sp_h147, disp_ldp_sp_h148, disp_ldp_sp_h149, disp_ldp_sp_h150, disp_ldp_sp_h151, disp_ldp_sp_h152, disp_ldp_sp_h153, disp_ldp_sp_h154, disp_ldp_sp_h155, disp_ldp_sp_h156, disp_ldp_sp_h157, disp_ldp_sp_h158, disp_ldp_sp_h159, disp_ldp_sp_h160, disp_ldp_sp_h161, disp_ldp_sp_h162, disp_ldp_sp_h163, disp_ldp_sp_h164, disp_ldp_sp_h165, disp_ldp_sp_h166, disp_ldp_sp_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore
  try simp (config := {decide := true}) only [disp_ldp_sp_h0, disp_ldp_sp_h0b, disp_ldp_sp_h1, disp_ldp_sp_h1b, disp_ldp_sp_h2, disp_ldp_sp_h3, disp_ldp_sp_h4, disp_ldp_sp_h5, disp_ldp_sp_h6, disp_ldp_sp_h7, disp_ldp_sp_h8, disp_ldp_sp_h9, disp_ldp_sp_h10, disp_ldp_sp_h11, disp_ldp_sp_h12, disp_ldp_sp_h13, disp_ldp_sp_h13b, disp_ldp_sp_h14, disp_ldp_sp_h14b, disp_ldp_sp_h15, disp_ldp_sp_h15b, disp_ldp_sp_h16, disp_ldp_sp_h16b, disp_ldp_sp_h17, disp_ldp_sp_h17b, disp_ldp_sp_h18, disp_ldp_sp_h18b, disp_ldp_sp_h19, disp_ldp_sp_h19b, disp_ldp_sp_h20, disp_ldp_sp_h20b, disp_ldp_sp_h21, disp_ldp_sp_h21b, disp_ldp_sp_h22, disp_ldp_sp_h22b, disp_ldp_sp_h23, disp_ldp_sp_h23b, disp_ldp_sp_h24, disp_ldp_sp_h24b, disp_ldp_sp_h25, disp_ldp_sp_h25b, disp_ldp_sp_h26, disp_ldp_sp_h26b, disp_ldp_sp_h27, disp_ldp_sp_h27b, disp_ldp_sp_h28, disp_ldp_sp_h28b, disp_ldp_sp_h29, disp_ldp_sp_h29b, disp_ldp_sp_h30, disp_ldp_sp_h30b, disp_ldp_sp_h31, disp_ldp_sp_h31b, disp_ldp_sp_h32, disp_ldp_sp_h32b, disp_ldp_sp_h33, disp_ldp_sp_h33b, disp_ldp_sp_h34, disp_ldp_sp_h34b, disp_ldp_sp_h35, disp_ldp_sp_h35b, disp_ldp_sp_h36, disp_ldp_sp_h36b, disp_ldp_sp_h37, disp_ldp_sp_h37b, disp_ldp_sp_h38, disp_ldp_sp_h38b, disp_ldp_sp_h39, disp_ldp_sp_h39b, disp_ldp_sp_h40, disp_ldp_sp_h40b, disp_ldp_sp_h41, disp_ldp_sp_h41b, disp_ldp_sp_h42, disp_ldp_sp_h42b, disp_ldp_sp_h43, disp_ldp_sp_h43b, disp_ldp_sp_h44, disp_ldp_sp_h44b, disp_ldp_sp_h45, disp_ldp_sp_h45b, disp_ldp_sp_h46, disp_ldp_sp_h46b, disp_ldp_sp_h47, disp_ldp_sp_h47b, disp_ldp_sp_h48, disp_ldp_sp_h48b, disp_ldp_sp_h49, disp_ldp_sp_h49b, disp_ldp_sp_h50, disp_ldp_sp_h50b, disp_ldp_sp_h51, disp_ldp_sp_h51b, disp_ldp_sp_h52, disp_ldp_sp_h52b, disp_ldp_sp_h53, disp_ldp_sp_h53b, disp_ldp_sp_h54, disp_ldp_sp_h54b, disp_ldp_sp_h55, disp_ldp_sp_h55b, disp_ldp_sp_h56, disp_ldp_sp_h56b, disp_ldp_sp_h57, disp_ldp_sp_h57b, disp_ldp_sp_h58, disp_ldp_sp_h59, disp_ldp_sp_h60, disp_ldp_sp_h61, disp_ldp_sp_h62, disp_ldp_sp_h63, disp_ldp_sp_h64, disp_ldp_sp_h65, disp_ldp_sp_h66, disp_ldp_sp_h67, disp_ldp_sp_h68, disp_ldp_sp_h69, disp_ldp_sp_h70, disp_ldp_sp_h71, disp_ldp_sp_h72, disp_ldp_sp_h73, disp_ldp_sp_h74, disp_ldp_sp_h75, disp_ldp_sp_h76, disp_ldp_sp_h77, disp_ldp_sp_h78, disp_ldp_sp_h79, disp_ldp_sp_h80, disp_ldp_sp_h81, disp_ldp_sp_h82, disp_ldp_sp_h83, disp_ldp_sp_h84, disp_ldp_sp_h85, disp_ldp_sp_h85b, disp_ldp_sp_h86, disp_ldp_sp_h86b, disp_ldp_sp_h87, disp_ldp_sp_h87b, disp_ldp_sp_h88, disp_ldp_sp_h88b, disp_ldp_sp_h89, disp_ldp_sp_h89b, disp_ldp_sp_h90, disp_ldp_sp_h90b, disp_ldp_sp_h91, disp_ldp_sp_h91b, disp_ldp_sp_h92, disp_ldp_sp_h92b, disp_ldp_sp_h93, disp_ldp_sp_h93b, disp_ldp_sp_h94, disp_ldp_sp_h94b, disp_ldp_sp_h95, disp_ldp_sp_h95b, disp_ldp_sp_h96, disp_ldp_sp_h96b, disp_ldp_sp_h97, disp_ldp_sp_h97b, disp_ldp_sp_h98, disp_ldp_sp_h98b, disp_ldp_sp_h99, disp_ldp_sp_h99b, disp_ldp_sp_h100, disp_ldp_sp_h100b, disp_ldp_sp_h101, disp_ldp_sp_h101b, disp_ldp_sp_h102, disp_ldp_sp_h102b, disp_ldp_sp_h103, disp_ldp_sp_h103b, disp_ldp_sp_h104, disp_ldp_sp_h104b, disp_ldp_sp_h105, disp_ldp_sp_h105b, disp_ldp_sp_h106, disp_ldp_sp_h106b, disp_ldp_sp_h107, disp_ldp_sp_h107b, disp_ldp_sp_h108, disp_ldp_sp_h108b, disp_ldp_sp_h109, disp_ldp_sp_h109b, disp_ldp_sp_h110, disp_ldp_sp_h110b, disp_ldp_sp_h111, disp_ldp_sp_h111b, disp_ldp_sp_h112, disp_ldp_sp_h112b, disp_ldp_sp_h113, disp_ldp_sp_h113b, disp_ldp_sp_h114, disp_ldp_sp_h114b, disp_ldp_sp_h115, disp_ldp_sp_h115b, disp_ldp_sp_h116, disp_ldp_sp_h116b, disp_ldp_sp_h117, disp_ldp_sp_h117b, disp_ldp_sp_h118, disp_ldp_sp_h118b, disp_ldp_sp_h119, disp_ldp_sp_h119b, disp_ldp_sp_h120, disp_ldp_sp_h120b, disp_ldp_sp_h121, disp_ldp_sp_h121b, disp_ldp_sp_h122, disp_ldp_sp_h122b, disp_ldp_sp_h123, disp_ldp_sp_h123b, disp_ldp_sp_h124, disp_ldp_sp_h124b, disp_ldp_sp_h125, disp_ldp_sp_h125b, disp_ldp_sp_h126, disp_ldp_sp_h126b, disp_ldp_sp_h127, disp_ldp_sp_h127b, disp_ldp_sp_h128, disp_ldp_sp_h128b, disp_ldp_sp_h129, disp_ldp_sp_h129b, disp_ldp_sp_h130, disp_ldp_sp_h131, disp_ldp_sp_h132, disp_ldp_sp_h133, disp_ldp_sp_h134, disp_ldp_sp_h135, disp_ldp_sp_h136, disp_ldp_sp_h137, disp_ldp_sp_h138, disp_ldp_sp_h139, disp_ldp_sp_h140, disp_ldp_sp_h141, disp_ldp_sp_h142, disp_ldp_sp_h143, disp_ldp_sp_h144, disp_ldp_sp_h145, disp_ldp_sp_h146, disp_ldp_sp_h147, disp_ldp_sp_h148, disp_ldp_sp_h149, disp_ldp_sp_h150, disp_ldp_sp_h151, disp_ldp_sp_h152, disp_ldp_sp_h153, disp_ldp_sp_h154, disp_ldp_sp_h155, disp_ldp_sp_h156, disp_ldp_sp_h157, disp_ldp_sp_h158, disp_ldp_sp_h159, disp_ldp_sp_h160, disp_ldp_sp_h161, disp_ldp_sp_h162, disp_ldp_sp_h163, disp_ldp_sp_h164, disp_ldp_sp_h165, disp_ldp_sp_h166, disp_ldp_sp_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg0
  try simp (config := {decide := true}) only [disp_ldp_sp_h0, disp_ldp_sp_h0b, disp_ldp_sp_h1, disp_ldp_sp_h1b, disp_ldp_sp_h2, disp_ldp_sp_h3, disp_ldp_sp_h4, disp_ldp_sp_h5, disp_ldp_sp_h6, disp_ldp_sp_h7, disp_ldp_sp_h8, disp_ldp_sp_h9, disp_ldp_sp_h10, disp_ldp_sp_h11, disp_ldp_sp_h12, disp_ldp_sp_h13, disp_ldp_sp_h13b, disp_ldp_sp_h14, disp_ldp_sp_h14b, disp_ldp_sp_h15, disp_ldp_sp_h15b, disp_ldp_sp_h16, disp_ldp_sp_h16b, disp_ldp_sp_h17, disp_ldp_sp_h17b, disp_ldp_sp_h18, disp_ldp_sp_h18b, disp_ldp_sp_h19, disp_ldp_sp_h19b, disp_ldp_sp_h20, disp_ldp_sp_h20b, disp_ldp_sp_h21, disp_ldp_sp_h21b, disp_ldp_sp_h22, disp_ldp_sp_h22b, disp_ldp_sp_h23, disp_ldp_sp_h23b, disp_ldp_sp_h24, disp_ldp_sp_h24b, disp_ldp_sp_h25, disp_ldp_sp_h25b, disp_ldp_sp_h26, disp_ldp_sp_h26b, disp_ldp_sp_h27, disp_ldp_sp_h27b, disp_ldp_sp_h28, disp_ldp_sp_h28b, disp_ldp_sp_h29, disp_ldp_sp_h29b, disp_ldp_sp_h30, disp_ldp_sp_h30b, disp_ldp_sp_h31, disp_ldp_sp_h31b, disp_ldp_sp_h32, disp_ldp_sp_h32b, disp_ldp_sp_h33, disp_ldp_sp_h33b, disp_ldp_sp_h34, disp_ldp_sp_h34b, disp_ldp_sp_h35, disp_ldp_sp_h35b, disp_ldp_sp_h36, disp_ldp_sp_h36b, disp_ldp_sp_h37, disp_ldp_sp_h37b, disp_ldp_sp_h38, disp_ldp_sp_h38b, disp_ldp_sp_h39, disp_ldp_sp_h39b, disp_ldp_sp_h40, disp_ldp_sp_h40b, disp_ldp_sp_h41, disp_ldp_sp_h41b, disp_ldp_sp_h42, disp_ldp_sp_h42b, disp_ldp_sp_h43, disp_ldp_sp_h43b, disp_ldp_sp_h44, disp_ldp_sp_h44b, disp_ldp_sp_h45, disp_ldp_sp_h45b, disp_ldp_sp_h46, disp_ldp_sp_h46b, disp_ldp_sp_h47, disp_ldp_sp_h47b, disp_ldp_sp_h48, disp_ldp_sp_h48b, disp_ldp_sp_h49, disp_ldp_sp_h49b, disp_ldp_sp_h50, disp_ldp_sp_h50b, disp_ldp_sp_h51, disp_ldp_sp_h51b, disp_ldp_sp_h52, disp_ldp_sp_h52b, disp_ldp_sp_h53, disp_ldp_sp_h53b, disp_ldp_sp_h54, disp_ldp_sp_h54b, disp_ldp_sp_h55, disp_ldp_sp_h55b, disp_ldp_sp_h56, disp_ldp_sp_h56b, disp_ldp_sp_h57, disp_ldp_sp_h57b, disp_ldp_sp_h58, disp_ldp_sp_h59, disp_ldp_sp_h60, disp_ldp_sp_h61, disp_ldp_sp_h62, disp_ldp_sp_h63, disp_ldp_sp_h64, disp_ldp_sp_h65, disp_ldp_sp_h66, disp_ldp_sp_h67, disp_ldp_sp_h68, disp_ldp_sp_h69, disp_ldp_sp_h70, disp_ldp_sp_h71, disp_ldp_sp_h72, disp_ldp_sp_h73, disp_ldp_sp_h74, disp_ldp_sp_h75, disp_ldp_sp_h76, disp_ldp_sp_h77, disp_ldp_sp_h78, disp_ldp_sp_h79, disp_ldp_sp_h80, disp_ldp_sp_h81, disp_ldp_sp_h82, disp_ldp_sp_h83, disp_ldp_sp_h84, disp_ldp_sp_h85, disp_ldp_sp_h85b, disp_ldp_sp_h86, disp_ldp_sp_h86b, disp_ldp_sp_h87, disp_ldp_sp_h87b, disp_ldp_sp_h88, disp_ldp_sp_h88b, disp_ldp_sp_h89, disp_ldp_sp_h89b, disp_ldp_sp_h90, disp_ldp_sp_h90b, disp_ldp_sp_h91, disp_ldp_sp_h91b, disp_ldp_sp_h92, disp_ldp_sp_h92b, disp_ldp_sp_h93, disp_ldp_sp_h93b, disp_ldp_sp_h94, disp_ldp_sp_h94b, disp_ldp_sp_h95, disp_ldp_sp_h95b, disp_ldp_sp_h96, disp_ldp_sp_h96b, disp_ldp_sp_h97, disp_ldp_sp_h97b, disp_ldp_sp_h98, disp_ldp_sp_h98b, disp_ldp_sp_h99, disp_ldp_sp_h99b, disp_ldp_sp_h100, disp_ldp_sp_h100b, disp_ldp_sp_h101, disp_ldp_sp_h101b, disp_ldp_sp_h102, disp_ldp_sp_h102b, disp_ldp_sp_h103, disp_ldp_sp_h103b, disp_ldp_sp_h104, disp_ldp_sp_h104b, disp_ldp_sp_h105, disp_ldp_sp_h105b, disp_ldp_sp_h106, disp_ldp_sp_h106b, disp_ldp_sp_h107, disp_ldp_sp_h107b, disp_ldp_sp_h108, disp_ldp_sp_h108b, disp_ldp_sp_h109, disp_ldp_sp_h109b, disp_ldp_sp_h110, disp_ldp_sp_h110b, disp_ldp_sp_h111, disp_ldp_sp_h111b, disp_ldp_sp_h112, disp_ldp_sp_h112b, disp_ldp_sp_h113, disp_ldp_sp_h113b, disp_ldp_sp_h114, disp_ldp_sp_h114b, disp_ldp_sp_h115, disp_ldp_sp_h115b, disp_ldp_sp_h116, disp_ldp_sp_h116b, disp_ldp_sp_h117, disp_ldp_sp_h117b, disp_ldp_sp_h118, disp_ldp_sp_h118b, disp_ldp_sp_h119, disp_ldp_sp_h119b, disp_ldp_sp_h120, disp_ldp_sp_h120b, disp_ldp_sp_h121, disp_ldp_sp_h121b, disp_ldp_sp_h122, disp_ldp_sp_h122b, disp_ldp_sp_h123, disp_ldp_sp_h123b, disp_ldp_sp_h124, disp_ldp_sp_h124b, disp_ldp_sp_h125, disp_ldp_sp_h125b, disp_ldp_sp_h126, disp_ldp_sp_h126b, disp_ldp_sp_h127, disp_ldp_sp_h127b, disp_ldp_sp_h128, disp_ldp_sp_h128b, disp_ldp_sp_h129, disp_ldp_sp_h129b, disp_ldp_sp_h130, disp_ldp_sp_h131, disp_ldp_sp_h132, disp_ldp_sp_h133, disp_ldp_sp_h134, disp_ldp_sp_h135, disp_ldp_sp_h136, disp_ldp_sp_h137, disp_ldp_sp_h138, disp_ldp_sp_h139, disp_ldp_sp_h140, disp_ldp_sp_h141, disp_ldp_sp_h142, disp_ldp_sp_h143, disp_ldp_sp_h144, disp_ldp_sp_h145, disp_ldp_sp_h146, disp_ldp_sp_h147, disp_ldp_sp_h148, disp_ldp_sp_h149, disp_ldp_sp_h150, disp_ldp_sp_h151, disp_ldp_sp_h152, disp_ldp_sp_h153, disp_ldp_sp_h154, disp_ldp_sp_h155, disp_ldp_sp_h156, disp_ldp_sp_h157, disp_ldp_sp_h158, disp_ldp_sp_h159, disp_ldp_sp_h160, disp_ldp_sp_h161, disp_ldp_sp_h162, disp_ldp_sp_h163, disp_ldp_sp_h164, disp_ldp_sp_h165, disp_ldp_sp_h166, disp_ldp_sp_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg1
  try simp (config := {decide := true}) only [disp_ldp_sp_h0, disp_ldp_sp_h0b, disp_ldp_sp_h1, disp_ldp_sp_h1b, disp_ldp_sp_h2, disp_ldp_sp_h3, disp_ldp_sp_h4, disp_ldp_sp_h5, disp_ldp_sp_h6, disp_ldp_sp_h7, disp_ldp_sp_h8, disp_ldp_sp_h9, disp_ldp_sp_h10, disp_ldp_sp_h11, disp_ldp_sp_h12, disp_ldp_sp_h13, disp_ldp_sp_h13b, disp_ldp_sp_h14, disp_ldp_sp_h14b, disp_ldp_sp_h15, disp_ldp_sp_h15b, disp_ldp_sp_h16, disp_ldp_sp_h16b, disp_ldp_sp_h17, disp_ldp_sp_h17b, disp_ldp_sp_h18, disp_ldp_sp_h18b, disp_ldp_sp_h19, disp_ldp_sp_h19b, disp_ldp_sp_h20, disp_ldp_sp_h20b, disp_ldp_sp_h21, disp_ldp_sp_h21b, disp_ldp_sp_h22, disp_ldp_sp_h22b, disp_ldp_sp_h23, disp_ldp_sp_h23b, disp_ldp_sp_h24, disp_ldp_sp_h24b, disp_ldp_sp_h25, disp_ldp_sp_h25b, disp_ldp_sp_h26, disp_ldp_sp_h26b, disp_ldp_sp_h27, disp_ldp_sp_h27b, disp_ldp_sp_h28, disp_ldp_sp_h28b, disp_ldp_sp_h29, disp_ldp_sp_h29b, disp_ldp_sp_h30, disp_ldp_sp_h30b, disp_ldp_sp_h31, disp_ldp_sp_h31b, disp_ldp_sp_h32, disp_ldp_sp_h32b, disp_ldp_sp_h33, disp_ldp_sp_h33b, disp_ldp_sp_h34, disp_ldp_sp_h34b, disp_ldp_sp_h35, disp_ldp_sp_h35b, disp_ldp_sp_h36, disp_ldp_sp_h36b, disp_ldp_sp_h37, disp_ldp_sp_h37b, disp_ldp_sp_h38, disp_ldp_sp_h38b, disp_ldp_sp_h39, disp_ldp_sp_h39b, disp_ldp_sp_h40, disp_ldp_sp_h40b, disp_ldp_sp_h41, disp_ldp_sp_h41b, disp_ldp_sp_h42, disp_ldp_sp_h42b, disp_ldp_sp_h43, disp_ldp_sp_h43b, disp_ldp_sp_h44, disp_ldp_sp_h44b, disp_ldp_sp_h45, disp_ldp_sp_h45b, disp_ldp_sp_h46, disp_ldp_sp_h46b, disp_ldp_sp_h47, disp_ldp_sp_h47b, disp_ldp_sp_h48, disp_ldp_sp_h48b, disp_ldp_sp_h49, disp_ldp_sp_h49b, disp_ldp_sp_h50, disp_ldp_sp_h50b, disp_ldp_sp_h51, disp_ldp_sp_h51b, disp_ldp_sp_h52, disp_ldp_sp_h52b, disp_ldp_sp_h53, disp_ldp_sp_h53b, disp_ldp_sp_h54, disp_ldp_sp_h54b, disp_ldp_sp_h55, disp_ldp_sp_h55b, disp_ldp_sp_h56, disp_ldp_sp_h56b, disp_ldp_sp_h57, disp_ldp_sp_h57b, disp_ldp_sp_h58, disp_ldp_sp_h59, disp_ldp_sp_h60, disp_ldp_sp_h61, disp_ldp_sp_h62, disp_ldp_sp_h63, disp_ldp_sp_h64, disp_ldp_sp_h65, disp_ldp_sp_h66, disp_ldp_sp_h67, disp_ldp_sp_h68, disp_ldp_sp_h69, disp_ldp_sp_h70, disp_ldp_sp_h71, disp_ldp_sp_h72, disp_ldp_sp_h73, disp_ldp_sp_h74, disp_ldp_sp_h75, disp_ldp_sp_h76, disp_ldp_sp_h77, disp_ldp_sp_h78, disp_ldp_sp_h79, disp_ldp_sp_h80, disp_ldp_sp_h81, disp_ldp_sp_h82, disp_ldp_sp_h83, disp_ldp_sp_h84, disp_ldp_sp_h85, disp_ldp_sp_h85b, disp_ldp_sp_h86, disp_ldp_sp_h86b, disp_ldp_sp_h87, disp_ldp_sp_h87b, disp_ldp_sp_h88, disp_ldp_sp_h88b, disp_ldp_sp_h89, disp_ldp_sp_h89b, disp_ldp_sp_h90, disp_ldp_sp_h90b, disp_ldp_sp_h91, disp_ldp_sp_h91b, disp_ldp_sp_h92, disp_ldp_sp_h92b, disp_ldp_sp_h93, disp_ldp_sp_h93b, disp_ldp_sp_h94, disp_ldp_sp_h94b, disp_ldp_sp_h95, disp_ldp_sp_h95b, disp_ldp_sp_h96, disp_ldp_sp_h96b, disp_ldp_sp_h97, disp_ldp_sp_h97b, disp_ldp_sp_h98, disp_ldp_sp_h98b, disp_ldp_sp_h99, disp_ldp_sp_h99b, disp_ldp_sp_h100, disp_ldp_sp_h100b, disp_ldp_sp_h101, disp_ldp_sp_h101b, disp_ldp_sp_h102, disp_ldp_sp_h102b, disp_ldp_sp_h103, disp_ldp_sp_h103b, disp_ldp_sp_h104, disp_ldp_sp_h104b, disp_ldp_sp_h105, disp_ldp_sp_h105b, disp_ldp_sp_h106, disp_ldp_sp_h106b, disp_ldp_sp_h107, disp_ldp_sp_h107b, disp_ldp_sp_h108, disp_ldp_sp_h108b, disp_ldp_sp_h109, disp_ldp_sp_h109b, disp_ldp_sp_h110, disp_ldp_sp_h110b, disp_ldp_sp_h111, disp_ldp_sp_h111b, disp_ldp_sp_h112, disp_ldp_sp_h112b, disp_ldp_sp_h113, disp_ldp_sp_h113b, disp_ldp_sp_h114, disp_ldp_sp_h114b, disp_ldp_sp_h115, disp_ldp_sp_h115b, disp_ldp_sp_h116, disp_ldp_sp_h116b, disp_ldp_sp_h117, disp_ldp_sp_h117b, disp_ldp_sp_h118, disp_ldp_sp_h118b, disp_ldp_sp_h119, disp_ldp_sp_h119b, disp_ldp_sp_h120, disp_ldp_sp_h120b, disp_ldp_sp_h121, disp_ldp_sp_h121b, disp_ldp_sp_h122, disp_ldp_sp_h122b, disp_ldp_sp_h123, disp_ldp_sp_h123b, disp_ldp_sp_h124, disp_ldp_sp_h124b, disp_ldp_sp_h125, disp_ldp_sp_h125b, disp_ldp_sp_h126, disp_ldp_sp_h126b, disp_ldp_sp_h127, disp_ldp_sp_h127b, disp_ldp_sp_h128, disp_ldp_sp_h128b, disp_ldp_sp_h129, disp_ldp_sp_h129b, disp_ldp_sp_h130, disp_ldp_sp_h131, disp_ldp_sp_h132, disp_ldp_sp_h133, disp_ldp_sp_h134, disp_ldp_sp_h135, disp_ldp_sp_h136, disp_ldp_sp_h137, disp_ldp_sp_h138, disp_ldp_sp_h139, disp_ldp_sp_h140, disp_ldp_sp_h141, disp_ldp_sp_h142, disp_ldp_sp_h143, disp_ldp_sp_h144, disp_ldp_sp_h145, disp_ldp_sp_h146, disp_ldp_sp_h147, disp_ldp_sp_h148, disp_ldp_sp_h149, disp_ldp_sp_h150, disp_ldp_sp_h151, disp_ldp_sp_h152, disp_ldp_sp_h153, disp_ldp_sp_h154, disp_ldp_sp_h155, disp_ldp_sp_h156, disp_ldp_sp_h157, disp_ldp_sp_h158, disp_ldp_sp_h159, disp_ldp_sp_h160, disp_ldp_sp_h161, disp_ldp_sp_h162, disp_ldp_sp_h163, disp_ldp_sp_h164, disp_ldp_sp_h165, disp_ldp_sp_h166, disp_ldp_sp_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg2
  try simp (config := {decide := true}) only [disp_ldp_sp_h0, disp_ldp_sp_h0b, disp_ldp_sp_h1, disp_ldp_sp_h1b, disp_ldp_sp_h2, disp_ldp_sp_h3, disp_ldp_sp_h4, disp_ldp_sp_h5, disp_ldp_sp_h6, disp_ldp_sp_h7, disp_ldp_sp_h8, disp_ldp_sp_h9, disp_ldp_sp_h10, disp_ldp_sp_h11, disp_ldp_sp_h12, disp_ldp_sp_h13, disp_ldp_sp_h13b, disp_ldp_sp_h14, disp_ldp_sp_h14b, disp_ldp_sp_h15, disp_ldp_sp_h15b, disp_ldp_sp_h16, disp_ldp_sp_h16b, disp_ldp_sp_h17, disp_ldp_sp_h17b, disp_ldp_sp_h18, disp_ldp_sp_h18b, disp_ldp_sp_h19, disp_ldp_sp_h19b, disp_ldp_sp_h20, disp_ldp_sp_h20b, disp_ldp_sp_h21, disp_ldp_sp_h21b, disp_ldp_sp_h22, disp_ldp_sp_h22b, disp_ldp_sp_h23, disp_ldp_sp_h23b, disp_ldp_sp_h24, disp_ldp_sp_h24b, disp_ldp_sp_h25, disp_ldp_sp_h25b, disp_ldp_sp_h26, disp_ldp_sp_h26b, disp_ldp_sp_h27, disp_ldp_sp_h27b, disp_ldp_sp_h28, disp_ldp_sp_h28b, disp_ldp_sp_h29, disp_ldp_sp_h29b, disp_ldp_sp_h30, disp_ldp_sp_h30b, disp_ldp_sp_h31, disp_ldp_sp_h31b, disp_ldp_sp_h32, disp_ldp_sp_h32b, disp_ldp_sp_h33, disp_ldp_sp_h33b, disp_ldp_sp_h34, disp_ldp_sp_h34b, disp_ldp_sp_h35, disp_ldp_sp_h35b, disp_ldp_sp_h36, disp_ldp_sp_h36b, disp_ldp_sp_h37, disp_ldp_sp_h37b, disp_ldp_sp_h38, disp_ldp_sp_h38b, disp_ldp_sp_h39, disp_ldp_sp_h39b, disp_ldp_sp_h40, disp_ldp_sp_h40b, disp_ldp_sp_h41, disp_ldp_sp_h41b, disp_ldp_sp_h42, disp_ldp_sp_h42b, disp_ldp_sp_h43, disp_ldp_sp_h43b, disp_ldp_sp_h44, disp_ldp_sp_h44b, disp_ldp_sp_h45, disp_ldp_sp_h45b, disp_ldp_sp_h46, disp_ldp_sp_h46b, disp_ldp_sp_h47, disp_ldp_sp_h47b, disp_ldp_sp_h48, disp_ldp_sp_h48b, disp_ldp_sp_h49, disp_ldp_sp_h49b, disp_ldp_sp_h50, disp_ldp_sp_h50b, disp_ldp_sp_h51, disp_ldp_sp_h51b, disp_ldp_sp_h52, disp_ldp_sp_h52b, disp_ldp_sp_h53, disp_ldp_sp_h53b, disp_ldp_sp_h54, disp_ldp_sp_h54b, disp_ldp_sp_h55, disp_ldp_sp_h55b, disp_ldp_sp_h56, disp_ldp_sp_h56b, disp_ldp_sp_h57, disp_ldp_sp_h57b, disp_ldp_sp_h58, disp_ldp_sp_h59, disp_ldp_sp_h60, disp_ldp_sp_h61, disp_ldp_sp_h62, disp_ldp_sp_h63, disp_ldp_sp_h64, disp_ldp_sp_h65, disp_ldp_sp_h66, disp_ldp_sp_h67, disp_ldp_sp_h68, disp_ldp_sp_h69, disp_ldp_sp_h70, disp_ldp_sp_h71, disp_ldp_sp_h72, disp_ldp_sp_h73, disp_ldp_sp_h74, disp_ldp_sp_h75, disp_ldp_sp_h76, disp_ldp_sp_h77, disp_ldp_sp_h78, disp_ldp_sp_h79, disp_ldp_sp_h80, disp_ldp_sp_h81, disp_ldp_sp_h82, disp_ldp_sp_h83, disp_ldp_sp_h84, disp_ldp_sp_h85, disp_ldp_sp_h85b, disp_ldp_sp_h86, disp_ldp_sp_h86b, disp_ldp_sp_h87, disp_ldp_sp_h87b, disp_ldp_sp_h88, disp_ldp_sp_h88b, disp_ldp_sp_h89, disp_ldp_sp_h89b, disp_ldp_sp_h90, disp_ldp_sp_h90b, disp_ldp_sp_h91, disp_ldp_sp_h91b, disp_ldp_sp_h92, disp_ldp_sp_h92b, disp_ldp_sp_h93, disp_ldp_sp_h93b, disp_ldp_sp_h94, disp_ldp_sp_h94b, disp_ldp_sp_h95, disp_ldp_sp_h95b, disp_ldp_sp_h96, disp_ldp_sp_h96b, disp_ldp_sp_h97, disp_ldp_sp_h97b, disp_ldp_sp_h98, disp_ldp_sp_h98b, disp_ldp_sp_h99, disp_ldp_sp_h99b, disp_ldp_sp_h100, disp_ldp_sp_h100b, disp_ldp_sp_h101, disp_ldp_sp_h101b, disp_ldp_sp_h102, disp_ldp_sp_h102b, disp_ldp_sp_h103, disp_ldp_sp_h103b, disp_ldp_sp_h104, disp_ldp_sp_h104b, disp_ldp_sp_h105, disp_ldp_sp_h105b, disp_ldp_sp_h106, disp_ldp_sp_h106b, disp_ldp_sp_h107, disp_ldp_sp_h107b, disp_ldp_sp_h108, disp_ldp_sp_h108b, disp_ldp_sp_h109, disp_ldp_sp_h109b, disp_ldp_sp_h110, disp_ldp_sp_h110b, disp_ldp_sp_h111, disp_ldp_sp_h111b, disp_ldp_sp_h112, disp_ldp_sp_h112b, disp_ldp_sp_h113, disp_ldp_sp_h113b, disp_ldp_sp_h114, disp_ldp_sp_h114b, disp_ldp_sp_h115, disp_ldp_sp_h115b, disp_ldp_sp_h116, disp_ldp_sp_h116b, disp_ldp_sp_h117, disp_ldp_sp_h117b, disp_ldp_sp_h118, disp_ldp_sp_h118b, disp_ldp_sp_h119, disp_ldp_sp_h119b, disp_ldp_sp_h120, disp_ldp_sp_h120b, disp_ldp_sp_h121, disp_ldp_sp_h121b, disp_ldp_sp_h122, disp_ldp_sp_h122b, disp_ldp_sp_h123, disp_ldp_sp_h123b, disp_ldp_sp_h124, disp_ldp_sp_h124b, disp_ldp_sp_h125, disp_ldp_sp_h125b, disp_ldp_sp_h126, disp_ldp_sp_h126b, disp_ldp_sp_h127, disp_ldp_sp_h127b, disp_ldp_sp_h128, disp_ldp_sp_h128b, disp_ldp_sp_h129, disp_ldp_sp_h129b, disp_ldp_sp_h130, disp_ldp_sp_h131, disp_ldp_sp_h132, disp_ldp_sp_h133, disp_ldp_sp_h134, disp_ldp_sp_h135, disp_ldp_sp_h136, disp_ldp_sp_h137, disp_ldp_sp_h138, disp_ldp_sp_h139, disp_ldp_sp_h140, disp_ldp_sp_h141, disp_ldp_sp_h142, disp_ldp_sp_h143, disp_ldp_sp_h144, disp_ldp_sp_h145, disp_ldp_sp_h146, disp_ldp_sp_h147, disp_ldp_sp_h148, disp_ldp_sp_h149, disp_ldp_sp_h150, disp_ldp_sp_h151, disp_ldp_sp_h152, disp_ldp_sp_h153, disp_ldp_sp_h154, disp_ldp_sp_h155, disp_ldp_sp_h156, disp_ldp_sp_h157, disp_ldp_sp_h158, disp_ldp_sp_h159, disp_ldp_sp_h160, disp_ldp_sp_h161, disp_ldp_sp_h162, disp_ldp_sp_h163, disp_ldp_sp_h164, disp_ldp_sp_h165, disp_ldp_sp_h166, disp_ldp_sp_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg3
  try simp (config := {decide := true}) only [disp_ldp_sp_h0, disp_ldp_sp_h0b, disp_ldp_sp_h1, disp_ldp_sp_h1b, disp_ldp_sp_h2, disp_ldp_sp_h3, disp_ldp_sp_h4, disp_ldp_sp_h5, disp_ldp_sp_h6, disp_ldp_sp_h7, disp_ldp_sp_h8, disp_ldp_sp_h9, disp_ldp_sp_h10, disp_ldp_sp_h11, disp_ldp_sp_h12, disp_ldp_sp_h13, disp_ldp_sp_h13b, disp_ldp_sp_h14, disp_ldp_sp_h14b, disp_ldp_sp_h15, disp_ldp_sp_h15b, disp_ldp_sp_h16, disp_ldp_sp_h16b, disp_ldp_sp_h17, disp_ldp_sp_h17b, disp_ldp_sp_h18, disp_ldp_sp_h18b, disp_ldp_sp_h19, disp_ldp_sp_h19b, disp_ldp_sp_h20, disp_ldp_sp_h20b, disp_ldp_sp_h21, disp_ldp_sp_h21b, disp_ldp_sp_h22, disp_ldp_sp_h22b, disp_ldp_sp_h23, disp_ldp_sp_h23b, disp_ldp_sp_h24, disp_ldp_sp_h24b, disp_ldp_sp_h25, disp_ldp_sp_h25b, disp_ldp_sp_h26, disp_ldp_sp_h26b, disp_ldp_sp_h27, disp_ldp_sp_h27b, disp_ldp_sp_h28, disp_ldp_sp_h28b, disp_ldp_sp_h29, disp_ldp_sp_h29b, disp_ldp_sp_h30, disp_ldp_sp_h30b, disp_ldp_sp_h31, disp_ldp_sp_h31b, disp_ldp_sp_h32, disp_ldp_sp_h32b, disp_ldp_sp_h33, disp_ldp_sp_h33b, disp_ldp_sp_h34, disp_ldp_sp_h34b, disp_ldp_sp_h35, disp_ldp_sp_h35b, disp_ldp_sp_h36, disp_ldp_sp_h36b, disp_ldp_sp_h37, disp_ldp_sp_h37b, disp_ldp_sp_h38, disp_ldp_sp_h38b, disp_ldp_sp_h39, disp_ldp_sp_h39b, disp_ldp_sp_h40, disp_ldp_sp_h40b, disp_ldp_sp_h41, disp_ldp_sp_h41b, disp_ldp_sp_h42, disp_ldp_sp_h42b, disp_ldp_sp_h43, disp_ldp_sp_h43b, disp_ldp_sp_h44, disp_ldp_sp_h44b, disp_ldp_sp_h45, disp_ldp_sp_h45b, disp_ldp_sp_h46, disp_ldp_sp_h46b, disp_ldp_sp_h47, disp_ldp_sp_h47b, disp_ldp_sp_h48, disp_ldp_sp_h48b, disp_ldp_sp_h49, disp_ldp_sp_h49b, disp_ldp_sp_h50, disp_ldp_sp_h50b, disp_ldp_sp_h51, disp_ldp_sp_h51b, disp_ldp_sp_h52, disp_ldp_sp_h52b, disp_ldp_sp_h53, disp_ldp_sp_h53b, disp_ldp_sp_h54, disp_ldp_sp_h54b, disp_ldp_sp_h55, disp_ldp_sp_h55b, disp_ldp_sp_h56, disp_ldp_sp_h56b, disp_ldp_sp_h57, disp_ldp_sp_h57b, disp_ldp_sp_h58, disp_ldp_sp_h59, disp_ldp_sp_h60, disp_ldp_sp_h61, disp_ldp_sp_h62, disp_ldp_sp_h63, disp_ldp_sp_h64, disp_ldp_sp_h65, disp_ldp_sp_h66, disp_ldp_sp_h67, disp_ldp_sp_h68, disp_ldp_sp_h69, disp_ldp_sp_h70, disp_ldp_sp_h71, disp_ldp_sp_h72, disp_ldp_sp_h73, disp_ldp_sp_h74, disp_ldp_sp_h75, disp_ldp_sp_h76, disp_ldp_sp_h77, disp_ldp_sp_h78, disp_ldp_sp_h79, disp_ldp_sp_h80, disp_ldp_sp_h81, disp_ldp_sp_h82, disp_ldp_sp_h83, disp_ldp_sp_h84, disp_ldp_sp_h85, disp_ldp_sp_h85b, disp_ldp_sp_h86, disp_ldp_sp_h86b, disp_ldp_sp_h87, disp_ldp_sp_h87b, disp_ldp_sp_h88, disp_ldp_sp_h88b, disp_ldp_sp_h89, disp_ldp_sp_h89b, disp_ldp_sp_h90, disp_ldp_sp_h90b, disp_ldp_sp_h91, disp_ldp_sp_h91b, disp_ldp_sp_h92, disp_ldp_sp_h92b, disp_ldp_sp_h93, disp_ldp_sp_h93b, disp_ldp_sp_h94, disp_ldp_sp_h94b, disp_ldp_sp_h95, disp_ldp_sp_h95b, disp_ldp_sp_h96, disp_ldp_sp_h96b, disp_ldp_sp_h97, disp_ldp_sp_h97b, disp_ldp_sp_h98, disp_ldp_sp_h98b, disp_ldp_sp_h99, disp_ldp_sp_h99b, disp_ldp_sp_h100, disp_ldp_sp_h100b, disp_ldp_sp_h101, disp_ldp_sp_h101b, disp_ldp_sp_h102, disp_ldp_sp_h102b, disp_ldp_sp_h103, disp_ldp_sp_h103b, disp_ldp_sp_h104, disp_ldp_sp_h104b, disp_ldp_sp_h105, disp_ldp_sp_h105b, disp_ldp_sp_h106, disp_ldp_sp_h106b, disp_ldp_sp_h107, disp_ldp_sp_h107b, disp_ldp_sp_h108, disp_ldp_sp_h108b, disp_ldp_sp_h109, disp_ldp_sp_h109b, disp_ldp_sp_h110, disp_ldp_sp_h110b, disp_ldp_sp_h111, disp_ldp_sp_h111b, disp_ldp_sp_h112, disp_ldp_sp_h112b, disp_ldp_sp_h113, disp_ldp_sp_h113b, disp_ldp_sp_h114, disp_ldp_sp_h114b, disp_ldp_sp_h115, disp_ldp_sp_h115b, disp_ldp_sp_h116, disp_ldp_sp_h116b, disp_ldp_sp_h117, disp_ldp_sp_h117b, disp_ldp_sp_h118, disp_ldp_sp_h118b, disp_ldp_sp_h119, disp_ldp_sp_h119b, disp_ldp_sp_h120, disp_ldp_sp_h120b, disp_ldp_sp_h121, disp_ldp_sp_h121b, disp_ldp_sp_h122, disp_ldp_sp_h122b, disp_ldp_sp_h123, disp_ldp_sp_h123b, disp_ldp_sp_h124, disp_ldp_sp_h124b, disp_ldp_sp_h125, disp_ldp_sp_h125b, disp_ldp_sp_h126, disp_ldp_sp_h126b, disp_ldp_sp_h127, disp_ldp_sp_h127b, disp_ldp_sp_h128, disp_ldp_sp_h128b, disp_ldp_sp_h129, disp_ldp_sp_h129b, disp_ldp_sp_h130, disp_ldp_sp_h131, disp_ldp_sp_h132, disp_ldp_sp_h133, disp_ldp_sp_h134, disp_ldp_sp_h135, disp_ldp_sp_h136, disp_ldp_sp_h137, disp_ldp_sp_h138, disp_ldp_sp_h139, disp_ldp_sp_h140, disp_ldp_sp_h141, disp_ldp_sp_h142, disp_ldp_sp_h143, disp_ldp_sp_h144, disp_ldp_sp_h145, disp_ldp_sp_h146, disp_ldp_sp_h147, disp_ldp_sp_h148, disp_ldp_sp_h149, disp_ldp_sp_h150, disp_ldp_sp_h151, disp_ldp_sp_h152, disp_ldp_sp_h153, disp_ldp_sp_h154, disp_ldp_sp_h155, disp_ldp_sp_h156, disp_ldp_sp_h157, disp_ldp_sp_h158, disp_ldp_sp_h159, disp_ldp_sp_h160, disp_ldp_sp_h161, disp_ldp_sp_h162, disp_ldp_sp_h163, disp_ldp_sp_h164, disp_ldp_sp_h165, disp_ldp_sp_h166, disp_ldp_sp_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg4
  try simp (config := {decide := true}) only [disp_ldp_sp_h0, disp_ldp_sp_h0b, disp_ldp_sp_h1, disp_ldp_sp_h1b, disp_ldp_sp_h2, disp_ldp_sp_h3, disp_ldp_sp_h4, disp_ldp_sp_h5, disp_ldp_sp_h6, disp_ldp_sp_h7, disp_ldp_sp_h8, disp_ldp_sp_h9, disp_ldp_sp_h10, disp_ldp_sp_h11, disp_ldp_sp_h12, disp_ldp_sp_h13, disp_ldp_sp_h13b, disp_ldp_sp_h14, disp_ldp_sp_h14b, disp_ldp_sp_h15, disp_ldp_sp_h15b, disp_ldp_sp_h16, disp_ldp_sp_h16b, disp_ldp_sp_h17, disp_ldp_sp_h17b, disp_ldp_sp_h18, disp_ldp_sp_h18b, disp_ldp_sp_h19, disp_ldp_sp_h19b, disp_ldp_sp_h20, disp_ldp_sp_h20b, disp_ldp_sp_h21, disp_ldp_sp_h21b, disp_ldp_sp_h22, disp_ldp_sp_h22b, disp_ldp_sp_h23, disp_ldp_sp_h23b, disp_ldp_sp_h24, disp_ldp_sp_h24b, disp_ldp_sp_h25, disp_ldp_sp_h25b, disp_ldp_sp_h26, disp_ldp_sp_h26b, disp_ldp_sp_h27, disp_ldp_sp_h27b, disp_ldp_sp_h28, disp_ldp_sp_h28b, disp_ldp_sp_h29, disp_ldp_sp_h29b, disp_ldp_sp_h30, disp_ldp_sp_h30b, disp_ldp_sp_h31, disp_ldp_sp_h31b, disp_ldp_sp_h32, disp_ldp_sp_h32b, disp_ldp_sp_h33, disp_ldp_sp_h33b, disp_ldp_sp_h34, disp_ldp_sp_h34b, disp_ldp_sp_h35, disp_ldp_sp_h35b, disp_ldp_sp_h36, disp_ldp_sp_h36b, disp_ldp_sp_h37, disp_ldp_sp_h37b, disp_ldp_sp_h38, disp_ldp_sp_h38b, disp_ldp_sp_h39, disp_ldp_sp_h39b, disp_ldp_sp_h40, disp_ldp_sp_h40b, disp_ldp_sp_h41, disp_ldp_sp_h41b, disp_ldp_sp_h42, disp_ldp_sp_h42b, disp_ldp_sp_h43, disp_ldp_sp_h43b, disp_ldp_sp_h44, disp_ldp_sp_h44b, disp_ldp_sp_h45, disp_ldp_sp_h45b, disp_ldp_sp_h46, disp_ldp_sp_h46b, disp_ldp_sp_h47, disp_ldp_sp_h47b, disp_ldp_sp_h48, disp_ldp_sp_h48b, disp_ldp_sp_h49, disp_ldp_sp_h49b, disp_ldp_sp_h50, disp_ldp_sp_h50b, disp_ldp_sp_h51, disp_ldp_sp_h51b, disp_ldp_sp_h52, disp_ldp_sp_h52b, disp_ldp_sp_h53, disp_ldp_sp_h53b, disp_ldp_sp_h54, disp_ldp_sp_h54b, disp_ldp_sp_h55, disp_ldp_sp_h55b, disp_ldp_sp_h56, disp_ldp_sp_h56b, disp_ldp_sp_h57, disp_ldp_sp_h57b, disp_ldp_sp_h58, disp_ldp_sp_h59, disp_ldp_sp_h60, disp_ldp_sp_h61, disp_ldp_sp_h62, disp_ldp_sp_h63, disp_ldp_sp_h64, disp_ldp_sp_h65, disp_ldp_sp_h66, disp_ldp_sp_h67, disp_ldp_sp_h68, disp_ldp_sp_h69, disp_ldp_sp_h70, disp_ldp_sp_h71, disp_ldp_sp_h72, disp_ldp_sp_h73, disp_ldp_sp_h74, disp_ldp_sp_h75, disp_ldp_sp_h76, disp_ldp_sp_h77, disp_ldp_sp_h78, disp_ldp_sp_h79, disp_ldp_sp_h80, disp_ldp_sp_h81, disp_ldp_sp_h82, disp_ldp_sp_h83, disp_ldp_sp_h84, disp_ldp_sp_h85, disp_ldp_sp_h85b, disp_ldp_sp_h86, disp_ldp_sp_h86b, disp_ldp_sp_h87, disp_ldp_sp_h87b, disp_ldp_sp_h88, disp_ldp_sp_h88b, disp_ldp_sp_h89, disp_ldp_sp_h89b, disp_ldp_sp_h90, disp_ldp_sp_h90b, disp_ldp_sp_h91, disp_ldp_sp_h91b, disp_ldp_sp_h92, disp_ldp_sp_h92b, disp_ldp_sp_h93, disp_ldp_sp_h93b, disp_ldp_sp_h94, disp_ldp_sp_h94b, disp_ldp_sp_h95, disp_ldp_sp_h95b, disp_ldp_sp_h96, disp_ldp_sp_h96b, disp_ldp_sp_h97, disp_ldp_sp_h97b, disp_ldp_sp_h98, disp_ldp_sp_h98b, disp_ldp_sp_h99, disp_ldp_sp_h99b, disp_ldp_sp_h100, disp_ldp_sp_h100b, disp_ldp_sp_h101, disp_ldp_sp_h101b, disp_ldp_sp_h102, disp_ldp_sp_h102b, disp_ldp_sp_h103, disp_ldp_sp_h103b, disp_ldp_sp_h104, disp_ldp_sp_h104b, disp_ldp_sp_h105, disp_ldp_sp_h105b, disp_ldp_sp_h106, disp_ldp_sp_h106b, disp_ldp_sp_h107, disp_ldp_sp_h107b, disp_ldp_sp_h108, disp_ldp_sp_h108b, disp_ldp_sp_h109, disp_ldp_sp_h109b, disp_ldp_sp_h110, disp_ldp_sp_h110b, disp_ldp_sp_h111, disp_ldp_sp_h111b, disp_ldp_sp_h112, disp_ldp_sp_h112b, disp_ldp_sp_h113, disp_ldp_sp_h113b, disp_ldp_sp_h114, disp_ldp_sp_h114b, disp_ldp_sp_h115, disp_ldp_sp_h115b, disp_ldp_sp_h116, disp_ldp_sp_h116b, disp_ldp_sp_h117, disp_ldp_sp_h117b, disp_ldp_sp_h118, disp_ldp_sp_h118b, disp_ldp_sp_h119, disp_ldp_sp_h119b, disp_ldp_sp_h120, disp_ldp_sp_h120b, disp_ldp_sp_h121, disp_ldp_sp_h121b, disp_ldp_sp_h122, disp_ldp_sp_h122b, disp_ldp_sp_h123, disp_ldp_sp_h123b, disp_ldp_sp_h124, disp_ldp_sp_h124b, disp_ldp_sp_h125, disp_ldp_sp_h125b, disp_ldp_sp_h126, disp_ldp_sp_h126b, disp_ldp_sp_h127, disp_ldp_sp_h127b, disp_ldp_sp_h128, disp_ldp_sp_h128b, disp_ldp_sp_h129, disp_ldp_sp_h129b, disp_ldp_sp_h130, disp_ldp_sp_h131, disp_ldp_sp_h132, disp_ldp_sp_h133, disp_ldp_sp_h134, disp_ldp_sp_h135, disp_ldp_sp_h136, disp_ldp_sp_h137, disp_ldp_sp_h138, disp_ldp_sp_h139, disp_ldp_sp_h140, disp_ldp_sp_h141, disp_ldp_sp_h142, disp_ldp_sp_h143, disp_ldp_sp_h144, disp_ldp_sp_h145, disp_ldp_sp_h146, disp_ldp_sp_h147, disp_ldp_sp_h148, disp_ldp_sp_h149, disp_ldp_sp_h150, disp_ldp_sp_h151, disp_ldp_sp_h152, disp_ldp_sp_h153, disp_ldp_sp_h154, disp_ldp_sp_h155, disp_ldp_sp_h156, disp_ldp_sp_h157, disp_ldp_sp_h158, disp_ldp_sp_h159, disp_ldp_sp_h160, disp_ldp_sp_h161, disp_ldp_sp_h162, disp_ldp_sp_h163, disp_ldp_sp_h164, disp_ldp_sp_h165, disp_ldp_sp_h166, disp_ldp_sp_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg5
  try simp (config := {decide := true}) only [disp_ldp_sp_h0, disp_ldp_sp_h0b, disp_ldp_sp_h1, disp_ldp_sp_h1b, disp_ldp_sp_h2, disp_ldp_sp_h3, disp_ldp_sp_h4, disp_ldp_sp_h5, disp_ldp_sp_h6, disp_ldp_sp_h7, disp_ldp_sp_h8, disp_ldp_sp_h9, disp_ldp_sp_h10, disp_ldp_sp_h11, disp_ldp_sp_h12, disp_ldp_sp_h13, disp_ldp_sp_h13b, disp_ldp_sp_h14, disp_ldp_sp_h14b, disp_ldp_sp_h15, disp_ldp_sp_h15b, disp_ldp_sp_h16, disp_ldp_sp_h16b, disp_ldp_sp_h17, disp_ldp_sp_h17b, disp_ldp_sp_h18, disp_ldp_sp_h18b, disp_ldp_sp_h19, disp_ldp_sp_h19b, disp_ldp_sp_h20, disp_ldp_sp_h20b, disp_ldp_sp_h21, disp_ldp_sp_h21b, disp_ldp_sp_h22, disp_ldp_sp_h22b, disp_ldp_sp_h23, disp_ldp_sp_h23b, disp_ldp_sp_h24, disp_ldp_sp_h24b, disp_ldp_sp_h25, disp_ldp_sp_h25b, disp_ldp_sp_h26, disp_ldp_sp_h26b, disp_ldp_sp_h27, disp_ldp_sp_h27b, disp_ldp_sp_h28, disp_ldp_sp_h28b, disp_ldp_sp_h29, disp_ldp_sp_h29b, disp_ldp_sp_h30, disp_ldp_sp_h30b, disp_ldp_sp_h31, disp_ldp_sp_h31b, disp_ldp_sp_h32, disp_ldp_sp_h32b, disp_ldp_sp_h33, disp_ldp_sp_h33b, disp_ldp_sp_h34, disp_ldp_sp_h34b, disp_ldp_sp_h35, disp_ldp_sp_h35b, disp_ldp_sp_h36, disp_ldp_sp_h36b, disp_ldp_sp_h37, disp_ldp_sp_h37b, disp_ldp_sp_h38, disp_ldp_sp_h38b, disp_ldp_sp_h39, disp_ldp_sp_h39b, disp_ldp_sp_h40, disp_ldp_sp_h40b, disp_ldp_sp_h41, disp_ldp_sp_h41b, disp_ldp_sp_h42, disp_ldp_sp_h42b, disp_ldp_sp_h43, disp_ldp_sp_h43b, disp_ldp_sp_h44, disp_ldp_sp_h44b, disp_ldp_sp_h45, disp_ldp_sp_h45b, disp_ldp_sp_h46, disp_ldp_sp_h46b, disp_ldp_sp_h47, disp_ldp_sp_h47b, disp_ldp_sp_h48, disp_ldp_sp_h48b, disp_ldp_sp_h49, disp_ldp_sp_h49b, disp_ldp_sp_h50, disp_ldp_sp_h50b, disp_ldp_sp_h51, disp_ldp_sp_h51b, disp_ldp_sp_h52, disp_ldp_sp_h52b, disp_ldp_sp_h53, disp_ldp_sp_h53b, disp_ldp_sp_h54, disp_ldp_sp_h54b, disp_ldp_sp_h55, disp_ldp_sp_h55b, disp_ldp_sp_h56, disp_ldp_sp_h56b, disp_ldp_sp_h57, disp_ldp_sp_h57b, disp_ldp_sp_h58, disp_ldp_sp_h59, disp_ldp_sp_h60, disp_ldp_sp_h61, disp_ldp_sp_h62, disp_ldp_sp_h63, disp_ldp_sp_h64, disp_ldp_sp_h65, disp_ldp_sp_h66, disp_ldp_sp_h67, disp_ldp_sp_h68, disp_ldp_sp_h69, disp_ldp_sp_h70, disp_ldp_sp_h71, disp_ldp_sp_h72, disp_ldp_sp_h73, disp_ldp_sp_h74, disp_ldp_sp_h75, disp_ldp_sp_h76, disp_ldp_sp_h77, disp_ldp_sp_h78, disp_ldp_sp_h79, disp_ldp_sp_h80, disp_ldp_sp_h81, disp_ldp_sp_h82, disp_ldp_sp_h83, disp_ldp_sp_h84, disp_ldp_sp_h85, disp_ldp_sp_h85b, disp_ldp_sp_h86, disp_ldp_sp_h86b, disp_ldp_sp_h87, disp_ldp_sp_h87b, disp_ldp_sp_h88, disp_ldp_sp_h88b, disp_ldp_sp_h89, disp_ldp_sp_h89b, disp_ldp_sp_h90, disp_ldp_sp_h90b, disp_ldp_sp_h91, disp_ldp_sp_h91b, disp_ldp_sp_h92, disp_ldp_sp_h92b, disp_ldp_sp_h93, disp_ldp_sp_h93b, disp_ldp_sp_h94, disp_ldp_sp_h94b, disp_ldp_sp_h95, disp_ldp_sp_h95b, disp_ldp_sp_h96, disp_ldp_sp_h96b, disp_ldp_sp_h97, disp_ldp_sp_h97b, disp_ldp_sp_h98, disp_ldp_sp_h98b, disp_ldp_sp_h99, disp_ldp_sp_h99b, disp_ldp_sp_h100, disp_ldp_sp_h100b, disp_ldp_sp_h101, disp_ldp_sp_h101b, disp_ldp_sp_h102, disp_ldp_sp_h102b, disp_ldp_sp_h103, disp_ldp_sp_h103b, disp_ldp_sp_h104, disp_ldp_sp_h104b, disp_ldp_sp_h105, disp_ldp_sp_h105b, disp_ldp_sp_h106, disp_ldp_sp_h106b, disp_ldp_sp_h107, disp_ldp_sp_h107b, disp_ldp_sp_h108, disp_ldp_sp_h108b, disp_ldp_sp_h109, disp_ldp_sp_h109b, disp_ldp_sp_h110, disp_ldp_sp_h110b, disp_ldp_sp_h111, disp_ldp_sp_h111b, disp_ldp_sp_h112, disp_ldp_sp_h112b, disp_ldp_sp_h113, disp_ldp_sp_h113b, disp_ldp_sp_h114, disp_ldp_sp_h114b, disp_ldp_sp_h115, disp_ldp_sp_h115b, disp_ldp_sp_h116, disp_ldp_sp_h116b, disp_ldp_sp_h117, disp_ldp_sp_h117b, disp_ldp_sp_h118, disp_ldp_sp_h118b, disp_ldp_sp_h119, disp_ldp_sp_h119b, disp_ldp_sp_h120, disp_ldp_sp_h120b, disp_ldp_sp_h121, disp_ldp_sp_h121b, disp_ldp_sp_h122, disp_ldp_sp_h122b, disp_ldp_sp_h123, disp_ldp_sp_h123b, disp_ldp_sp_h124, disp_ldp_sp_h124b, disp_ldp_sp_h125, disp_ldp_sp_h125b, disp_ldp_sp_h126, disp_ldp_sp_h126b, disp_ldp_sp_h127, disp_ldp_sp_h127b, disp_ldp_sp_h128, disp_ldp_sp_h128b, disp_ldp_sp_h129, disp_ldp_sp_h129b, disp_ldp_sp_h130, disp_ldp_sp_h131, disp_ldp_sp_h132, disp_ldp_sp_h133, disp_ldp_sp_h134, disp_ldp_sp_h135, disp_ldp_sp_h136, disp_ldp_sp_h137, disp_ldp_sp_h138, disp_ldp_sp_h139, disp_ldp_sp_h140, disp_ldp_sp_h141, disp_ldp_sp_h142, disp_ldp_sp_h143, disp_ldp_sp_h144, disp_ldp_sp_h145, disp_ldp_sp_h146, disp_ldp_sp_h147, disp_ldp_sp_h148, disp_ldp_sp_h149, disp_ldp_sp_h150, disp_ldp_sp_h151, disp_ldp_sp_h152, disp_ldp_sp_h153, disp_ldp_sp_h154, disp_ldp_sp_h155, disp_ldp_sp_h156, disp_ldp_sp_h157, disp_ldp_sp_h158, disp_ldp_sp_h159, disp_ldp_sp_h160, disp_ldp_sp_h161, disp_ldp_sp_h162, disp_ldp_sp_h163, disp_ldp_sp_h164, disp_ldp_sp_h165, disp_ldp_sp_h166, disp_ldp_sp_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg6
  try simp (config := {decide := true}) only [disp_ldp_sp_h0, disp_ldp_sp_h0b, disp_ldp_sp_h1, disp_ldp_sp_h1b, disp_ldp_sp_h2, disp_ldp_sp_h3, disp_ldp_sp_h4, disp_ldp_sp_h5, disp_ldp_sp_h6, disp_ldp_sp_h7, disp_ldp_sp_h8, disp_ldp_sp_h9, disp_ldp_sp_h10, disp_ldp_sp_h11, disp_ldp_sp_h12, disp_ldp_sp_h13, disp_ldp_sp_h13b, disp_ldp_sp_h14, disp_ldp_sp_h14b, disp_ldp_sp_h15, disp_ldp_sp_h15b, disp_ldp_sp_h16, disp_ldp_sp_h16b, disp_ldp_sp_h17, disp_ldp_sp_h17b, disp_ldp_sp_h18, disp_ldp_sp_h18b, disp_ldp_sp_h19, disp_ldp_sp_h19b, disp_ldp_sp_h20, disp_ldp_sp_h20b, disp_ldp_sp_h21, disp_ldp_sp_h21b, disp_ldp_sp_h22, disp_ldp_sp_h22b, disp_ldp_sp_h23, disp_ldp_sp_h23b, disp_ldp_sp_h24, disp_ldp_sp_h24b, disp_ldp_sp_h25, disp_ldp_sp_h25b, disp_ldp_sp_h26, disp_ldp_sp_h26b, disp_ldp_sp_h27, disp_ldp_sp_h27b, disp_ldp_sp_h28, disp_ldp_sp_h28b, disp_ldp_sp_h29, disp_ldp_sp_h29b, disp_ldp_sp_h30, disp_ldp_sp_h30b, disp_ldp_sp_h31, disp_ldp_sp_h31b, disp_ldp_sp_h32, disp_ldp_sp_h32b, disp_ldp_sp_h33, disp_ldp_sp_h33b, disp_ldp_sp_h34, disp_ldp_sp_h34b, disp_ldp_sp_h35, disp_ldp_sp_h35b, disp_ldp_sp_h36, disp_ldp_sp_h36b, disp_ldp_sp_h37, disp_ldp_sp_h37b, disp_ldp_sp_h38, disp_ldp_sp_h38b, disp_ldp_sp_h39, disp_ldp_sp_h39b, disp_ldp_sp_h40, disp_ldp_sp_h40b, disp_ldp_sp_h41, disp_ldp_sp_h41b, disp_ldp_sp_h42, disp_ldp_sp_h42b, disp_ldp_sp_h43, disp_ldp_sp_h43b, disp_ldp_sp_h44, disp_ldp_sp_h44b, disp_ldp_sp_h45, disp_ldp_sp_h45b, disp_ldp_sp_h46, disp_ldp_sp_h46b, disp_ldp_sp_h47, disp_ldp_sp_h47b, disp_ldp_sp_h48, disp_ldp_sp_h48b, disp_ldp_sp_h49, disp_ldp_sp_h49b, disp_ldp_sp_h50, disp_ldp_sp_h50b, disp_ldp_sp_h51, disp_ldp_sp_h51b, disp_ldp_sp_h52, disp_ldp_sp_h52b, disp_ldp_sp_h53, disp_ldp_sp_h53b, disp_ldp_sp_h54, disp_ldp_sp_h54b, disp_ldp_sp_h55, disp_ldp_sp_h55b, disp_ldp_sp_h56, disp_ldp_sp_h56b, disp_ldp_sp_h57, disp_ldp_sp_h57b, disp_ldp_sp_h58, disp_ldp_sp_h59, disp_ldp_sp_h60, disp_ldp_sp_h61, disp_ldp_sp_h62, disp_ldp_sp_h63, disp_ldp_sp_h64, disp_ldp_sp_h65, disp_ldp_sp_h66, disp_ldp_sp_h67, disp_ldp_sp_h68, disp_ldp_sp_h69, disp_ldp_sp_h70, disp_ldp_sp_h71, disp_ldp_sp_h72, disp_ldp_sp_h73, disp_ldp_sp_h74, disp_ldp_sp_h75, disp_ldp_sp_h76, disp_ldp_sp_h77, disp_ldp_sp_h78, disp_ldp_sp_h79, disp_ldp_sp_h80, disp_ldp_sp_h81, disp_ldp_sp_h82, disp_ldp_sp_h83, disp_ldp_sp_h84, disp_ldp_sp_h85, disp_ldp_sp_h85b, disp_ldp_sp_h86, disp_ldp_sp_h86b, disp_ldp_sp_h87, disp_ldp_sp_h87b, disp_ldp_sp_h88, disp_ldp_sp_h88b, disp_ldp_sp_h89, disp_ldp_sp_h89b, disp_ldp_sp_h90, disp_ldp_sp_h90b, disp_ldp_sp_h91, disp_ldp_sp_h91b, disp_ldp_sp_h92, disp_ldp_sp_h92b, disp_ldp_sp_h93, disp_ldp_sp_h93b, disp_ldp_sp_h94, disp_ldp_sp_h94b, disp_ldp_sp_h95, disp_ldp_sp_h95b, disp_ldp_sp_h96, disp_ldp_sp_h96b, disp_ldp_sp_h97, disp_ldp_sp_h97b, disp_ldp_sp_h98, disp_ldp_sp_h98b, disp_ldp_sp_h99, disp_ldp_sp_h99b, disp_ldp_sp_h100, disp_ldp_sp_h100b, disp_ldp_sp_h101, disp_ldp_sp_h101b, disp_ldp_sp_h102, disp_ldp_sp_h102b, disp_ldp_sp_h103, disp_ldp_sp_h103b, disp_ldp_sp_h104, disp_ldp_sp_h104b, disp_ldp_sp_h105, disp_ldp_sp_h105b, disp_ldp_sp_h106, disp_ldp_sp_h106b, disp_ldp_sp_h107, disp_ldp_sp_h107b, disp_ldp_sp_h108, disp_ldp_sp_h108b, disp_ldp_sp_h109, disp_ldp_sp_h109b, disp_ldp_sp_h110, disp_ldp_sp_h110b, disp_ldp_sp_h111, disp_ldp_sp_h111b, disp_ldp_sp_h112, disp_ldp_sp_h112b, disp_ldp_sp_h113, disp_ldp_sp_h113b, disp_ldp_sp_h114, disp_ldp_sp_h114b, disp_ldp_sp_h115, disp_ldp_sp_h115b, disp_ldp_sp_h116, disp_ldp_sp_h116b, disp_ldp_sp_h117, disp_ldp_sp_h117b, disp_ldp_sp_h118, disp_ldp_sp_h118b, disp_ldp_sp_h119, disp_ldp_sp_h119b, disp_ldp_sp_h120, disp_ldp_sp_h120b, disp_ldp_sp_h121, disp_ldp_sp_h121b, disp_ldp_sp_h122, disp_ldp_sp_h122b, disp_ldp_sp_h123, disp_ldp_sp_h123b, disp_ldp_sp_h124, disp_ldp_sp_h124b, disp_ldp_sp_h125, disp_ldp_sp_h125b, disp_ldp_sp_h126, disp_ldp_sp_h126b, disp_ldp_sp_h127, disp_ldp_sp_h127b, disp_ldp_sp_h128, disp_ldp_sp_h128b, disp_ldp_sp_h129, disp_ldp_sp_h129b, disp_ldp_sp_h130, disp_ldp_sp_h131, disp_ldp_sp_h132, disp_ldp_sp_h133, disp_ldp_sp_h134, disp_ldp_sp_h135, disp_ldp_sp_h136, disp_ldp_sp_h137, disp_ldp_sp_h138, disp_ldp_sp_h139, disp_ldp_sp_h140, disp_ldp_sp_h141, disp_ldp_sp_h142, disp_ldp_sp_h143, disp_ldp_sp_h144, disp_ldp_sp_h145, disp_ldp_sp_h146, disp_ldp_sp_h147, disp_ldp_sp_h148, disp_ldp_sp_h149, disp_ldp_sp_h150, disp_ldp_sp_h151, disp_ldp_sp_h152, disp_ldp_sp_h153, disp_ldp_sp_h154, disp_ldp_sp_h155, disp_ldp_sp_h156, disp_ldp_sp_h157, disp_ldp_sp_h158, disp_ldp_sp_h159, disp_ldp_sp_h160, disp_ldp_sp_h161, disp_ldp_sp_h162, disp_ldp_sp_h163, disp_ldp_sp_h164, disp_ldp_sp_h165, disp_ldp_sp_h166, disp_ldp_sp_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg7
  try simp (config := {decide := true}) only [disp_ldp_sp_h0, disp_ldp_sp_h0b, disp_ldp_sp_h1, disp_ldp_sp_h1b, disp_ldp_sp_h2, disp_ldp_sp_h3, disp_ldp_sp_h4, disp_ldp_sp_h5, disp_ldp_sp_h6, disp_ldp_sp_h7, disp_ldp_sp_h8, disp_ldp_sp_h9, disp_ldp_sp_h10, disp_ldp_sp_h11, disp_ldp_sp_h12, disp_ldp_sp_h13, disp_ldp_sp_h13b, disp_ldp_sp_h14, disp_ldp_sp_h14b, disp_ldp_sp_h15, disp_ldp_sp_h15b, disp_ldp_sp_h16, disp_ldp_sp_h16b, disp_ldp_sp_h17, disp_ldp_sp_h17b, disp_ldp_sp_h18, disp_ldp_sp_h18b, disp_ldp_sp_h19, disp_ldp_sp_h19b, disp_ldp_sp_h20, disp_ldp_sp_h20b, disp_ldp_sp_h21, disp_ldp_sp_h21b, disp_ldp_sp_h22, disp_ldp_sp_h22b, disp_ldp_sp_h23, disp_ldp_sp_h23b, disp_ldp_sp_h24, disp_ldp_sp_h24b, disp_ldp_sp_h25, disp_ldp_sp_h25b, disp_ldp_sp_h26, disp_ldp_sp_h26b, disp_ldp_sp_h27, disp_ldp_sp_h27b, disp_ldp_sp_h28, disp_ldp_sp_h28b, disp_ldp_sp_h29, disp_ldp_sp_h29b, disp_ldp_sp_h30, disp_ldp_sp_h30b, disp_ldp_sp_h31, disp_ldp_sp_h31b, disp_ldp_sp_h32, disp_ldp_sp_h32b, disp_ldp_sp_h33, disp_ldp_sp_h33b, disp_ldp_sp_h34, disp_ldp_sp_h34b, disp_ldp_sp_h35, disp_ldp_sp_h35b, disp_ldp_sp_h36, disp_ldp_sp_h36b, disp_ldp_sp_h37, disp_ldp_sp_h37b, disp_ldp_sp_h38, disp_ldp_sp_h38b, disp_ldp_sp_h39, disp_ldp_sp_h39b, disp_ldp_sp_h40, disp_ldp_sp_h40b, disp_ldp_sp_h41, disp_ldp_sp_h41b, disp_ldp_sp_h42, disp_ldp_sp_h42b, disp_ldp_sp_h43, disp_ldp_sp_h43b, disp_ldp_sp_h44, disp_ldp_sp_h44b, disp_ldp_sp_h45, disp_ldp_sp_h45b, disp_ldp_sp_h46, disp_ldp_sp_h46b, disp_ldp_sp_h47, disp_ldp_sp_h47b, disp_ldp_sp_h48, disp_ldp_sp_h48b, disp_ldp_sp_h49, disp_ldp_sp_h49b, disp_ldp_sp_h50, disp_ldp_sp_h50b, disp_ldp_sp_h51, disp_ldp_sp_h51b, disp_ldp_sp_h52, disp_ldp_sp_h52b, disp_ldp_sp_h53, disp_ldp_sp_h53b, disp_ldp_sp_h54, disp_ldp_sp_h54b, disp_ldp_sp_h55, disp_ldp_sp_h55b, disp_ldp_sp_h56, disp_ldp_sp_h56b, disp_ldp_sp_h57, disp_ldp_sp_h57b, disp_ldp_sp_h58, disp_ldp_sp_h59, disp_ldp_sp_h60, disp_ldp_sp_h61, disp_ldp_sp_h62, disp_ldp_sp_h63, disp_ldp_sp_h64, disp_ldp_sp_h65, disp_ldp_sp_h66, disp_ldp_sp_h67, disp_ldp_sp_h68, disp_ldp_sp_h69, disp_ldp_sp_h70, disp_ldp_sp_h71, disp_ldp_sp_h72, disp_ldp_sp_h73, disp_ldp_sp_h74, disp_ldp_sp_h75, disp_ldp_sp_h76, disp_ldp_sp_h77, disp_ldp_sp_h78, disp_ldp_sp_h79, disp_ldp_sp_h80, disp_ldp_sp_h81, disp_ldp_sp_h82, disp_ldp_sp_h83, disp_ldp_sp_h84, disp_ldp_sp_h85, disp_ldp_sp_h85b, disp_ldp_sp_h86, disp_ldp_sp_h86b, disp_ldp_sp_h87, disp_ldp_sp_h87b, disp_ldp_sp_h88, disp_ldp_sp_h88b, disp_ldp_sp_h89, disp_ldp_sp_h89b, disp_ldp_sp_h90, disp_ldp_sp_h90b, disp_ldp_sp_h91, disp_ldp_sp_h91b, disp_ldp_sp_h92, disp_ldp_sp_h92b, disp_ldp_sp_h93, disp_ldp_sp_h93b, disp_ldp_sp_h94, disp_ldp_sp_h94b, disp_ldp_sp_h95, disp_ldp_sp_h95b, disp_ldp_sp_h96, disp_ldp_sp_h96b, disp_ldp_sp_h97, disp_ldp_sp_h97b, disp_ldp_sp_h98, disp_ldp_sp_h98b, disp_ldp_sp_h99, disp_ldp_sp_h99b, disp_ldp_sp_h100, disp_ldp_sp_h100b, disp_ldp_sp_h101, disp_ldp_sp_h101b, disp_ldp_sp_h102, disp_ldp_sp_h102b, disp_ldp_sp_h103, disp_ldp_sp_h103b, disp_ldp_sp_h104, disp_ldp_sp_h104b, disp_ldp_sp_h105, disp_ldp_sp_h105b, disp_ldp_sp_h106, disp_ldp_sp_h106b, disp_ldp_sp_h107, disp_ldp_sp_h107b, disp_ldp_sp_h108, disp_ldp_sp_h108b, disp_ldp_sp_h109, disp_ldp_sp_h109b, disp_ldp_sp_h110, disp_ldp_sp_h110b, disp_ldp_sp_h111, disp_ldp_sp_h111b, disp_ldp_sp_h112, disp_ldp_sp_h112b, disp_ldp_sp_h113, disp_ldp_sp_h113b, disp_ldp_sp_h114, disp_ldp_sp_h114b, disp_ldp_sp_h115, disp_ldp_sp_h115b, disp_ldp_sp_h116, disp_ldp_sp_h116b, disp_ldp_sp_h117, disp_ldp_sp_h117b, disp_ldp_sp_h118, disp_ldp_sp_h118b, disp_ldp_sp_h119, disp_ldp_sp_h119b, disp_ldp_sp_h120, disp_ldp_sp_h120b, disp_ldp_sp_h121, disp_ldp_sp_h121b, disp_ldp_sp_h122, disp_ldp_sp_h122b, disp_ldp_sp_h123, disp_ldp_sp_h123b, disp_ldp_sp_h124, disp_ldp_sp_h124b, disp_ldp_sp_h125, disp_ldp_sp_h125b, disp_ldp_sp_h126, disp_ldp_sp_h126b, disp_ldp_sp_h127, disp_ldp_sp_h127b, disp_ldp_sp_h128, disp_ldp_sp_h128b, disp_ldp_sp_h129, disp_ldp_sp_h129b, disp_ldp_sp_h130, disp_ldp_sp_h131, disp_ldp_sp_h132, disp_ldp_sp_h133, disp_ldp_sp_h134, disp_ldp_sp_h135, disp_ldp_sp_h136, disp_ldp_sp_h137, disp_ldp_sp_h138, disp_ldp_sp_h139, disp_ldp_sp_h140, disp_ldp_sp_h141, disp_ldp_sp_h142, disp_ldp_sp_h143, disp_ldp_sp_h144, disp_ldp_sp_h145, disp_ldp_sp_h146, disp_ldp_sp_h147, disp_ldp_sp_h148, disp_ldp_sp_h149, disp_ldp_sp_h150, disp_ldp_sp_h151, disp_ldp_sp_h152, disp_ldp_sp_h153, disp_ldp_sp_h154, disp_ldp_sp_h155, disp_ldp_sp_h156, disp_ldp_sp_h157, disp_ldp_sp_h158, disp_ldp_sp_h159, disp_ldp_sp_h160, disp_ldp_sp_h161, disp_ldp_sp_h162, disp_ldp_sp_h163, disp_ldp_sp_h164, disp_ldp_sp_h165, disp_ldp_sp_h166, disp_ldp_sp_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg8
  try simp (config := {decide := true}) only [disp_ldp_sp_h0, disp_ldp_sp_h0b, disp_ldp_sp_h1, disp_ldp_sp_h1b, disp_ldp_sp_h2, disp_ldp_sp_h3, disp_ldp_sp_h4, disp_ldp_sp_h5, disp_ldp_sp_h6, disp_ldp_sp_h7, disp_ldp_sp_h8, disp_ldp_sp_h9, disp_ldp_sp_h10, disp_ldp_sp_h11, disp_ldp_sp_h12, disp_ldp_sp_h13, disp_ldp_sp_h13b, disp_ldp_sp_h14, disp_ldp_sp_h14b, disp_ldp_sp_h15, disp_ldp_sp_h15b, disp_ldp_sp_h16, disp_ldp_sp_h16b, disp_ldp_sp_h17, disp_ldp_sp_h17b, disp_ldp_sp_h18, disp_ldp_sp_h18b, disp_ldp_sp_h19, disp_ldp_sp_h19b, disp_ldp_sp_h20, disp_ldp_sp_h20b, disp_ldp_sp_h21, disp_ldp_sp_h21b, disp_ldp_sp_h22, disp_ldp_sp_h22b, disp_ldp_sp_h23, disp_ldp_sp_h23b, disp_ldp_sp_h24, disp_ldp_sp_h24b, disp_ldp_sp_h25, disp_ldp_sp_h25b, disp_ldp_sp_h26, disp_ldp_sp_h26b, disp_ldp_sp_h27, disp_ldp_sp_h27b, disp_ldp_sp_h28, disp_ldp_sp_h28b, disp_ldp_sp_h29, disp_ldp_sp_h29b, disp_ldp_sp_h30, disp_ldp_sp_h30b, disp_ldp_sp_h31, disp_ldp_sp_h31b, disp_ldp_sp_h32, disp_ldp_sp_h32b, disp_ldp_sp_h33, disp_ldp_sp_h33b, disp_ldp_sp_h34, disp_ldp_sp_h34b, disp_ldp_sp_h35, disp_ldp_sp_h35b, disp_ldp_sp_h36, disp_ldp_sp_h36b, disp_ldp_sp_h37, disp_ldp_sp_h37b, disp_ldp_sp_h38, disp_ldp_sp_h38b, disp_ldp_sp_h39, disp_ldp_sp_h39b, disp_ldp_sp_h40, disp_ldp_sp_h40b, disp_ldp_sp_h41, disp_ldp_sp_h41b, disp_ldp_sp_h42, disp_ldp_sp_h42b, disp_ldp_sp_h43, disp_ldp_sp_h43b, disp_ldp_sp_h44, disp_ldp_sp_h44b, disp_ldp_sp_h45, disp_ldp_sp_h45b, disp_ldp_sp_h46, disp_ldp_sp_h46b, disp_ldp_sp_h47, disp_ldp_sp_h47b, disp_ldp_sp_h48, disp_ldp_sp_h48b, disp_ldp_sp_h49, disp_ldp_sp_h49b, disp_ldp_sp_h50, disp_ldp_sp_h50b, disp_ldp_sp_h51, disp_ldp_sp_h51b, disp_ldp_sp_h52, disp_ldp_sp_h52b, disp_ldp_sp_h53, disp_ldp_sp_h53b, disp_ldp_sp_h54, disp_ldp_sp_h54b, disp_ldp_sp_h55, disp_ldp_sp_h55b, disp_ldp_sp_h56, disp_ldp_sp_h56b, disp_ldp_sp_h57, disp_ldp_sp_h57b, disp_ldp_sp_h58, disp_ldp_sp_h59, disp_ldp_sp_h60, disp_ldp_sp_h61, disp_ldp_sp_h62, disp_ldp_sp_h63, disp_ldp_sp_h64, disp_ldp_sp_h65, disp_ldp_sp_h66, disp_ldp_sp_h67, disp_ldp_sp_h68, disp_ldp_sp_h69, disp_ldp_sp_h70, disp_ldp_sp_h71, disp_ldp_sp_h72, disp_ldp_sp_h73, disp_ldp_sp_h74, disp_ldp_sp_h75, disp_ldp_sp_h76, disp_ldp_sp_h77, disp_ldp_sp_h78, disp_ldp_sp_h79, disp_ldp_sp_h80, disp_ldp_sp_h81, disp_ldp_sp_h82, disp_ldp_sp_h83, disp_ldp_sp_h84, disp_ldp_sp_h85, disp_ldp_sp_h85b, disp_ldp_sp_h86, disp_ldp_sp_h86b, disp_ldp_sp_h87, disp_ldp_sp_h87b, disp_ldp_sp_h88, disp_ldp_sp_h88b, disp_ldp_sp_h89, disp_ldp_sp_h89b, disp_ldp_sp_h90, disp_ldp_sp_h90b, disp_ldp_sp_h91, disp_ldp_sp_h91b, disp_ldp_sp_h92, disp_ldp_sp_h92b, disp_ldp_sp_h93, disp_ldp_sp_h93b, disp_ldp_sp_h94, disp_ldp_sp_h94b, disp_ldp_sp_h95, disp_ldp_sp_h95b, disp_ldp_sp_h96, disp_ldp_sp_h96b, disp_ldp_sp_h97, disp_ldp_sp_h97b, disp_ldp_sp_h98, disp_ldp_sp_h98b, disp_ldp_sp_h99, disp_ldp_sp_h99b, disp_ldp_sp_h100, disp_ldp_sp_h100b, disp_ldp_sp_h101, disp_ldp_sp_h101b, disp_ldp_sp_h102, disp_ldp_sp_h102b, disp_ldp_sp_h103, disp_ldp_sp_h103b, disp_ldp_sp_h104, disp_ldp_sp_h104b, disp_ldp_sp_h105, disp_ldp_sp_h105b, disp_ldp_sp_h106, disp_ldp_sp_h106b, disp_ldp_sp_h107, disp_ldp_sp_h107b, disp_ldp_sp_h108, disp_ldp_sp_h108b, disp_ldp_sp_h109, disp_ldp_sp_h109b, disp_ldp_sp_h110, disp_ldp_sp_h110b, disp_ldp_sp_h111, disp_ldp_sp_h111b, disp_ldp_sp_h112, disp_ldp_sp_h112b, disp_ldp_sp_h113, disp_ldp_sp_h113b, disp_ldp_sp_h114, disp_ldp_sp_h114b, disp_ldp_sp_h115, disp_ldp_sp_h115b, disp_ldp_sp_h116, disp_ldp_sp_h116b, disp_ldp_sp_h117, disp_ldp_sp_h117b, disp_ldp_sp_h118, disp_ldp_sp_h118b, disp_ldp_sp_h119, disp_ldp_sp_h119b, disp_ldp_sp_h120, disp_ldp_sp_h120b, disp_ldp_sp_h121, disp_ldp_sp_h121b, disp_ldp_sp_h122, disp_ldp_sp_h122b, disp_ldp_sp_h123, disp_ldp_sp_h123b, disp_ldp_sp_h124, disp_ldp_sp_h124b, disp_ldp_sp_h125, disp_ldp_sp_h125b, disp_ldp_sp_h126, disp_ldp_sp_h126b, disp_ldp_sp_h127, disp_ldp_sp_h127b, disp_ldp_sp_h128, disp_ldp_sp_h128b, disp_ldp_sp_h129, disp_ldp_sp_h129b, disp_ldp_sp_h130, disp_ldp_sp_h131, disp_ldp_sp_h132, disp_ldp_sp_h133, disp_ldp_sp_h134, disp_ldp_sp_h135, disp_ldp_sp_h136, disp_ldp_sp_h137, disp_ldp_sp_h138, disp_ldp_sp_h139, disp_ldp_sp_h140, disp_ldp_sp_h141, disp_ldp_sp_h142, disp_ldp_sp_h143, disp_ldp_sp_h144, disp_ldp_sp_h145, disp_ldp_sp_h146, disp_ldp_sp_h147, disp_ldp_sp_h148, disp_ldp_sp_h149, disp_ldp_sp_h150, disp_ldp_sp_h151, disp_ldp_sp_h152, disp_ldp_sp_h153, disp_ldp_sp_h154, disp_ldp_sp_h155, disp_ldp_sp_h156, disp_ldp_sp_h157, disp_ldp_sp_h158, disp_ldp_sp_h159, disp_ldp_sp_h160, disp_ldp_sp_h161, disp_ldp_sp_h162, disp_ldp_sp_h163, disp_ldp_sp_h164, disp_ldp_sp_h165, disp_ldp_sp_h166, disp_ldp_sp_h167, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

  -- crux workspace addition: the segmented LoadStore decoder leaves a Bool-continuation bind; fold it.
  congr 1
  funext x
  split
  · simp only [bind_assoc, pure_bind, Bool.false_eq_true, ite_false, bind_pure_unit]
  · simp only [pure_bind, ite_true]

#print axioms disp_ldp_sp
end ArmCertMem.Disp
