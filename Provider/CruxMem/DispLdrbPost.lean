import CryptoMem.LdstPostDecode
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

theorem disp_ldrb_post_h0 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 10 10) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h1 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 11 10) : BitVec 2) = 1#2 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldrb_post_h2 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 11 10) : BitVec 2) = 1#2 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldrb_post_h3 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 11 10) : BitVec 2) = 1#2 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldrb_post_h4 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 11 10) : BitVec 2) = 1#2 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldrb_post_h5 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 14 10) : BitVec 5) = 31#5) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h5b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 14 10) : BitVec 5) == 31#5) = false := by
  have := disp_ldrb_post_h5 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h6 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 0#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h6b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 0#6) = false := by
  have := disp_ldrb_post_h6 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h7 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 2#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h7b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 2#6) = false := by
  have := disp_ldrb_post_h7 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h8 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 3#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h8b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 3#6) = false := by
  have := disp_ldrb_post_h8 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h9 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 4#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h9b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 4#6) = false := by
  have := disp_ldrb_post_h9 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h10 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 8#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h10b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 8#6) = false := by
  have := disp_ldrb_post_h10 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h11 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 12#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h11b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 12#6) = false := by
  have := disp_ldrb_post_h11 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h12 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 16#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h12b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 16#6) = false := by
  have := disp_ldrb_post_h12 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h13 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 20#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h13b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 20#6) = false := by
  have := disp_ldrb_post_h13 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h14 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 24#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h14b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 24#6) = false := by
  have := disp_ldrb_post_h14 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h15 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 28#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h15b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 28#6) = false := by
  have := disp_ldrb_post_h15 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h16 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 31#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h16b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 31#6) = false := by
  have := disp_ldrb_post_h16 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h17 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 32#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h17b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 32#6) = false := by
  have := disp_ldrb_post_h17 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h18 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 36#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h18b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 36#6) = false := by
  have := disp_ldrb_post_h18 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h19 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 40#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h19b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 40#6) = false := by
  have := disp_ldrb_post_h19 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h20 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 44#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h20b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 44#6) = false := by
  have := disp_ldrb_post_h20 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h21 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) = 63#6) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h21b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 15 10) : BitVec 6) == 63#6) = false := by
  have := disp_ldrb_post_h21 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h22 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 21 21) : BitVec 1) = 0#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h23 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 21 21) : BitVec 1) = 0#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h24 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 22 21) : BitVec 2) = 2#2 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldrb_post_h25 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 22 21) : BitVec 2) = 2#2 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldrb_post_h26 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 22 21) : BitVec 2) = 2#2 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldrb_post_h27 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 22 21) : BitVec 2) = 2#2 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldrb_post_h28 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 22 22) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h29 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 22 22) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h30 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 25 25) : BitVec 1) = 0#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h31 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 27 25) : BitVec 3) = 4#3 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h32 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 27 27) : BitVec 1) = 1#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h33 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h34 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h35 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h36 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h37 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 28 26) : BitVec 3) = 6#3 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h38 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 28 26) : BitVec 3) = 6#3 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h39 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) = 137183#20) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h39b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) == 137183#20) = false := by
  have := disp_ldrb_post_h39 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h40 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) = 137215#20) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h40b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) == 137215#20) = false := by
  have := disp_ldrb_post_h40 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h41 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) = 141279#20) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h41b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) == 141279#20) = false := by
  have := disp_ldrb_post_h41 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h42 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) = 141311#20) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h42b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) == 141311#20) = false := by
  have := disp_ldrb_post_h42 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h43 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) = 145375#20) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h43b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) == 145375#20) = false := by
  have := disp_ldrb_post_h43 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h44 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) = 145407#20) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h44b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) == 145407#20) = false := by
  have := disp_ldrb_post_h44 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h45 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) = 213089#20) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h45b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) == 213089#20) = false := by
  have := disp_ldrb_post_h45 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h46 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) = 217185#20) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h46b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) == 217185#20) = false := by
  have := disp_ldrb_post_h46 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h47 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) = 417794#20) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h47b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) == 417794#20) = false := by
  have := disp_ldrb_post_h47 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h48 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) = 421890#20) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h48b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) == 421890#20) = false := by
  have := disp_ldrb_post_h48 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h49 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) = 929776#20) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h49b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 10) : BitVec 20) == 929776#20) = false := by
  have := disp_ldrb_post_h49 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h50 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) = 49152#18) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h50b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) == 49152#18) = false := by
  have := disp_ldrb_post_h50 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h51 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) = 49156#18) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h51b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) == 49156#18) = false := by
  have := disp_ldrb_post_h51 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h52 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) = 49160#18) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h52b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) == 49160#18) = false := by
  have := disp_ldrb_post_h52 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h53 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) = 50176#18) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h53b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) == 50176#18) = false := by
  have := disp_ldrb_post_h53 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h54 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) = 50180#18) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h54b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) == 50180#18) = false := by
  have := disp_ldrb_post_h54 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h55 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) = 50184#18) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h55b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) == 50184#18) = false := by
  have := disp_ldrb_post_h55 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h56 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) = 54284#18) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h56b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) == 54284#18) = false := by
  have := disp_ldrb_post_h56 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h57 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) = 54286#18) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h57b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) == 54286#18) = false := by
  have := disp_ldrb_post_h57 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h58 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) = 54796#18) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h58b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) == 54796#18) = false := by
  have := disp_ldrb_post_h58 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h59 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) = 54798#18) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h59b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 12) : BitVec 18) == 54798#18) = false := by
  have := disp_ldrb_post_h59 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h60 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 15) : BitVec 15) = 4350#15) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h60b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 15) : BitVec 15) == 4350#15) = false := by
  have := disp_ldrb_post_h60 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h61 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 15) : BitVec 15) = 4351#15) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h61b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 15) : BitVec 15) == 4351#15) = false := by
  have := disp_ldrb_post_h61 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h62 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) = 3072#14) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h62b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) == 3072#14) = false := by
  have := disp_ldrb_post_h62 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h63 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) = 3136#14) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h63b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) == 3136#14) = false := by
  have := disp_ldrb_post_h63 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h64 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) = 3328#14) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h64b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) == 3328#14) = false := by
  have := disp_ldrb_post_h64 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h65 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) = 3360#14) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h65b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) == 3360#14) = false := by
  have := disp_ldrb_post_h65 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h66 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) = 3392#14) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h66b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) == 3392#14) = false := by
  have := disp_ldrb_post_h66 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h67 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) = 3424#14) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h67b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 16) : BitVec 14) == 3424#14) = false := by
  have := disp_ldrb_post_h67 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h68 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h69 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h70 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h71 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h72 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h73 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h74 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h75 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h76 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h77 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h78 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h79 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h80 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h81 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h82 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h83 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 21) : BitVec 9) = 450#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h84 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h85 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h86 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h87 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h88 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h89 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h90 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h91 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h92 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h93 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 22) : BitVec 8) = 225#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h94 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 23) : BitVec 7) = 112#7 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h95 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 23) : BitVec 7) = 112#7 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h96 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h97 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h98 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h99 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h100 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h101 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h102 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 29 24) : BitVec 6) = 56#6 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h103 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h104 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h105 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h106 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h107 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h108 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h109 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h110 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 30 22) : BitVec 9) = 225#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h111 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 137183#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h111b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 137183#22) = false := by
  have := disp_ldrb_post_h111 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h112 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 137215#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h112b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 137215#22) = false := by
  have := disp_ldrb_post_h112 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h113 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 141279#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h113b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 141279#22) = false := by
  have := disp_ldrb_post_h113 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h114 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 141311#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h114b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 141311#22) = false := by
  have := disp_ldrb_post_h114 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h115 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 145375#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h115b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 145375#22) = false := by
  have := disp_ldrb_post_h115 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h116 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 145407#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h116b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 145407#22) = false := by
  have := disp_ldrb_post_h116 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h117 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 929776#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h117b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 929776#22) = false := by
  have := disp_ldrb_post_h117 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h118 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 1185759#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h118b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 1185759#22) = false := by
  have := disp_ldrb_post_h118 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h119 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 1185791#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h119b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 1185791#22) = false := by
  have := disp_ldrb_post_h119 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h120 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 1189855#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h120b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 1189855#22) = false := by
  have := disp_ldrb_post_h120 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h121 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 1189887#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h121b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 1189887#22) = false := by
  have := disp_ldrb_post_h121 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h122 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 1193951#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h122b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 1193951#22) = false := by
  have := disp_ldrb_post_h122 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h123 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 1193983#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h123b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 1193983#22) = false := by
  have := disp_ldrb_post_h123 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h124 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 1978352#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h124b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 1978352#22) = false := by
  have := disp_ldrb_post_h124 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h125 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 3557315#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h125b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 3557315#22) = false := by
  have := disp_ldrb_post_h125 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h126 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 3557319#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h126b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 3557319#22) = false := by
  have := disp_ldrb_post_h126 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h127 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 3557376#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h127b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 3557376#22) = false := by
  have := disp_ldrb_post_h127 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h128 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 3565568#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h128b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 3565568#22) = false := by
  have := disp_ldrb_post_h128 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h129 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 3569664#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h129b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 3569664#22) = false := by
  have := disp_ldrb_post_h129 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h130 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 4067300#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h130b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 4067300#22) = false := by
  have := disp_ldrb_post_h130 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h131 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) = 4067316#22) := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 0) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem disp_ldrb_post_h131b (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 10) : BitVec 22) == 4067316#22) = false := by
  have := disp_ldrb_post_h131 imm9 Rn Rt
  simpa using this

theorem disp_ldrb_post_h132 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h133 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h134 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h135 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h136 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h137 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h138 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h139 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h140 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h141 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h142 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h143 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h144 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h145 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h146 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h147 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h148 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h149 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h150 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h151 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h152 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h153 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h154 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h155 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 21) : BitVec 11) = 450#11 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h156 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h157 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h158 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h159 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h160 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h161 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h162 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h163 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h164 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h165 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h166 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h167 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 22) : BitVec 10) = 225#10 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h168 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h169 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h170 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h171 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h172 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h173 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h174 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h175 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 23) : BitVec 9) = 112#9 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h176 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h177 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h178 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h179 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h180 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h181 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h182 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 24) : BitVec 8) = 56#8 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem disp_ldrb_post_h183 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 31) : BitVec 1) = 0#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h184 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 31 31) : BitVec 1) = 0#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h185 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 0 5 = Rt := by
    unfold CryptoMem.LdstPost.ldstPostWord BitVec.slice
    bv_field

theorem disp_ldrb_post_h186 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 5 5 = Rn := by
    unfold CryptoMem.LdstPost.ldstPostWord BitVec.slice
    bv_field

theorem disp_ldrb_post_h187 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 10 2 = 1#2 := by
    unfold CryptoMem.LdstPost.ldstPostWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldrb_post_h188 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 11 1 = 0#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h189 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 12 9 = imm9 := by
    unfold CryptoMem.LdstPost.ldstPostWord BitVec.slice
    bv_field

theorem disp_ldrb_post_h190 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 21 1 = 0#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h191 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 22 1 = 1#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h192 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 22 2 = 1#2 := by
    unfold CryptoMem.LdstPost.ldstPostWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldrb_post_h193 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 23 1 = 0#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h194 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 30 1 = 0#1 := by
    unfold CryptoMem.LdstPost.ldstPostWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem disp_ldrb_post_h195 (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) 30 2 = 0#2 := by
    unfold CryptoMem.LdstPost.ldstPostWord BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem disp_ldrb_post (pc : Int) (imm9 : BitVec 9) (Rn : BitVec 5) (Rt : BitVec 5) :
    __DecodeA64 (real := real) pc (CryptoMem.LdstPost.ldstPostWord 0#2 1#2 imm9 Rn Rt) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 631))
      if c = true then (do writeReg Register.SEE 631; decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  try simp (config := {decide := true}) only [disp_ldrb_post_h0, disp_ldrb_post_h1, disp_ldrb_post_h2, disp_ldrb_post_h3, disp_ldrb_post_h4, disp_ldrb_post_h5, disp_ldrb_post_h5b, disp_ldrb_post_h6, disp_ldrb_post_h6b, disp_ldrb_post_h7, disp_ldrb_post_h7b, disp_ldrb_post_h8, disp_ldrb_post_h8b, disp_ldrb_post_h9, disp_ldrb_post_h9b, disp_ldrb_post_h10, disp_ldrb_post_h10b, disp_ldrb_post_h11, disp_ldrb_post_h11b, disp_ldrb_post_h12, disp_ldrb_post_h12b, disp_ldrb_post_h13, disp_ldrb_post_h13b, disp_ldrb_post_h14, disp_ldrb_post_h14b, disp_ldrb_post_h15, disp_ldrb_post_h15b, disp_ldrb_post_h16, disp_ldrb_post_h16b, disp_ldrb_post_h17, disp_ldrb_post_h17b, disp_ldrb_post_h18, disp_ldrb_post_h18b, disp_ldrb_post_h19, disp_ldrb_post_h19b, disp_ldrb_post_h20, disp_ldrb_post_h20b, disp_ldrb_post_h21, disp_ldrb_post_h21b, disp_ldrb_post_h22, disp_ldrb_post_h23, disp_ldrb_post_h24, disp_ldrb_post_h25, disp_ldrb_post_h26, disp_ldrb_post_h27, disp_ldrb_post_h28, disp_ldrb_post_h29, disp_ldrb_post_h30, disp_ldrb_post_h31, disp_ldrb_post_h32, disp_ldrb_post_h33, disp_ldrb_post_h34, disp_ldrb_post_h35, disp_ldrb_post_h36, disp_ldrb_post_h37, disp_ldrb_post_h38, disp_ldrb_post_h39, disp_ldrb_post_h39b, disp_ldrb_post_h40, disp_ldrb_post_h40b, disp_ldrb_post_h41, disp_ldrb_post_h41b, disp_ldrb_post_h42, disp_ldrb_post_h42b, disp_ldrb_post_h43, disp_ldrb_post_h43b, disp_ldrb_post_h44, disp_ldrb_post_h44b, disp_ldrb_post_h45, disp_ldrb_post_h45b, disp_ldrb_post_h46, disp_ldrb_post_h46b, disp_ldrb_post_h47, disp_ldrb_post_h47b, disp_ldrb_post_h48, disp_ldrb_post_h48b, disp_ldrb_post_h49, disp_ldrb_post_h49b, disp_ldrb_post_h50, disp_ldrb_post_h50b, disp_ldrb_post_h51, disp_ldrb_post_h51b, disp_ldrb_post_h52, disp_ldrb_post_h52b, disp_ldrb_post_h53, disp_ldrb_post_h53b, disp_ldrb_post_h54, disp_ldrb_post_h54b, disp_ldrb_post_h55, disp_ldrb_post_h55b, disp_ldrb_post_h56, disp_ldrb_post_h56b, disp_ldrb_post_h57, disp_ldrb_post_h57b, disp_ldrb_post_h58, disp_ldrb_post_h58b, disp_ldrb_post_h59, disp_ldrb_post_h59b, disp_ldrb_post_h60, disp_ldrb_post_h60b, disp_ldrb_post_h61, disp_ldrb_post_h61b, disp_ldrb_post_h62, disp_ldrb_post_h62b, disp_ldrb_post_h63, disp_ldrb_post_h63b, disp_ldrb_post_h64, disp_ldrb_post_h64b, disp_ldrb_post_h65, disp_ldrb_post_h65b, disp_ldrb_post_h66, disp_ldrb_post_h66b, disp_ldrb_post_h67, disp_ldrb_post_h67b, disp_ldrb_post_h68, disp_ldrb_post_h69, disp_ldrb_post_h70, disp_ldrb_post_h71, disp_ldrb_post_h72, disp_ldrb_post_h73, disp_ldrb_post_h74, disp_ldrb_post_h75, disp_ldrb_post_h76, disp_ldrb_post_h77, disp_ldrb_post_h78, disp_ldrb_post_h79, disp_ldrb_post_h80, disp_ldrb_post_h81, disp_ldrb_post_h82, disp_ldrb_post_h83, disp_ldrb_post_h84, disp_ldrb_post_h85, disp_ldrb_post_h86, disp_ldrb_post_h87, disp_ldrb_post_h88, disp_ldrb_post_h89, disp_ldrb_post_h90, disp_ldrb_post_h91, disp_ldrb_post_h92, disp_ldrb_post_h93, disp_ldrb_post_h94, disp_ldrb_post_h95, disp_ldrb_post_h96, disp_ldrb_post_h97, disp_ldrb_post_h98, disp_ldrb_post_h99, disp_ldrb_post_h100, disp_ldrb_post_h101, disp_ldrb_post_h102, disp_ldrb_post_h103, disp_ldrb_post_h104, disp_ldrb_post_h105, disp_ldrb_post_h106, disp_ldrb_post_h107, disp_ldrb_post_h108, disp_ldrb_post_h109, disp_ldrb_post_h110, disp_ldrb_post_h111, disp_ldrb_post_h111b, disp_ldrb_post_h112, disp_ldrb_post_h112b, disp_ldrb_post_h113, disp_ldrb_post_h113b, disp_ldrb_post_h114, disp_ldrb_post_h114b, disp_ldrb_post_h115, disp_ldrb_post_h115b, disp_ldrb_post_h116, disp_ldrb_post_h116b, disp_ldrb_post_h117, disp_ldrb_post_h117b, disp_ldrb_post_h118, disp_ldrb_post_h118b, disp_ldrb_post_h119, disp_ldrb_post_h119b, disp_ldrb_post_h120, disp_ldrb_post_h120b, disp_ldrb_post_h121, disp_ldrb_post_h121b, disp_ldrb_post_h122, disp_ldrb_post_h122b, disp_ldrb_post_h123, disp_ldrb_post_h123b, disp_ldrb_post_h124, disp_ldrb_post_h124b, disp_ldrb_post_h125, disp_ldrb_post_h125b, disp_ldrb_post_h126, disp_ldrb_post_h126b, disp_ldrb_post_h127, disp_ldrb_post_h127b, disp_ldrb_post_h128, disp_ldrb_post_h128b, disp_ldrb_post_h129, disp_ldrb_post_h129b, disp_ldrb_post_h130, disp_ldrb_post_h130b, disp_ldrb_post_h131, disp_ldrb_post_h131b, disp_ldrb_post_h132, disp_ldrb_post_h133, disp_ldrb_post_h134, disp_ldrb_post_h135, disp_ldrb_post_h136, disp_ldrb_post_h137, disp_ldrb_post_h138, disp_ldrb_post_h139, disp_ldrb_post_h140, disp_ldrb_post_h141, disp_ldrb_post_h142, disp_ldrb_post_h143, disp_ldrb_post_h144, disp_ldrb_post_h145, disp_ldrb_post_h146, disp_ldrb_post_h147, disp_ldrb_post_h148, disp_ldrb_post_h149, disp_ldrb_post_h150, disp_ldrb_post_h151, disp_ldrb_post_h152, disp_ldrb_post_h153, disp_ldrb_post_h154, disp_ldrb_post_h155, disp_ldrb_post_h156, disp_ldrb_post_h157, disp_ldrb_post_h158, disp_ldrb_post_h159, disp_ldrb_post_h160, disp_ldrb_post_h161, disp_ldrb_post_h162, disp_ldrb_post_h163, disp_ldrb_post_h164, disp_ldrb_post_h165, disp_ldrb_post_h166, disp_ldrb_post_h167, disp_ldrb_post_h168, disp_ldrb_post_h169, disp_ldrb_post_h170, disp_ldrb_post_h171, disp_ldrb_post_h172, disp_ldrb_post_h173, disp_ldrb_post_h174, disp_ldrb_post_h175, disp_ldrb_post_h176, disp_ldrb_post_h177, disp_ldrb_post_h178, disp_ldrb_post_h179, disp_ldrb_post_h180, disp_ldrb_post_h181, disp_ldrb_post_h182, disp_ldrb_post_h183, disp_ldrb_post_h184, disp_ldrb_post_h185, disp_ldrb_post_h186, disp_ldrb_post_h187, disp_ldrb_post_h188, disp_ldrb_post_h189, disp_ldrb_post_h190, disp_ldrb_post_h191, disp_ldrb_post_h192, disp_ldrb_post_h193, disp_ldrb_post_h194, disp_ldrb_post_h195, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore
  try simp (config := {decide := true}) only [disp_ldrb_post_h0, disp_ldrb_post_h1, disp_ldrb_post_h2, disp_ldrb_post_h3, disp_ldrb_post_h4, disp_ldrb_post_h5, disp_ldrb_post_h5b, disp_ldrb_post_h6, disp_ldrb_post_h6b, disp_ldrb_post_h7, disp_ldrb_post_h7b, disp_ldrb_post_h8, disp_ldrb_post_h8b, disp_ldrb_post_h9, disp_ldrb_post_h9b, disp_ldrb_post_h10, disp_ldrb_post_h10b, disp_ldrb_post_h11, disp_ldrb_post_h11b, disp_ldrb_post_h12, disp_ldrb_post_h12b, disp_ldrb_post_h13, disp_ldrb_post_h13b, disp_ldrb_post_h14, disp_ldrb_post_h14b, disp_ldrb_post_h15, disp_ldrb_post_h15b, disp_ldrb_post_h16, disp_ldrb_post_h16b, disp_ldrb_post_h17, disp_ldrb_post_h17b, disp_ldrb_post_h18, disp_ldrb_post_h18b, disp_ldrb_post_h19, disp_ldrb_post_h19b, disp_ldrb_post_h20, disp_ldrb_post_h20b, disp_ldrb_post_h21, disp_ldrb_post_h21b, disp_ldrb_post_h22, disp_ldrb_post_h23, disp_ldrb_post_h24, disp_ldrb_post_h25, disp_ldrb_post_h26, disp_ldrb_post_h27, disp_ldrb_post_h28, disp_ldrb_post_h29, disp_ldrb_post_h30, disp_ldrb_post_h31, disp_ldrb_post_h32, disp_ldrb_post_h33, disp_ldrb_post_h34, disp_ldrb_post_h35, disp_ldrb_post_h36, disp_ldrb_post_h37, disp_ldrb_post_h38, disp_ldrb_post_h39, disp_ldrb_post_h39b, disp_ldrb_post_h40, disp_ldrb_post_h40b, disp_ldrb_post_h41, disp_ldrb_post_h41b, disp_ldrb_post_h42, disp_ldrb_post_h42b, disp_ldrb_post_h43, disp_ldrb_post_h43b, disp_ldrb_post_h44, disp_ldrb_post_h44b, disp_ldrb_post_h45, disp_ldrb_post_h45b, disp_ldrb_post_h46, disp_ldrb_post_h46b, disp_ldrb_post_h47, disp_ldrb_post_h47b, disp_ldrb_post_h48, disp_ldrb_post_h48b, disp_ldrb_post_h49, disp_ldrb_post_h49b, disp_ldrb_post_h50, disp_ldrb_post_h50b, disp_ldrb_post_h51, disp_ldrb_post_h51b, disp_ldrb_post_h52, disp_ldrb_post_h52b, disp_ldrb_post_h53, disp_ldrb_post_h53b, disp_ldrb_post_h54, disp_ldrb_post_h54b, disp_ldrb_post_h55, disp_ldrb_post_h55b, disp_ldrb_post_h56, disp_ldrb_post_h56b, disp_ldrb_post_h57, disp_ldrb_post_h57b, disp_ldrb_post_h58, disp_ldrb_post_h58b, disp_ldrb_post_h59, disp_ldrb_post_h59b, disp_ldrb_post_h60, disp_ldrb_post_h60b, disp_ldrb_post_h61, disp_ldrb_post_h61b, disp_ldrb_post_h62, disp_ldrb_post_h62b, disp_ldrb_post_h63, disp_ldrb_post_h63b, disp_ldrb_post_h64, disp_ldrb_post_h64b, disp_ldrb_post_h65, disp_ldrb_post_h65b, disp_ldrb_post_h66, disp_ldrb_post_h66b, disp_ldrb_post_h67, disp_ldrb_post_h67b, disp_ldrb_post_h68, disp_ldrb_post_h69, disp_ldrb_post_h70, disp_ldrb_post_h71, disp_ldrb_post_h72, disp_ldrb_post_h73, disp_ldrb_post_h74, disp_ldrb_post_h75, disp_ldrb_post_h76, disp_ldrb_post_h77, disp_ldrb_post_h78, disp_ldrb_post_h79, disp_ldrb_post_h80, disp_ldrb_post_h81, disp_ldrb_post_h82, disp_ldrb_post_h83, disp_ldrb_post_h84, disp_ldrb_post_h85, disp_ldrb_post_h86, disp_ldrb_post_h87, disp_ldrb_post_h88, disp_ldrb_post_h89, disp_ldrb_post_h90, disp_ldrb_post_h91, disp_ldrb_post_h92, disp_ldrb_post_h93, disp_ldrb_post_h94, disp_ldrb_post_h95, disp_ldrb_post_h96, disp_ldrb_post_h97, disp_ldrb_post_h98, disp_ldrb_post_h99, disp_ldrb_post_h100, disp_ldrb_post_h101, disp_ldrb_post_h102, disp_ldrb_post_h103, disp_ldrb_post_h104, disp_ldrb_post_h105, disp_ldrb_post_h106, disp_ldrb_post_h107, disp_ldrb_post_h108, disp_ldrb_post_h109, disp_ldrb_post_h110, disp_ldrb_post_h111, disp_ldrb_post_h111b, disp_ldrb_post_h112, disp_ldrb_post_h112b, disp_ldrb_post_h113, disp_ldrb_post_h113b, disp_ldrb_post_h114, disp_ldrb_post_h114b, disp_ldrb_post_h115, disp_ldrb_post_h115b, disp_ldrb_post_h116, disp_ldrb_post_h116b, disp_ldrb_post_h117, disp_ldrb_post_h117b, disp_ldrb_post_h118, disp_ldrb_post_h118b, disp_ldrb_post_h119, disp_ldrb_post_h119b, disp_ldrb_post_h120, disp_ldrb_post_h120b, disp_ldrb_post_h121, disp_ldrb_post_h121b, disp_ldrb_post_h122, disp_ldrb_post_h122b, disp_ldrb_post_h123, disp_ldrb_post_h123b, disp_ldrb_post_h124, disp_ldrb_post_h124b, disp_ldrb_post_h125, disp_ldrb_post_h125b, disp_ldrb_post_h126, disp_ldrb_post_h126b, disp_ldrb_post_h127, disp_ldrb_post_h127b, disp_ldrb_post_h128, disp_ldrb_post_h128b, disp_ldrb_post_h129, disp_ldrb_post_h129b, disp_ldrb_post_h130, disp_ldrb_post_h130b, disp_ldrb_post_h131, disp_ldrb_post_h131b, disp_ldrb_post_h132, disp_ldrb_post_h133, disp_ldrb_post_h134, disp_ldrb_post_h135, disp_ldrb_post_h136, disp_ldrb_post_h137, disp_ldrb_post_h138, disp_ldrb_post_h139, disp_ldrb_post_h140, disp_ldrb_post_h141, disp_ldrb_post_h142, disp_ldrb_post_h143, disp_ldrb_post_h144, disp_ldrb_post_h145, disp_ldrb_post_h146, disp_ldrb_post_h147, disp_ldrb_post_h148, disp_ldrb_post_h149, disp_ldrb_post_h150, disp_ldrb_post_h151, disp_ldrb_post_h152, disp_ldrb_post_h153, disp_ldrb_post_h154, disp_ldrb_post_h155, disp_ldrb_post_h156, disp_ldrb_post_h157, disp_ldrb_post_h158, disp_ldrb_post_h159, disp_ldrb_post_h160, disp_ldrb_post_h161, disp_ldrb_post_h162, disp_ldrb_post_h163, disp_ldrb_post_h164, disp_ldrb_post_h165, disp_ldrb_post_h166, disp_ldrb_post_h167, disp_ldrb_post_h168, disp_ldrb_post_h169, disp_ldrb_post_h170, disp_ldrb_post_h171, disp_ldrb_post_h172, disp_ldrb_post_h173, disp_ldrb_post_h174, disp_ldrb_post_h175, disp_ldrb_post_h176, disp_ldrb_post_h177, disp_ldrb_post_h178, disp_ldrb_post_h179, disp_ldrb_post_h180, disp_ldrb_post_h181, disp_ldrb_post_h182, disp_ldrb_post_h183, disp_ldrb_post_h184, disp_ldrb_post_h185, disp_ldrb_post_h186, disp_ldrb_post_h187, disp_ldrb_post_h188, disp_ldrb_post_h189, disp_ldrb_post_h190, disp_ldrb_post_h191, disp_ldrb_post_h192, disp_ldrb_post_h193, disp_ldrb_post_h194, disp_ldrb_post_h195, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg0
  try simp (config := {decide := true}) only [disp_ldrb_post_h0, disp_ldrb_post_h1, disp_ldrb_post_h2, disp_ldrb_post_h3, disp_ldrb_post_h4, disp_ldrb_post_h5, disp_ldrb_post_h5b, disp_ldrb_post_h6, disp_ldrb_post_h6b, disp_ldrb_post_h7, disp_ldrb_post_h7b, disp_ldrb_post_h8, disp_ldrb_post_h8b, disp_ldrb_post_h9, disp_ldrb_post_h9b, disp_ldrb_post_h10, disp_ldrb_post_h10b, disp_ldrb_post_h11, disp_ldrb_post_h11b, disp_ldrb_post_h12, disp_ldrb_post_h12b, disp_ldrb_post_h13, disp_ldrb_post_h13b, disp_ldrb_post_h14, disp_ldrb_post_h14b, disp_ldrb_post_h15, disp_ldrb_post_h15b, disp_ldrb_post_h16, disp_ldrb_post_h16b, disp_ldrb_post_h17, disp_ldrb_post_h17b, disp_ldrb_post_h18, disp_ldrb_post_h18b, disp_ldrb_post_h19, disp_ldrb_post_h19b, disp_ldrb_post_h20, disp_ldrb_post_h20b, disp_ldrb_post_h21, disp_ldrb_post_h21b, disp_ldrb_post_h22, disp_ldrb_post_h23, disp_ldrb_post_h24, disp_ldrb_post_h25, disp_ldrb_post_h26, disp_ldrb_post_h27, disp_ldrb_post_h28, disp_ldrb_post_h29, disp_ldrb_post_h30, disp_ldrb_post_h31, disp_ldrb_post_h32, disp_ldrb_post_h33, disp_ldrb_post_h34, disp_ldrb_post_h35, disp_ldrb_post_h36, disp_ldrb_post_h37, disp_ldrb_post_h38, disp_ldrb_post_h39, disp_ldrb_post_h39b, disp_ldrb_post_h40, disp_ldrb_post_h40b, disp_ldrb_post_h41, disp_ldrb_post_h41b, disp_ldrb_post_h42, disp_ldrb_post_h42b, disp_ldrb_post_h43, disp_ldrb_post_h43b, disp_ldrb_post_h44, disp_ldrb_post_h44b, disp_ldrb_post_h45, disp_ldrb_post_h45b, disp_ldrb_post_h46, disp_ldrb_post_h46b, disp_ldrb_post_h47, disp_ldrb_post_h47b, disp_ldrb_post_h48, disp_ldrb_post_h48b, disp_ldrb_post_h49, disp_ldrb_post_h49b, disp_ldrb_post_h50, disp_ldrb_post_h50b, disp_ldrb_post_h51, disp_ldrb_post_h51b, disp_ldrb_post_h52, disp_ldrb_post_h52b, disp_ldrb_post_h53, disp_ldrb_post_h53b, disp_ldrb_post_h54, disp_ldrb_post_h54b, disp_ldrb_post_h55, disp_ldrb_post_h55b, disp_ldrb_post_h56, disp_ldrb_post_h56b, disp_ldrb_post_h57, disp_ldrb_post_h57b, disp_ldrb_post_h58, disp_ldrb_post_h58b, disp_ldrb_post_h59, disp_ldrb_post_h59b, disp_ldrb_post_h60, disp_ldrb_post_h60b, disp_ldrb_post_h61, disp_ldrb_post_h61b, disp_ldrb_post_h62, disp_ldrb_post_h62b, disp_ldrb_post_h63, disp_ldrb_post_h63b, disp_ldrb_post_h64, disp_ldrb_post_h64b, disp_ldrb_post_h65, disp_ldrb_post_h65b, disp_ldrb_post_h66, disp_ldrb_post_h66b, disp_ldrb_post_h67, disp_ldrb_post_h67b, disp_ldrb_post_h68, disp_ldrb_post_h69, disp_ldrb_post_h70, disp_ldrb_post_h71, disp_ldrb_post_h72, disp_ldrb_post_h73, disp_ldrb_post_h74, disp_ldrb_post_h75, disp_ldrb_post_h76, disp_ldrb_post_h77, disp_ldrb_post_h78, disp_ldrb_post_h79, disp_ldrb_post_h80, disp_ldrb_post_h81, disp_ldrb_post_h82, disp_ldrb_post_h83, disp_ldrb_post_h84, disp_ldrb_post_h85, disp_ldrb_post_h86, disp_ldrb_post_h87, disp_ldrb_post_h88, disp_ldrb_post_h89, disp_ldrb_post_h90, disp_ldrb_post_h91, disp_ldrb_post_h92, disp_ldrb_post_h93, disp_ldrb_post_h94, disp_ldrb_post_h95, disp_ldrb_post_h96, disp_ldrb_post_h97, disp_ldrb_post_h98, disp_ldrb_post_h99, disp_ldrb_post_h100, disp_ldrb_post_h101, disp_ldrb_post_h102, disp_ldrb_post_h103, disp_ldrb_post_h104, disp_ldrb_post_h105, disp_ldrb_post_h106, disp_ldrb_post_h107, disp_ldrb_post_h108, disp_ldrb_post_h109, disp_ldrb_post_h110, disp_ldrb_post_h111, disp_ldrb_post_h111b, disp_ldrb_post_h112, disp_ldrb_post_h112b, disp_ldrb_post_h113, disp_ldrb_post_h113b, disp_ldrb_post_h114, disp_ldrb_post_h114b, disp_ldrb_post_h115, disp_ldrb_post_h115b, disp_ldrb_post_h116, disp_ldrb_post_h116b, disp_ldrb_post_h117, disp_ldrb_post_h117b, disp_ldrb_post_h118, disp_ldrb_post_h118b, disp_ldrb_post_h119, disp_ldrb_post_h119b, disp_ldrb_post_h120, disp_ldrb_post_h120b, disp_ldrb_post_h121, disp_ldrb_post_h121b, disp_ldrb_post_h122, disp_ldrb_post_h122b, disp_ldrb_post_h123, disp_ldrb_post_h123b, disp_ldrb_post_h124, disp_ldrb_post_h124b, disp_ldrb_post_h125, disp_ldrb_post_h125b, disp_ldrb_post_h126, disp_ldrb_post_h126b, disp_ldrb_post_h127, disp_ldrb_post_h127b, disp_ldrb_post_h128, disp_ldrb_post_h128b, disp_ldrb_post_h129, disp_ldrb_post_h129b, disp_ldrb_post_h130, disp_ldrb_post_h130b, disp_ldrb_post_h131, disp_ldrb_post_h131b, disp_ldrb_post_h132, disp_ldrb_post_h133, disp_ldrb_post_h134, disp_ldrb_post_h135, disp_ldrb_post_h136, disp_ldrb_post_h137, disp_ldrb_post_h138, disp_ldrb_post_h139, disp_ldrb_post_h140, disp_ldrb_post_h141, disp_ldrb_post_h142, disp_ldrb_post_h143, disp_ldrb_post_h144, disp_ldrb_post_h145, disp_ldrb_post_h146, disp_ldrb_post_h147, disp_ldrb_post_h148, disp_ldrb_post_h149, disp_ldrb_post_h150, disp_ldrb_post_h151, disp_ldrb_post_h152, disp_ldrb_post_h153, disp_ldrb_post_h154, disp_ldrb_post_h155, disp_ldrb_post_h156, disp_ldrb_post_h157, disp_ldrb_post_h158, disp_ldrb_post_h159, disp_ldrb_post_h160, disp_ldrb_post_h161, disp_ldrb_post_h162, disp_ldrb_post_h163, disp_ldrb_post_h164, disp_ldrb_post_h165, disp_ldrb_post_h166, disp_ldrb_post_h167, disp_ldrb_post_h168, disp_ldrb_post_h169, disp_ldrb_post_h170, disp_ldrb_post_h171, disp_ldrb_post_h172, disp_ldrb_post_h173, disp_ldrb_post_h174, disp_ldrb_post_h175, disp_ldrb_post_h176, disp_ldrb_post_h177, disp_ldrb_post_h178, disp_ldrb_post_h179, disp_ldrb_post_h180, disp_ldrb_post_h181, disp_ldrb_post_h182, disp_ldrb_post_h183, disp_ldrb_post_h184, disp_ldrb_post_h185, disp_ldrb_post_h186, disp_ldrb_post_h187, disp_ldrb_post_h188, disp_ldrb_post_h189, disp_ldrb_post_h190, disp_ldrb_post_h191, disp_ldrb_post_h192, disp_ldrb_post_h193, disp_ldrb_post_h194, disp_ldrb_post_h195, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg1
  try simp (config := {decide := true}) only [disp_ldrb_post_h0, disp_ldrb_post_h1, disp_ldrb_post_h2, disp_ldrb_post_h3, disp_ldrb_post_h4, disp_ldrb_post_h5, disp_ldrb_post_h5b, disp_ldrb_post_h6, disp_ldrb_post_h6b, disp_ldrb_post_h7, disp_ldrb_post_h7b, disp_ldrb_post_h8, disp_ldrb_post_h8b, disp_ldrb_post_h9, disp_ldrb_post_h9b, disp_ldrb_post_h10, disp_ldrb_post_h10b, disp_ldrb_post_h11, disp_ldrb_post_h11b, disp_ldrb_post_h12, disp_ldrb_post_h12b, disp_ldrb_post_h13, disp_ldrb_post_h13b, disp_ldrb_post_h14, disp_ldrb_post_h14b, disp_ldrb_post_h15, disp_ldrb_post_h15b, disp_ldrb_post_h16, disp_ldrb_post_h16b, disp_ldrb_post_h17, disp_ldrb_post_h17b, disp_ldrb_post_h18, disp_ldrb_post_h18b, disp_ldrb_post_h19, disp_ldrb_post_h19b, disp_ldrb_post_h20, disp_ldrb_post_h20b, disp_ldrb_post_h21, disp_ldrb_post_h21b, disp_ldrb_post_h22, disp_ldrb_post_h23, disp_ldrb_post_h24, disp_ldrb_post_h25, disp_ldrb_post_h26, disp_ldrb_post_h27, disp_ldrb_post_h28, disp_ldrb_post_h29, disp_ldrb_post_h30, disp_ldrb_post_h31, disp_ldrb_post_h32, disp_ldrb_post_h33, disp_ldrb_post_h34, disp_ldrb_post_h35, disp_ldrb_post_h36, disp_ldrb_post_h37, disp_ldrb_post_h38, disp_ldrb_post_h39, disp_ldrb_post_h39b, disp_ldrb_post_h40, disp_ldrb_post_h40b, disp_ldrb_post_h41, disp_ldrb_post_h41b, disp_ldrb_post_h42, disp_ldrb_post_h42b, disp_ldrb_post_h43, disp_ldrb_post_h43b, disp_ldrb_post_h44, disp_ldrb_post_h44b, disp_ldrb_post_h45, disp_ldrb_post_h45b, disp_ldrb_post_h46, disp_ldrb_post_h46b, disp_ldrb_post_h47, disp_ldrb_post_h47b, disp_ldrb_post_h48, disp_ldrb_post_h48b, disp_ldrb_post_h49, disp_ldrb_post_h49b, disp_ldrb_post_h50, disp_ldrb_post_h50b, disp_ldrb_post_h51, disp_ldrb_post_h51b, disp_ldrb_post_h52, disp_ldrb_post_h52b, disp_ldrb_post_h53, disp_ldrb_post_h53b, disp_ldrb_post_h54, disp_ldrb_post_h54b, disp_ldrb_post_h55, disp_ldrb_post_h55b, disp_ldrb_post_h56, disp_ldrb_post_h56b, disp_ldrb_post_h57, disp_ldrb_post_h57b, disp_ldrb_post_h58, disp_ldrb_post_h58b, disp_ldrb_post_h59, disp_ldrb_post_h59b, disp_ldrb_post_h60, disp_ldrb_post_h60b, disp_ldrb_post_h61, disp_ldrb_post_h61b, disp_ldrb_post_h62, disp_ldrb_post_h62b, disp_ldrb_post_h63, disp_ldrb_post_h63b, disp_ldrb_post_h64, disp_ldrb_post_h64b, disp_ldrb_post_h65, disp_ldrb_post_h65b, disp_ldrb_post_h66, disp_ldrb_post_h66b, disp_ldrb_post_h67, disp_ldrb_post_h67b, disp_ldrb_post_h68, disp_ldrb_post_h69, disp_ldrb_post_h70, disp_ldrb_post_h71, disp_ldrb_post_h72, disp_ldrb_post_h73, disp_ldrb_post_h74, disp_ldrb_post_h75, disp_ldrb_post_h76, disp_ldrb_post_h77, disp_ldrb_post_h78, disp_ldrb_post_h79, disp_ldrb_post_h80, disp_ldrb_post_h81, disp_ldrb_post_h82, disp_ldrb_post_h83, disp_ldrb_post_h84, disp_ldrb_post_h85, disp_ldrb_post_h86, disp_ldrb_post_h87, disp_ldrb_post_h88, disp_ldrb_post_h89, disp_ldrb_post_h90, disp_ldrb_post_h91, disp_ldrb_post_h92, disp_ldrb_post_h93, disp_ldrb_post_h94, disp_ldrb_post_h95, disp_ldrb_post_h96, disp_ldrb_post_h97, disp_ldrb_post_h98, disp_ldrb_post_h99, disp_ldrb_post_h100, disp_ldrb_post_h101, disp_ldrb_post_h102, disp_ldrb_post_h103, disp_ldrb_post_h104, disp_ldrb_post_h105, disp_ldrb_post_h106, disp_ldrb_post_h107, disp_ldrb_post_h108, disp_ldrb_post_h109, disp_ldrb_post_h110, disp_ldrb_post_h111, disp_ldrb_post_h111b, disp_ldrb_post_h112, disp_ldrb_post_h112b, disp_ldrb_post_h113, disp_ldrb_post_h113b, disp_ldrb_post_h114, disp_ldrb_post_h114b, disp_ldrb_post_h115, disp_ldrb_post_h115b, disp_ldrb_post_h116, disp_ldrb_post_h116b, disp_ldrb_post_h117, disp_ldrb_post_h117b, disp_ldrb_post_h118, disp_ldrb_post_h118b, disp_ldrb_post_h119, disp_ldrb_post_h119b, disp_ldrb_post_h120, disp_ldrb_post_h120b, disp_ldrb_post_h121, disp_ldrb_post_h121b, disp_ldrb_post_h122, disp_ldrb_post_h122b, disp_ldrb_post_h123, disp_ldrb_post_h123b, disp_ldrb_post_h124, disp_ldrb_post_h124b, disp_ldrb_post_h125, disp_ldrb_post_h125b, disp_ldrb_post_h126, disp_ldrb_post_h126b, disp_ldrb_post_h127, disp_ldrb_post_h127b, disp_ldrb_post_h128, disp_ldrb_post_h128b, disp_ldrb_post_h129, disp_ldrb_post_h129b, disp_ldrb_post_h130, disp_ldrb_post_h130b, disp_ldrb_post_h131, disp_ldrb_post_h131b, disp_ldrb_post_h132, disp_ldrb_post_h133, disp_ldrb_post_h134, disp_ldrb_post_h135, disp_ldrb_post_h136, disp_ldrb_post_h137, disp_ldrb_post_h138, disp_ldrb_post_h139, disp_ldrb_post_h140, disp_ldrb_post_h141, disp_ldrb_post_h142, disp_ldrb_post_h143, disp_ldrb_post_h144, disp_ldrb_post_h145, disp_ldrb_post_h146, disp_ldrb_post_h147, disp_ldrb_post_h148, disp_ldrb_post_h149, disp_ldrb_post_h150, disp_ldrb_post_h151, disp_ldrb_post_h152, disp_ldrb_post_h153, disp_ldrb_post_h154, disp_ldrb_post_h155, disp_ldrb_post_h156, disp_ldrb_post_h157, disp_ldrb_post_h158, disp_ldrb_post_h159, disp_ldrb_post_h160, disp_ldrb_post_h161, disp_ldrb_post_h162, disp_ldrb_post_h163, disp_ldrb_post_h164, disp_ldrb_post_h165, disp_ldrb_post_h166, disp_ldrb_post_h167, disp_ldrb_post_h168, disp_ldrb_post_h169, disp_ldrb_post_h170, disp_ldrb_post_h171, disp_ldrb_post_h172, disp_ldrb_post_h173, disp_ldrb_post_h174, disp_ldrb_post_h175, disp_ldrb_post_h176, disp_ldrb_post_h177, disp_ldrb_post_h178, disp_ldrb_post_h179, disp_ldrb_post_h180, disp_ldrb_post_h181, disp_ldrb_post_h182, disp_ldrb_post_h183, disp_ldrb_post_h184, disp_ldrb_post_h185, disp_ldrb_post_h186, disp_ldrb_post_h187, disp_ldrb_post_h188, disp_ldrb_post_h189, disp_ldrb_post_h190, disp_ldrb_post_h191, disp_ldrb_post_h192, disp_ldrb_post_h193, disp_ldrb_post_h194, disp_ldrb_post_h195, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg2
  try simp (config := {decide := true}) only [disp_ldrb_post_h0, disp_ldrb_post_h1, disp_ldrb_post_h2, disp_ldrb_post_h3, disp_ldrb_post_h4, disp_ldrb_post_h5, disp_ldrb_post_h5b, disp_ldrb_post_h6, disp_ldrb_post_h6b, disp_ldrb_post_h7, disp_ldrb_post_h7b, disp_ldrb_post_h8, disp_ldrb_post_h8b, disp_ldrb_post_h9, disp_ldrb_post_h9b, disp_ldrb_post_h10, disp_ldrb_post_h10b, disp_ldrb_post_h11, disp_ldrb_post_h11b, disp_ldrb_post_h12, disp_ldrb_post_h12b, disp_ldrb_post_h13, disp_ldrb_post_h13b, disp_ldrb_post_h14, disp_ldrb_post_h14b, disp_ldrb_post_h15, disp_ldrb_post_h15b, disp_ldrb_post_h16, disp_ldrb_post_h16b, disp_ldrb_post_h17, disp_ldrb_post_h17b, disp_ldrb_post_h18, disp_ldrb_post_h18b, disp_ldrb_post_h19, disp_ldrb_post_h19b, disp_ldrb_post_h20, disp_ldrb_post_h20b, disp_ldrb_post_h21, disp_ldrb_post_h21b, disp_ldrb_post_h22, disp_ldrb_post_h23, disp_ldrb_post_h24, disp_ldrb_post_h25, disp_ldrb_post_h26, disp_ldrb_post_h27, disp_ldrb_post_h28, disp_ldrb_post_h29, disp_ldrb_post_h30, disp_ldrb_post_h31, disp_ldrb_post_h32, disp_ldrb_post_h33, disp_ldrb_post_h34, disp_ldrb_post_h35, disp_ldrb_post_h36, disp_ldrb_post_h37, disp_ldrb_post_h38, disp_ldrb_post_h39, disp_ldrb_post_h39b, disp_ldrb_post_h40, disp_ldrb_post_h40b, disp_ldrb_post_h41, disp_ldrb_post_h41b, disp_ldrb_post_h42, disp_ldrb_post_h42b, disp_ldrb_post_h43, disp_ldrb_post_h43b, disp_ldrb_post_h44, disp_ldrb_post_h44b, disp_ldrb_post_h45, disp_ldrb_post_h45b, disp_ldrb_post_h46, disp_ldrb_post_h46b, disp_ldrb_post_h47, disp_ldrb_post_h47b, disp_ldrb_post_h48, disp_ldrb_post_h48b, disp_ldrb_post_h49, disp_ldrb_post_h49b, disp_ldrb_post_h50, disp_ldrb_post_h50b, disp_ldrb_post_h51, disp_ldrb_post_h51b, disp_ldrb_post_h52, disp_ldrb_post_h52b, disp_ldrb_post_h53, disp_ldrb_post_h53b, disp_ldrb_post_h54, disp_ldrb_post_h54b, disp_ldrb_post_h55, disp_ldrb_post_h55b, disp_ldrb_post_h56, disp_ldrb_post_h56b, disp_ldrb_post_h57, disp_ldrb_post_h57b, disp_ldrb_post_h58, disp_ldrb_post_h58b, disp_ldrb_post_h59, disp_ldrb_post_h59b, disp_ldrb_post_h60, disp_ldrb_post_h60b, disp_ldrb_post_h61, disp_ldrb_post_h61b, disp_ldrb_post_h62, disp_ldrb_post_h62b, disp_ldrb_post_h63, disp_ldrb_post_h63b, disp_ldrb_post_h64, disp_ldrb_post_h64b, disp_ldrb_post_h65, disp_ldrb_post_h65b, disp_ldrb_post_h66, disp_ldrb_post_h66b, disp_ldrb_post_h67, disp_ldrb_post_h67b, disp_ldrb_post_h68, disp_ldrb_post_h69, disp_ldrb_post_h70, disp_ldrb_post_h71, disp_ldrb_post_h72, disp_ldrb_post_h73, disp_ldrb_post_h74, disp_ldrb_post_h75, disp_ldrb_post_h76, disp_ldrb_post_h77, disp_ldrb_post_h78, disp_ldrb_post_h79, disp_ldrb_post_h80, disp_ldrb_post_h81, disp_ldrb_post_h82, disp_ldrb_post_h83, disp_ldrb_post_h84, disp_ldrb_post_h85, disp_ldrb_post_h86, disp_ldrb_post_h87, disp_ldrb_post_h88, disp_ldrb_post_h89, disp_ldrb_post_h90, disp_ldrb_post_h91, disp_ldrb_post_h92, disp_ldrb_post_h93, disp_ldrb_post_h94, disp_ldrb_post_h95, disp_ldrb_post_h96, disp_ldrb_post_h97, disp_ldrb_post_h98, disp_ldrb_post_h99, disp_ldrb_post_h100, disp_ldrb_post_h101, disp_ldrb_post_h102, disp_ldrb_post_h103, disp_ldrb_post_h104, disp_ldrb_post_h105, disp_ldrb_post_h106, disp_ldrb_post_h107, disp_ldrb_post_h108, disp_ldrb_post_h109, disp_ldrb_post_h110, disp_ldrb_post_h111, disp_ldrb_post_h111b, disp_ldrb_post_h112, disp_ldrb_post_h112b, disp_ldrb_post_h113, disp_ldrb_post_h113b, disp_ldrb_post_h114, disp_ldrb_post_h114b, disp_ldrb_post_h115, disp_ldrb_post_h115b, disp_ldrb_post_h116, disp_ldrb_post_h116b, disp_ldrb_post_h117, disp_ldrb_post_h117b, disp_ldrb_post_h118, disp_ldrb_post_h118b, disp_ldrb_post_h119, disp_ldrb_post_h119b, disp_ldrb_post_h120, disp_ldrb_post_h120b, disp_ldrb_post_h121, disp_ldrb_post_h121b, disp_ldrb_post_h122, disp_ldrb_post_h122b, disp_ldrb_post_h123, disp_ldrb_post_h123b, disp_ldrb_post_h124, disp_ldrb_post_h124b, disp_ldrb_post_h125, disp_ldrb_post_h125b, disp_ldrb_post_h126, disp_ldrb_post_h126b, disp_ldrb_post_h127, disp_ldrb_post_h127b, disp_ldrb_post_h128, disp_ldrb_post_h128b, disp_ldrb_post_h129, disp_ldrb_post_h129b, disp_ldrb_post_h130, disp_ldrb_post_h130b, disp_ldrb_post_h131, disp_ldrb_post_h131b, disp_ldrb_post_h132, disp_ldrb_post_h133, disp_ldrb_post_h134, disp_ldrb_post_h135, disp_ldrb_post_h136, disp_ldrb_post_h137, disp_ldrb_post_h138, disp_ldrb_post_h139, disp_ldrb_post_h140, disp_ldrb_post_h141, disp_ldrb_post_h142, disp_ldrb_post_h143, disp_ldrb_post_h144, disp_ldrb_post_h145, disp_ldrb_post_h146, disp_ldrb_post_h147, disp_ldrb_post_h148, disp_ldrb_post_h149, disp_ldrb_post_h150, disp_ldrb_post_h151, disp_ldrb_post_h152, disp_ldrb_post_h153, disp_ldrb_post_h154, disp_ldrb_post_h155, disp_ldrb_post_h156, disp_ldrb_post_h157, disp_ldrb_post_h158, disp_ldrb_post_h159, disp_ldrb_post_h160, disp_ldrb_post_h161, disp_ldrb_post_h162, disp_ldrb_post_h163, disp_ldrb_post_h164, disp_ldrb_post_h165, disp_ldrb_post_h166, disp_ldrb_post_h167, disp_ldrb_post_h168, disp_ldrb_post_h169, disp_ldrb_post_h170, disp_ldrb_post_h171, disp_ldrb_post_h172, disp_ldrb_post_h173, disp_ldrb_post_h174, disp_ldrb_post_h175, disp_ldrb_post_h176, disp_ldrb_post_h177, disp_ldrb_post_h178, disp_ldrb_post_h179, disp_ldrb_post_h180, disp_ldrb_post_h181, disp_ldrb_post_h182, disp_ldrb_post_h183, disp_ldrb_post_h184, disp_ldrb_post_h185, disp_ldrb_post_h186, disp_ldrb_post_h187, disp_ldrb_post_h188, disp_ldrb_post_h189, disp_ldrb_post_h190, disp_ldrb_post_h191, disp_ldrb_post_h192, disp_ldrb_post_h193, disp_ldrb_post_h194, disp_ldrb_post_h195, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg3
  try simp (config := {decide := true}) only [disp_ldrb_post_h0, disp_ldrb_post_h1, disp_ldrb_post_h2, disp_ldrb_post_h3, disp_ldrb_post_h4, disp_ldrb_post_h5, disp_ldrb_post_h5b, disp_ldrb_post_h6, disp_ldrb_post_h6b, disp_ldrb_post_h7, disp_ldrb_post_h7b, disp_ldrb_post_h8, disp_ldrb_post_h8b, disp_ldrb_post_h9, disp_ldrb_post_h9b, disp_ldrb_post_h10, disp_ldrb_post_h10b, disp_ldrb_post_h11, disp_ldrb_post_h11b, disp_ldrb_post_h12, disp_ldrb_post_h12b, disp_ldrb_post_h13, disp_ldrb_post_h13b, disp_ldrb_post_h14, disp_ldrb_post_h14b, disp_ldrb_post_h15, disp_ldrb_post_h15b, disp_ldrb_post_h16, disp_ldrb_post_h16b, disp_ldrb_post_h17, disp_ldrb_post_h17b, disp_ldrb_post_h18, disp_ldrb_post_h18b, disp_ldrb_post_h19, disp_ldrb_post_h19b, disp_ldrb_post_h20, disp_ldrb_post_h20b, disp_ldrb_post_h21, disp_ldrb_post_h21b, disp_ldrb_post_h22, disp_ldrb_post_h23, disp_ldrb_post_h24, disp_ldrb_post_h25, disp_ldrb_post_h26, disp_ldrb_post_h27, disp_ldrb_post_h28, disp_ldrb_post_h29, disp_ldrb_post_h30, disp_ldrb_post_h31, disp_ldrb_post_h32, disp_ldrb_post_h33, disp_ldrb_post_h34, disp_ldrb_post_h35, disp_ldrb_post_h36, disp_ldrb_post_h37, disp_ldrb_post_h38, disp_ldrb_post_h39, disp_ldrb_post_h39b, disp_ldrb_post_h40, disp_ldrb_post_h40b, disp_ldrb_post_h41, disp_ldrb_post_h41b, disp_ldrb_post_h42, disp_ldrb_post_h42b, disp_ldrb_post_h43, disp_ldrb_post_h43b, disp_ldrb_post_h44, disp_ldrb_post_h44b, disp_ldrb_post_h45, disp_ldrb_post_h45b, disp_ldrb_post_h46, disp_ldrb_post_h46b, disp_ldrb_post_h47, disp_ldrb_post_h47b, disp_ldrb_post_h48, disp_ldrb_post_h48b, disp_ldrb_post_h49, disp_ldrb_post_h49b, disp_ldrb_post_h50, disp_ldrb_post_h50b, disp_ldrb_post_h51, disp_ldrb_post_h51b, disp_ldrb_post_h52, disp_ldrb_post_h52b, disp_ldrb_post_h53, disp_ldrb_post_h53b, disp_ldrb_post_h54, disp_ldrb_post_h54b, disp_ldrb_post_h55, disp_ldrb_post_h55b, disp_ldrb_post_h56, disp_ldrb_post_h56b, disp_ldrb_post_h57, disp_ldrb_post_h57b, disp_ldrb_post_h58, disp_ldrb_post_h58b, disp_ldrb_post_h59, disp_ldrb_post_h59b, disp_ldrb_post_h60, disp_ldrb_post_h60b, disp_ldrb_post_h61, disp_ldrb_post_h61b, disp_ldrb_post_h62, disp_ldrb_post_h62b, disp_ldrb_post_h63, disp_ldrb_post_h63b, disp_ldrb_post_h64, disp_ldrb_post_h64b, disp_ldrb_post_h65, disp_ldrb_post_h65b, disp_ldrb_post_h66, disp_ldrb_post_h66b, disp_ldrb_post_h67, disp_ldrb_post_h67b, disp_ldrb_post_h68, disp_ldrb_post_h69, disp_ldrb_post_h70, disp_ldrb_post_h71, disp_ldrb_post_h72, disp_ldrb_post_h73, disp_ldrb_post_h74, disp_ldrb_post_h75, disp_ldrb_post_h76, disp_ldrb_post_h77, disp_ldrb_post_h78, disp_ldrb_post_h79, disp_ldrb_post_h80, disp_ldrb_post_h81, disp_ldrb_post_h82, disp_ldrb_post_h83, disp_ldrb_post_h84, disp_ldrb_post_h85, disp_ldrb_post_h86, disp_ldrb_post_h87, disp_ldrb_post_h88, disp_ldrb_post_h89, disp_ldrb_post_h90, disp_ldrb_post_h91, disp_ldrb_post_h92, disp_ldrb_post_h93, disp_ldrb_post_h94, disp_ldrb_post_h95, disp_ldrb_post_h96, disp_ldrb_post_h97, disp_ldrb_post_h98, disp_ldrb_post_h99, disp_ldrb_post_h100, disp_ldrb_post_h101, disp_ldrb_post_h102, disp_ldrb_post_h103, disp_ldrb_post_h104, disp_ldrb_post_h105, disp_ldrb_post_h106, disp_ldrb_post_h107, disp_ldrb_post_h108, disp_ldrb_post_h109, disp_ldrb_post_h110, disp_ldrb_post_h111, disp_ldrb_post_h111b, disp_ldrb_post_h112, disp_ldrb_post_h112b, disp_ldrb_post_h113, disp_ldrb_post_h113b, disp_ldrb_post_h114, disp_ldrb_post_h114b, disp_ldrb_post_h115, disp_ldrb_post_h115b, disp_ldrb_post_h116, disp_ldrb_post_h116b, disp_ldrb_post_h117, disp_ldrb_post_h117b, disp_ldrb_post_h118, disp_ldrb_post_h118b, disp_ldrb_post_h119, disp_ldrb_post_h119b, disp_ldrb_post_h120, disp_ldrb_post_h120b, disp_ldrb_post_h121, disp_ldrb_post_h121b, disp_ldrb_post_h122, disp_ldrb_post_h122b, disp_ldrb_post_h123, disp_ldrb_post_h123b, disp_ldrb_post_h124, disp_ldrb_post_h124b, disp_ldrb_post_h125, disp_ldrb_post_h125b, disp_ldrb_post_h126, disp_ldrb_post_h126b, disp_ldrb_post_h127, disp_ldrb_post_h127b, disp_ldrb_post_h128, disp_ldrb_post_h128b, disp_ldrb_post_h129, disp_ldrb_post_h129b, disp_ldrb_post_h130, disp_ldrb_post_h130b, disp_ldrb_post_h131, disp_ldrb_post_h131b, disp_ldrb_post_h132, disp_ldrb_post_h133, disp_ldrb_post_h134, disp_ldrb_post_h135, disp_ldrb_post_h136, disp_ldrb_post_h137, disp_ldrb_post_h138, disp_ldrb_post_h139, disp_ldrb_post_h140, disp_ldrb_post_h141, disp_ldrb_post_h142, disp_ldrb_post_h143, disp_ldrb_post_h144, disp_ldrb_post_h145, disp_ldrb_post_h146, disp_ldrb_post_h147, disp_ldrb_post_h148, disp_ldrb_post_h149, disp_ldrb_post_h150, disp_ldrb_post_h151, disp_ldrb_post_h152, disp_ldrb_post_h153, disp_ldrb_post_h154, disp_ldrb_post_h155, disp_ldrb_post_h156, disp_ldrb_post_h157, disp_ldrb_post_h158, disp_ldrb_post_h159, disp_ldrb_post_h160, disp_ldrb_post_h161, disp_ldrb_post_h162, disp_ldrb_post_h163, disp_ldrb_post_h164, disp_ldrb_post_h165, disp_ldrb_post_h166, disp_ldrb_post_h167, disp_ldrb_post_h168, disp_ldrb_post_h169, disp_ldrb_post_h170, disp_ldrb_post_h171, disp_ldrb_post_h172, disp_ldrb_post_h173, disp_ldrb_post_h174, disp_ldrb_post_h175, disp_ldrb_post_h176, disp_ldrb_post_h177, disp_ldrb_post_h178, disp_ldrb_post_h179, disp_ldrb_post_h180, disp_ldrb_post_h181, disp_ldrb_post_h182, disp_ldrb_post_h183, disp_ldrb_post_h184, disp_ldrb_post_h185, disp_ldrb_post_h186, disp_ldrb_post_h187, disp_ldrb_post_h188, disp_ldrb_post_h189, disp_ldrb_post_h190, disp_ldrb_post_h191, disp_ldrb_post_h192, disp_ldrb_post_h193, disp_ldrb_post_h194, disp_ldrb_post_h195, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg4
  try simp (config := {decide := true}) only [disp_ldrb_post_h0, disp_ldrb_post_h1, disp_ldrb_post_h2, disp_ldrb_post_h3, disp_ldrb_post_h4, disp_ldrb_post_h5, disp_ldrb_post_h5b, disp_ldrb_post_h6, disp_ldrb_post_h6b, disp_ldrb_post_h7, disp_ldrb_post_h7b, disp_ldrb_post_h8, disp_ldrb_post_h8b, disp_ldrb_post_h9, disp_ldrb_post_h9b, disp_ldrb_post_h10, disp_ldrb_post_h10b, disp_ldrb_post_h11, disp_ldrb_post_h11b, disp_ldrb_post_h12, disp_ldrb_post_h12b, disp_ldrb_post_h13, disp_ldrb_post_h13b, disp_ldrb_post_h14, disp_ldrb_post_h14b, disp_ldrb_post_h15, disp_ldrb_post_h15b, disp_ldrb_post_h16, disp_ldrb_post_h16b, disp_ldrb_post_h17, disp_ldrb_post_h17b, disp_ldrb_post_h18, disp_ldrb_post_h18b, disp_ldrb_post_h19, disp_ldrb_post_h19b, disp_ldrb_post_h20, disp_ldrb_post_h20b, disp_ldrb_post_h21, disp_ldrb_post_h21b, disp_ldrb_post_h22, disp_ldrb_post_h23, disp_ldrb_post_h24, disp_ldrb_post_h25, disp_ldrb_post_h26, disp_ldrb_post_h27, disp_ldrb_post_h28, disp_ldrb_post_h29, disp_ldrb_post_h30, disp_ldrb_post_h31, disp_ldrb_post_h32, disp_ldrb_post_h33, disp_ldrb_post_h34, disp_ldrb_post_h35, disp_ldrb_post_h36, disp_ldrb_post_h37, disp_ldrb_post_h38, disp_ldrb_post_h39, disp_ldrb_post_h39b, disp_ldrb_post_h40, disp_ldrb_post_h40b, disp_ldrb_post_h41, disp_ldrb_post_h41b, disp_ldrb_post_h42, disp_ldrb_post_h42b, disp_ldrb_post_h43, disp_ldrb_post_h43b, disp_ldrb_post_h44, disp_ldrb_post_h44b, disp_ldrb_post_h45, disp_ldrb_post_h45b, disp_ldrb_post_h46, disp_ldrb_post_h46b, disp_ldrb_post_h47, disp_ldrb_post_h47b, disp_ldrb_post_h48, disp_ldrb_post_h48b, disp_ldrb_post_h49, disp_ldrb_post_h49b, disp_ldrb_post_h50, disp_ldrb_post_h50b, disp_ldrb_post_h51, disp_ldrb_post_h51b, disp_ldrb_post_h52, disp_ldrb_post_h52b, disp_ldrb_post_h53, disp_ldrb_post_h53b, disp_ldrb_post_h54, disp_ldrb_post_h54b, disp_ldrb_post_h55, disp_ldrb_post_h55b, disp_ldrb_post_h56, disp_ldrb_post_h56b, disp_ldrb_post_h57, disp_ldrb_post_h57b, disp_ldrb_post_h58, disp_ldrb_post_h58b, disp_ldrb_post_h59, disp_ldrb_post_h59b, disp_ldrb_post_h60, disp_ldrb_post_h60b, disp_ldrb_post_h61, disp_ldrb_post_h61b, disp_ldrb_post_h62, disp_ldrb_post_h62b, disp_ldrb_post_h63, disp_ldrb_post_h63b, disp_ldrb_post_h64, disp_ldrb_post_h64b, disp_ldrb_post_h65, disp_ldrb_post_h65b, disp_ldrb_post_h66, disp_ldrb_post_h66b, disp_ldrb_post_h67, disp_ldrb_post_h67b, disp_ldrb_post_h68, disp_ldrb_post_h69, disp_ldrb_post_h70, disp_ldrb_post_h71, disp_ldrb_post_h72, disp_ldrb_post_h73, disp_ldrb_post_h74, disp_ldrb_post_h75, disp_ldrb_post_h76, disp_ldrb_post_h77, disp_ldrb_post_h78, disp_ldrb_post_h79, disp_ldrb_post_h80, disp_ldrb_post_h81, disp_ldrb_post_h82, disp_ldrb_post_h83, disp_ldrb_post_h84, disp_ldrb_post_h85, disp_ldrb_post_h86, disp_ldrb_post_h87, disp_ldrb_post_h88, disp_ldrb_post_h89, disp_ldrb_post_h90, disp_ldrb_post_h91, disp_ldrb_post_h92, disp_ldrb_post_h93, disp_ldrb_post_h94, disp_ldrb_post_h95, disp_ldrb_post_h96, disp_ldrb_post_h97, disp_ldrb_post_h98, disp_ldrb_post_h99, disp_ldrb_post_h100, disp_ldrb_post_h101, disp_ldrb_post_h102, disp_ldrb_post_h103, disp_ldrb_post_h104, disp_ldrb_post_h105, disp_ldrb_post_h106, disp_ldrb_post_h107, disp_ldrb_post_h108, disp_ldrb_post_h109, disp_ldrb_post_h110, disp_ldrb_post_h111, disp_ldrb_post_h111b, disp_ldrb_post_h112, disp_ldrb_post_h112b, disp_ldrb_post_h113, disp_ldrb_post_h113b, disp_ldrb_post_h114, disp_ldrb_post_h114b, disp_ldrb_post_h115, disp_ldrb_post_h115b, disp_ldrb_post_h116, disp_ldrb_post_h116b, disp_ldrb_post_h117, disp_ldrb_post_h117b, disp_ldrb_post_h118, disp_ldrb_post_h118b, disp_ldrb_post_h119, disp_ldrb_post_h119b, disp_ldrb_post_h120, disp_ldrb_post_h120b, disp_ldrb_post_h121, disp_ldrb_post_h121b, disp_ldrb_post_h122, disp_ldrb_post_h122b, disp_ldrb_post_h123, disp_ldrb_post_h123b, disp_ldrb_post_h124, disp_ldrb_post_h124b, disp_ldrb_post_h125, disp_ldrb_post_h125b, disp_ldrb_post_h126, disp_ldrb_post_h126b, disp_ldrb_post_h127, disp_ldrb_post_h127b, disp_ldrb_post_h128, disp_ldrb_post_h128b, disp_ldrb_post_h129, disp_ldrb_post_h129b, disp_ldrb_post_h130, disp_ldrb_post_h130b, disp_ldrb_post_h131, disp_ldrb_post_h131b, disp_ldrb_post_h132, disp_ldrb_post_h133, disp_ldrb_post_h134, disp_ldrb_post_h135, disp_ldrb_post_h136, disp_ldrb_post_h137, disp_ldrb_post_h138, disp_ldrb_post_h139, disp_ldrb_post_h140, disp_ldrb_post_h141, disp_ldrb_post_h142, disp_ldrb_post_h143, disp_ldrb_post_h144, disp_ldrb_post_h145, disp_ldrb_post_h146, disp_ldrb_post_h147, disp_ldrb_post_h148, disp_ldrb_post_h149, disp_ldrb_post_h150, disp_ldrb_post_h151, disp_ldrb_post_h152, disp_ldrb_post_h153, disp_ldrb_post_h154, disp_ldrb_post_h155, disp_ldrb_post_h156, disp_ldrb_post_h157, disp_ldrb_post_h158, disp_ldrb_post_h159, disp_ldrb_post_h160, disp_ldrb_post_h161, disp_ldrb_post_h162, disp_ldrb_post_h163, disp_ldrb_post_h164, disp_ldrb_post_h165, disp_ldrb_post_h166, disp_ldrb_post_h167, disp_ldrb_post_h168, disp_ldrb_post_h169, disp_ldrb_post_h170, disp_ldrb_post_h171, disp_ldrb_post_h172, disp_ldrb_post_h173, disp_ldrb_post_h174, disp_ldrb_post_h175, disp_ldrb_post_h176, disp_ldrb_post_h177, disp_ldrb_post_h178, disp_ldrb_post_h179, disp_ldrb_post_h180, disp_ldrb_post_h181, disp_ldrb_post_h182, disp_ldrb_post_h183, disp_ldrb_post_h184, disp_ldrb_post_h185, disp_ldrb_post_h186, disp_ldrb_post_h187, disp_ldrb_post_h188, disp_ldrb_post_h189, disp_ldrb_post_h190, disp_ldrb_post_h191, disp_ldrb_post_h192, disp_ldrb_post_h193, disp_ldrb_post_h194, disp_ldrb_post_h195, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg5
  try simp (config := {decide := true}) only [disp_ldrb_post_h0, disp_ldrb_post_h1, disp_ldrb_post_h2, disp_ldrb_post_h3, disp_ldrb_post_h4, disp_ldrb_post_h5, disp_ldrb_post_h5b, disp_ldrb_post_h6, disp_ldrb_post_h6b, disp_ldrb_post_h7, disp_ldrb_post_h7b, disp_ldrb_post_h8, disp_ldrb_post_h8b, disp_ldrb_post_h9, disp_ldrb_post_h9b, disp_ldrb_post_h10, disp_ldrb_post_h10b, disp_ldrb_post_h11, disp_ldrb_post_h11b, disp_ldrb_post_h12, disp_ldrb_post_h12b, disp_ldrb_post_h13, disp_ldrb_post_h13b, disp_ldrb_post_h14, disp_ldrb_post_h14b, disp_ldrb_post_h15, disp_ldrb_post_h15b, disp_ldrb_post_h16, disp_ldrb_post_h16b, disp_ldrb_post_h17, disp_ldrb_post_h17b, disp_ldrb_post_h18, disp_ldrb_post_h18b, disp_ldrb_post_h19, disp_ldrb_post_h19b, disp_ldrb_post_h20, disp_ldrb_post_h20b, disp_ldrb_post_h21, disp_ldrb_post_h21b, disp_ldrb_post_h22, disp_ldrb_post_h23, disp_ldrb_post_h24, disp_ldrb_post_h25, disp_ldrb_post_h26, disp_ldrb_post_h27, disp_ldrb_post_h28, disp_ldrb_post_h29, disp_ldrb_post_h30, disp_ldrb_post_h31, disp_ldrb_post_h32, disp_ldrb_post_h33, disp_ldrb_post_h34, disp_ldrb_post_h35, disp_ldrb_post_h36, disp_ldrb_post_h37, disp_ldrb_post_h38, disp_ldrb_post_h39, disp_ldrb_post_h39b, disp_ldrb_post_h40, disp_ldrb_post_h40b, disp_ldrb_post_h41, disp_ldrb_post_h41b, disp_ldrb_post_h42, disp_ldrb_post_h42b, disp_ldrb_post_h43, disp_ldrb_post_h43b, disp_ldrb_post_h44, disp_ldrb_post_h44b, disp_ldrb_post_h45, disp_ldrb_post_h45b, disp_ldrb_post_h46, disp_ldrb_post_h46b, disp_ldrb_post_h47, disp_ldrb_post_h47b, disp_ldrb_post_h48, disp_ldrb_post_h48b, disp_ldrb_post_h49, disp_ldrb_post_h49b, disp_ldrb_post_h50, disp_ldrb_post_h50b, disp_ldrb_post_h51, disp_ldrb_post_h51b, disp_ldrb_post_h52, disp_ldrb_post_h52b, disp_ldrb_post_h53, disp_ldrb_post_h53b, disp_ldrb_post_h54, disp_ldrb_post_h54b, disp_ldrb_post_h55, disp_ldrb_post_h55b, disp_ldrb_post_h56, disp_ldrb_post_h56b, disp_ldrb_post_h57, disp_ldrb_post_h57b, disp_ldrb_post_h58, disp_ldrb_post_h58b, disp_ldrb_post_h59, disp_ldrb_post_h59b, disp_ldrb_post_h60, disp_ldrb_post_h60b, disp_ldrb_post_h61, disp_ldrb_post_h61b, disp_ldrb_post_h62, disp_ldrb_post_h62b, disp_ldrb_post_h63, disp_ldrb_post_h63b, disp_ldrb_post_h64, disp_ldrb_post_h64b, disp_ldrb_post_h65, disp_ldrb_post_h65b, disp_ldrb_post_h66, disp_ldrb_post_h66b, disp_ldrb_post_h67, disp_ldrb_post_h67b, disp_ldrb_post_h68, disp_ldrb_post_h69, disp_ldrb_post_h70, disp_ldrb_post_h71, disp_ldrb_post_h72, disp_ldrb_post_h73, disp_ldrb_post_h74, disp_ldrb_post_h75, disp_ldrb_post_h76, disp_ldrb_post_h77, disp_ldrb_post_h78, disp_ldrb_post_h79, disp_ldrb_post_h80, disp_ldrb_post_h81, disp_ldrb_post_h82, disp_ldrb_post_h83, disp_ldrb_post_h84, disp_ldrb_post_h85, disp_ldrb_post_h86, disp_ldrb_post_h87, disp_ldrb_post_h88, disp_ldrb_post_h89, disp_ldrb_post_h90, disp_ldrb_post_h91, disp_ldrb_post_h92, disp_ldrb_post_h93, disp_ldrb_post_h94, disp_ldrb_post_h95, disp_ldrb_post_h96, disp_ldrb_post_h97, disp_ldrb_post_h98, disp_ldrb_post_h99, disp_ldrb_post_h100, disp_ldrb_post_h101, disp_ldrb_post_h102, disp_ldrb_post_h103, disp_ldrb_post_h104, disp_ldrb_post_h105, disp_ldrb_post_h106, disp_ldrb_post_h107, disp_ldrb_post_h108, disp_ldrb_post_h109, disp_ldrb_post_h110, disp_ldrb_post_h111, disp_ldrb_post_h111b, disp_ldrb_post_h112, disp_ldrb_post_h112b, disp_ldrb_post_h113, disp_ldrb_post_h113b, disp_ldrb_post_h114, disp_ldrb_post_h114b, disp_ldrb_post_h115, disp_ldrb_post_h115b, disp_ldrb_post_h116, disp_ldrb_post_h116b, disp_ldrb_post_h117, disp_ldrb_post_h117b, disp_ldrb_post_h118, disp_ldrb_post_h118b, disp_ldrb_post_h119, disp_ldrb_post_h119b, disp_ldrb_post_h120, disp_ldrb_post_h120b, disp_ldrb_post_h121, disp_ldrb_post_h121b, disp_ldrb_post_h122, disp_ldrb_post_h122b, disp_ldrb_post_h123, disp_ldrb_post_h123b, disp_ldrb_post_h124, disp_ldrb_post_h124b, disp_ldrb_post_h125, disp_ldrb_post_h125b, disp_ldrb_post_h126, disp_ldrb_post_h126b, disp_ldrb_post_h127, disp_ldrb_post_h127b, disp_ldrb_post_h128, disp_ldrb_post_h128b, disp_ldrb_post_h129, disp_ldrb_post_h129b, disp_ldrb_post_h130, disp_ldrb_post_h130b, disp_ldrb_post_h131, disp_ldrb_post_h131b, disp_ldrb_post_h132, disp_ldrb_post_h133, disp_ldrb_post_h134, disp_ldrb_post_h135, disp_ldrb_post_h136, disp_ldrb_post_h137, disp_ldrb_post_h138, disp_ldrb_post_h139, disp_ldrb_post_h140, disp_ldrb_post_h141, disp_ldrb_post_h142, disp_ldrb_post_h143, disp_ldrb_post_h144, disp_ldrb_post_h145, disp_ldrb_post_h146, disp_ldrb_post_h147, disp_ldrb_post_h148, disp_ldrb_post_h149, disp_ldrb_post_h150, disp_ldrb_post_h151, disp_ldrb_post_h152, disp_ldrb_post_h153, disp_ldrb_post_h154, disp_ldrb_post_h155, disp_ldrb_post_h156, disp_ldrb_post_h157, disp_ldrb_post_h158, disp_ldrb_post_h159, disp_ldrb_post_h160, disp_ldrb_post_h161, disp_ldrb_post_h162, disp_ldrb_post_h163, disp_ldrb_post_h164, disp_ldrb_post_h165, disp_ldrb_post_h166, disp_ldrb_post_h167, disp_ldrb_post_h168, disp_ldrb_post_h169, disp_ldrb_post_h170, disp_ldrb_post_h171, disp_ldrb_post_h172, disp_ldrb_post_h173, disp_ldrb_post_h174, disp_ldrb_post_h175, disp_ldrb_post_h176, disp_ldrb_post_h177, disp_ldrb_post_h178, disp_ldrb_post_h179, disp_ldrb_post_h180, disp_ldrb_post_h181, disp_ldrb_post_h182, disp_ldrb_post_h183, disp_ldrb_post_h184, disp_ldrb_post_h185, disp_ldrb_post_h186, disp_ldrb_post_h187, disp_ldrb_post_h188, disp_ldrb_post_h189, disp_ldrb_post_h190, disp_ldrb_post_h191, disp_ldrb_post_h192, disp_ldrb_post_h193, disp_ldrb_post_h194, disp_ldrb_post_h195, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg6
  try simp (config := {decide := true}) only [disp_ldrb_post_h0, disp_ldrb_post_h1, disp_ldrb_post_h2, disp_ldrb_post_h3, disp_ldrb_post_h4, disp_ldrb_post_h5, disp_ldrb_post_h5b, disp_ldrb_post_h6, disp_ldrb_post_h6b, disp_ldrb_post_h7, disp_ldrb_post_h7b, disp_ldrb_post_h8, disp_ldrb_post_h8b, disp_ldrb_post_h9, disp_ldrb_post_h9b, disp_ldrb_post_h10, disp_ldrb_post_h10b, disp_ldrb_post_h11, disp_ldrb_post_h11b, disp_ldrb_post_h12, disp_ldrb_post_h12b, disp_ldrb_post_h13, disp_ldrb_post_h13b, disp_ldrb_post_h14, disp_ldrb_post_h14b, disp_ldrb_post_h15, disp_ldrb_post_h15b, disp_ldrb_post_h16, disp_ldrb_post_h16b, disp_ldrb_post_h17, disp_ldrb_post_h17b, disp_ldrb_post_h18, disp_ldrb_post_h18b, disp_ldrb_post_h19, disp_ldrb_post_h19b, disp_ldrb_post_h20, disp_ldrb_post_h20b, disp_ldrb_post_h21, disp_ldrb_post_h21b, disp_ldrb_post_h22, disp_ldrb_post_h23, disp_ldrb_post_h24, disp_ldrb_post_h25, disp_ldrb_post_h26, disp_ldrb_post_h27, disp_ldrb_post_h28, disp_ldrb_post_h29, disp_ldrb_post_h30, disp_ldrb_post_h31, disp_ldrb_post_h32, disp_ldrb_post_h33, disp_ldrb_post_h34, disp_ldrb_post_h35, disp_ldrb_post_h36, disp_ldrb_post_h37, disp_ldrb_post_h38, disp_ldrb_post_h39, disp_ldrb_post_h39b, disp_ldrb_post_h40, disp_ldrb_post_h40b, disp_ldrb_post_h41, disp_ldrb_post_h41b, disp_ldrb_post_h42, disp_ldrb_post_h42b, disp_ldrb_post_h43, disp_ldrb_post_h43b, disp_ldrb_post_h44, disp_ldrb_post_h44b, disp_ldrb_post_h45, disp_ldrb_post_h45b, disp_ldrb_post_h46, disp_ldrb_post_h46b, disp_ldrb_post_h47, disp_ldrb_post_h47b, disp_ldrb_post_h48, disp_ldrb_post_h48b, disp_ldrb_post_h49, disp_ldrb_post_h49b, disp_ldrb_post_h50, disp_ldrb_post_h50b, disp_ldrb_post_h51, disp_ldrb_post_h51b, disp_ldrb_post_h52, disp_ldrb_post_h52b, disp_ldrb_post_h53, disp_ldrb_post_h53b, disp_ldrb_post_h54, disp_ldrb_post_h54b, disp_ldrb_post_h55, disp_ldrb_post_h55b, disp_ldrb_post_h56, disp_ldrb_post_h56b, disp_ldrb_post_h57, disp_ldrb_post_h57b, disp_ldrb_post_h58, disp_ldrb_post_h58b, disp_ldrb_post_h59, disp_ldrb_post_h59b, disp_ldrb_post_h60, disp_ldrb_post_h60b, disp_ldrb_post_h61, disp_ldrb_post_h61b, disp_ldrb_post_h62, disp_ldrb_post_h62b, disp_ldrb_post_h63, disp_ldrb_post_h63b, disp_ldrb_post_h64, disp_ldrb_post_h64b, disp_ldrb_post_h65, disp_ldrb_post_h65b, disp_ldrb_post_h66, disp_ldrb_post_h66b, disp_ldrb_post_h67, disp_ldrb_post_h67b, disp_ldrb_post_h68, disp_ldrb_post_h69, disp_ldrb_post_h70, disp_ldrb_post_h71, disp_ldrb_post_h72, disp_ldrb_post_h73, disp_ldrb_post_h74, disp_ldrb_post_h75, disp_ldrb_post_h76, disp_ldrb_post_h77, disp_ldrb_post_h78, disp_ldrb_post_h79, disp_ldrb_post_h80, disp_ldrb_post_h81, disp_ldrb_post_h82, disp_ldrb_post_h83, disp_ldrb_post_h84, disp_ldrb_post_h85, disp_ldrb_post_h86, disp_ldrb_post_h87, disp_ldrb_post_h88, disp_ldrb_post_h89, disp_ldrb_post_h90, disp_ldrb_post_h91, disp_ldrb_post_h92, disp_ldrb_post_h93, disp_ldrb_post_h94, disp_ldrb_post_h95, disp_ldrb_post_h96, disp_ldrb_post_h97, disp_ldrb_post_h98, disp_ldrb_post_h99, disp_ldrb_post_h100, disp_ldrb_post_h101, disp_ldrb_post_h102, disp_ldrb_post_h103, disp_ldrb_post_h104, disp_ldrb_post_h105, disp_ldrb_post_h106, disp_ldrb_post_h107, disp_ldrb_post_h108, disp_ldrb_post_h109, disp_ldrb_post_h110, disp_ldrb_post_h111, disp_ldrb_post_h111b, disp_ldrb_post_h112, disp_ldrb_post_h112b, disp_ldrb_post_h113, disp_ldrb_post_h113b, disp_ldrb_post_h114, disp_ldrb_post_h114b, disp_ldrb_post_h115, disp_ldrb_post_h115b, disp_ldrb_post_h116, disp_ldrb_post_h116b, disp_ldrb_post_h117, disp_ldrb_post_h117b, disp_ldrb_post_h118, disp_ldrb_post_h118b, disp_ldrb_post_h119, disp_ldrb_post_h119b, disp_ldrb_post_h120, disp_ldrb_post_h120b, disp_ldrb_post_h121, disp_ldrb_post_h121b, disp_ldrb_post_h122, disp_ldrb_post_h122b, disp_ldrb_post_h123, disp_ldrb_post_h123b, disp_ldrb_post_h124, disp_ldrb_post_h124b, disp_ldrb_post_h125, disp_ldrb_post_h125b, disp_ldrb_post_h126, disp_ldrb_post_h126b, disp_ldrb_post_h127, disp_ldrb_post_h127b, disp_ldrb_post_h128, disp_ldrb_post_h128b, disp_ldrb_post_h129, disp_ldrb_post_h129b, disp_ldrb_post_h130, disp_ldrb_post_h130b, disp_ldrb_post_h131, disp_ldrb_post_h131b, disp_ldrb_post_h132, disp_ldrb_post_h133, disp_ldrb_post_h134, disp_ldrb_post_h135, disp_ldrb_post_h136, disp_ldrb_post_h137, disp_ldrb_post_h138, disp_ldrb_post_h139, disp_ldrb_post_h140, disp_ldrb_post_h141, disp_ldrb_post_h142, disp_ldrb_post_h143, disp_ldrb_post_h144, disp_ldrb_post_h145, disp_ldrb_post_h146, disp_ldrb_post_h147, disp_ldrb_post_h148, disp_ldrb_post_h149, disp_ldrb_post_h150, disp_ldrb_post_h151, disp_ldrb_post_h152, disp_ldrb_post_h153, disp_ldrb_post_h154, disp_ldrb_post_h155, disp_ldrb_post_h156, disp_ldrb_post_h157, disp_ldrb_post_h158, disp_ldrb_post_h159, disp_ldrb_post_h160, disp_ldrb_post_h161, disp_ldrb_post_h162, disp_ldrb_post_h163, disp_ldrb_post_h164, disp_ldrb_post_h165, disp_ldrb_post_h166, disp_ldrb_post_h167, disp_ldrb_post_h168, disp_ldrb_post_h169, disp_ldrb_post_h170, disp_ldrb_post_h171, disp_ldrb_post_h172, disp_ldrb_post_h173, disp_ldrb_post_h174, disp_ldrb_post_h175, disp_ldrb_post_h176, disp_ldrb_post_h177, disp_ldrb_post_h178, disp_ldrb_post_h179, disp_ldrb_post_h180, disp_ldrb_post_h181, disp_ldrb_post_h182, disp_ldrb_post_h183, disp_ldrb_post_h184, disp_ldrb_post_h185, disp_ldrb_post_h186, disp_ldrb_post_h187, disp_ldrb_post_h188, disp_ldrb_post_h189, disp_ldrb_post_h190, disp_ldrb_post_h191, disp_ldrb_post_h192, disp_ldrb_post_h193, disp_ldrb_post_h194, disp_ldrb_post_h195, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg7
  try simp (config := {decide := true}) only [disp_ldrb_post_h0, disp_ldrb_post_h1, disp_ldrb_post_h2, disp_ldrb_post_h3, disp_ldrb_post_h4, disp_ldrb_post_h5, disp_ldrb_post_h5b, disp_ldrb_post_h6, disp_ldrb_post_h6b, disp_ldrb_post_h7, disp_ldrb_post_h7b, disp_ldrb_post_h8, disp_ldrb_post_h8b, disp_ldrb_post_h9, disp_ldrb_post_h9b, disp_ldrb_post_h10, disp_ldrb_post_h10b, disp_ldrb_post_h11, disp_ldrb_post_h11b, disp_ldrb_post_h12, disp_ldrb_post_h12b, disp_ldrb_post_h13, disp_ldrb_post_h13b, disp_ldrb_post_h14, disp_ldrb_post_h14b, disp_ldrb_post_h15, disp_ldrb_post_h15b, disp_ldrb_post_h16, disp_ldrb_post_h16b, disp_ldrb_post_h17, disp_ldrb_post_h17b, disp_ldrb_post_h18, disp_ldrb_post_h18b, disp_ldrb_post_h19, disp_ldrb_post_h19b, disp_ldrb_post_h20, disp_ldrb_post_h20b, disp_ldrb_post_h21, disp_ldrb_post_h21b, disp_ldrb_post_h22, disp_ldrb_post_h23, disp_ldrb_post_h24, disp_ldrb_post_h25, disp_ldrb_post_h26, disp_ldrb_post_h27, disp_ldrb_post_h28, disp_ldrb_post_h29, disp_ldrb_post_h30, disp_ldrb_post_h31, disp_ldrb_post_h32, disp_ldrb_post_h33, disp_ldrb_post_h34, disp_ldrb_post_h35, disp_ldrb_post_h36, disp_ldrb_post_h37, disp_ldrb_post_h38, disp_ldrb_post_h39, disp_ldrb_post_h39b, disp_ldrb_post_h40, disp_ldrb_post_h40b, disp_ldrb_post_h41, disp_ldrb_post_h41b, disp_ldrb_post_h42, disp_ldrb_post_h42b, disp_ldrb_post_h43, disp_ldrb_post_h43b, disp_ldrb_post_h44, disp_ldrb_post_h44b, disp_ldrb_post_h45, disp_ldrb_post_h45b, disp_ldrb_post_h46, disp_ldrb_post_h46b, disp_ldrb_post_h47, disp_ldrb_post_h47b, disp_ldrb_post_h48, disp_ldrb_post_h48b, disp_ldrb_post_h49, disp_ldrb_post_h49b, disp_ldrb_post_h50, disp_ldrb_post_h50b, disp_ldrb_post_h51, disp_ldrb_post_h51b, disp_ldrb_post_h52, disp_ldrb_post_h52b, disp_ldrb_post_h53, disp_ldrb_post_h53b, disp_ldrb_post_h54, disp_ldrb_post_h54b, disp_ldrb_post_h55, disp_ldrb_post_h55b, disp_ldrb_post_h56, disp_ldrb_post_h56b, disp_ldrb_post_h57, disp_ldrb_post_h57b, disp_ldrb_post_h58, disp_ldrb_post_h58b, disp_ldrb_post_h59, disp_ldrb_post_h59b, disp_ldrb_post_h60, disp_ldrb_post_h60b, disp_ldrb_post_h61, disp_ldrb_post_h61b, disp_ldrb_post_h62, disp_ldrb_post_h62b, disp_ldrb_post_h63, disp_ldrb_post_h63b, disp_ldrb_post_h64, disp_ldrb_post_h64b, disp_ldrb_post_h65, disp_ldrb_post_h65b, disp_ldrb_post_h66, disp_ldrb_post_h66b, disp_ldrb_post_h67, disp_ldrb_post_h67b, disp_ldrb_post_h68, disp_ldrb_post_h69, disp_ldrb_post_h70, disp_ldrb_post_h71, disp_ldrb_post_h72, disp_ldrb_post_h73, disp_ldrb_post_h74, disp_ldrb_post_h75, disp_ldrb_post_h76, disp_ldrb_post_h77, disp_ldrb_post_h78, disp_ldrb_post_h79, disp_ldrb_post_h80, disp_ldrb_post_h81, disp_ldrb_post_h82, disp_ldrb_post_h83, disp_ldrb_post_h84, disp_ldrb_post_h85, disp_ldrb_post_h86, disp_ldrb_post_h87, disp_ldrb_post_h88, disp_ldrb_post_h89, disp_ldrb_post_h90, disp_ldrb_post_h91, disp_ldrb_post_h92, disp_ldrb_post_h93, disp_ldrb_post_h94, disp_ldrb_post_h95, disp_ldrb_post_h96, disp_ldrb_post_h97, disp_ldrb_post_h98, disp_ldrb_post_h99, disp_ldrb_post_h100, disp_ldrb_post_h101, disp_ldrb_post_h102, disp_ldrb_post_h103, disp_ldrb_post_h104, disp_ldrb_post_h105, disp_ldrb_post_h106, disp_ldrb_post_h107, disp_ldrb_post_h108, disp_ldrb_post_h109, disp_ldrb_post_h110, disp_ldrb_post_h111, disp_ldrb_post_h111b, disp_ldrb_post_h112, disp_ldrb_post_h112b, disp_ldrb_post_h113, disp_ldrb_post_h113b, disp_ldrb_post_h114, disp_ldrb_post_h114b, disp_ldrb_post_h115, disp_ldrb_post_h115b, disp_ldrb_post_h116, disp_ldrb_post_h116b, disp_ldrb_post_h117, disp_ldrb_post_h117b, disp_ldrb_post_h118, disp_ldrb_post_h118b, disp_ldrb_post_h119, disp_ldrb_post_h119b, disp_ldrb_post_h120, disp_ldrb_post_h120b, disp_ldrb_post_h121, disp_ldrb_post_h121b, disp_ldrb_post_h122, disp_ldrb_post_h122b, disp_ldrb_post_h123, disp_ldrb_post_h123b, disp_ldrb_post_h124, disp_ldrb_post_h124b, disp_ldrb_post_h125, disp_ldrb_post_h125b, disp_ldrb_post_h126, disp_ldrb_post_h126b, disp_ldrb_post_h127, disp_ldrb_post_h127b, disp_ldrb_post_h128, disp_ldrb_post_h128b, disp_ldrb_post_h129, disp_ldrb_post_h129b, disp_ldrb_post_h130, disp_ldrb_post_h130b, disp_ldrb_post_h131, disp_ldrb_post_h131b, disp_ldrb_post_h132, disp_ldrb_post_h133, disp_ldrb_post_h134, disp_ldrb_post_h135, disp_ldrb_post_h136, disp_ldrb_post_h137, disp_ldrb_post_h138, disp_ldrb_post_h139, disp_ldrb_post_h140, disp_ldrb_post_h141, disp_ldrb_post_h142, disp_ldrb_post_h143, disp_ldrb_post_h144, disp_ldrb_post_h145, disp_ldrb_post_h146, disp_ldrb_post_h147, disp_ldrb_post_h148, disp_ldrb_post_h149, disp_ldrb_post_h150, disp_ldrb_post_h151, disp_ldrb_post_h152, disp_ldrb_post_h153, disp_ldrb_post_h154, disp_ldrb_post_h155, disp_ldrb_post_h156, disp_ldrb_post_h157, disp_ldrb_post_h158, disp_ldrb_post_h159, disp_ldrb_post_h160, disp_ldrb_post_h161, disp_ldrb_post_h162, disp_ldrb_post_h163, disp_ldrb_post_h164, disp_ldrb_post_h165, disp_ldrb_post_h166, disp_ldrb_post_h167, disp_ldrb_post_h168, disp_ldrb_post_h169, disp_ldrb_post_h170, disp_ldrb_post_h171, disp_ldrb_post_h172, disp_ldrb_post_h173, disp_ldrb_post_h174, disp_ldrb_post_h175, disp_ldrb_post_h176, disp_ldrb_post_h177, disp_ldrb_post_h178, disp_ldrb_post_h179, disp_ldrb_post_h180, disp_ldrb_post_h181, disp_ldrb_post_h182, disp_ldrb_post_h183, disp_ldrb_post_h184, disp_ldrb_post_h185, disp_ldrb_post_h186, disp_ldrb_post_h187, disp_ldrb_post_h188, disp_ldrb_post_h189, disp_ldrb_post_h190, disp_ldrb_post_h191, disp_ldrb_post_h192, disp_ldrb_post_h193, disp_ldrb_post_h194, disp_ldrb_post_h195, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg8
  try simp (config := {decide := true}) only [disp_ldrb_post_h0, disp_ldrb_post_h1, disp_ldrb_post_h2, disp_ldrb_post_h3, disp_ldrb_post_h4, disp_ldrb_post_h5, disp_ldrb_post_h5b, disp_ldrb_post_h6, disp_ldrb_post_h6b, disp_ldrb_post_h7, disp_ldrb_post_h7b, disp_ldrb_post_h8, disp_ldrb_post_h8b, disp_ldrb_post_h9, disp_ldrb_post_h9b, disp_ldrb_post_h10, disp_ldrb_post_h10b, disp_ldrb_post_h11, disp_ldrb_post_h11b, disp_ldrb_post_h12, disp_ldrb_post_h12b, disp_ldrb_post_h13, disp_ldrb_post_h13b, disp_ldrb_post_h14, disp_ldrb_post_h14b, disp_ldrb_post_h15, disp_ldrb_post_h15b, disp_ldrb_post_h16, disp_ldrb_post_h16b, disp_ldrb_post_h17, disp_ldrb_post_h17b, disp_ldrb_post_h18, disp_ldrb_post_h18b, disp_ldrb_post_h19, disp_ldrb_post_h19b, disp_ldrb_post_h20, disp_ldrb_post_h20b, disp_ldrb_post_h21, disp_ldrb_post_h21b, disp_ldrb_post_h22, disp_ldrb_post_h23, disp_ldrb_post_h24, disp_ldrb_post_h25, disp_ldrb_post_h26, disp_ldrb_post_h27, disp_ldrb_post_h28, disp_ldrb_post_h29, disp_ldrb_post_h30, disp_ldrb_post_h31, disp_ldrb_post_h32, disp_ldrb_post_h33, disp_ldrb_post_h34, disp_ldrb_post_h35, disp_ldrb_post_h36, disp_ldrb_post_h37, disp_ldrb_post_h38, disp_ldrb_post_h39, disp_ldrb_post_h39b, disp_ldrb_post_h40, disp_ldrb_post_h40b, disp_ldrb_post_h41, disp_ldrb_post_h41b, disp_ldrb_post_h42, disp_ldrb_post_h42b, disp_ldrb_post_h43, disp_ldrb_post_h43b, disp_ldrb_post_h44, disp_ldrb_post_h44b, disp_ldrb_post_h45, disp_ldrb_post_h45b, disp_ldrb_post_h46, disp_ldrb_post_h46b, disp_ldrb_post_h47, disp_ldrb_post_h47b, disp_ldrb_post_h48, disp_ldrb_post_h48b, disp_ldrb_post_h49, disp_ldrb_post_h49b, disp_ldrb_post_h50, disp_ldrb_post_h50b, disp_ldrb_post_h51, disp_ldrb_post_h51b, disp_ldrb_post_h52, disp_ldrb_post_h52b, disp_ldrb_post_h53, disp_ldrb_post_h53b, disp_ldrb_post_h54, disp_ldrb_post_h54b, disp_ldrb_post_h55, disp_ldrb_post_h55b, disp_ldrb_post_h56, disp_ldrb_post_h56b, disp_ldrb_post_h57, disp_ldrb_post_h57b, disp_ldrb_post_h58, disp_ldrb_post_h58b, disp_ldrb_post_h59, disp_ldrb_post_h59b, disp_ldrb_post_h60, disp_ldrb_post_h60b, disp_ldrb_post_h61, disp_ldrb_post_h61b, disp_ldrb_post_h62, disp_ldrb_post_h62b, disp_ldrb_post_h63, disp_ldrb_post_h63b, disp_ldrb_post_h64, disp_ldrb_post_h64b, disp_ldrb_post_h65, disp_ldrb_post_h65b, disp_ldrb_post_h66, disp_ldrb_post_h66b, disp_ldrb_post_h67, disp_ldrb_post_h67b, disp_ldrb_post_h68, disp_ldrb_post_h69, disp_ldrb_post_h70, disp_ldrb_post_h71, disp_ldrb_post_h72, disp_ldrb_post_h73, disp_ldrb_post_h74, disp_ldrb_post_h75, disp_ldrb_post_h76, disp_ldrb_post_h77, disp_ldrb_post_h78, disp_ldrb_post_h79, disp_ldrb_post_h80, disp_ldrb_post_h81, disp_ldrb_post_h82, disp_ldrb_post_h83, disp_ldrb_post_h84, disp_ldrb_post_h85, disp_ldrb_post_h86, disp_ldrb_post_h87, disp_ldrb_post_h88, disp_ldrb_post_h89, disp_ldrb_post_h90, disp_ldrb_post_h91, disp_ldrb_post_h92, disp_ldrb_post_h93, disp_ldrb_post_h94, disp_ldrb_post_h95, disp_ldrb_post_h96, disp_ldrb_post_h97, disp_ldrb_post_h98, disp_ldrb_post_h99, disp_ldrb_post_h100, disp_ldrb_post_h101, disp_ldrb_post_h102, disp_ldrb_post_h103, disp_ldrb_post_h104, disp_ldrb_post_h105, disp_ldrb_post_h106, disp_ldrb_post_h107, disp_ldrb_post_h108, disp_ldrb_post_h109, disp_ldrb_post_h110, disp_ldrb_post_h111, disp_ldrb_post_h111b, disp_ldrb_post_h112, disp_ldrb_post_h112b, disp_ldrb_post_h113, disp_ldrb_post_h113b, disp_ldrb_post_h114, disp_ldrb_post_h114b, disp_ldrb_post_h115, disp_ldrb_post_h115b, disp_ldrb_post_h116, disp_ldrb_post_h116b, disp_ldrb_post_h117, disp_ldrb_post_h117b, disp_ldrb_post_h118, disp_ldrb_post_h118b, disp_ldrb_post_h119, disp_ldrb_post_h119b, disp_ldrb_post_h120, disp_ldrb_post_h120b, disp_ldrb_post_h121, disp_ldrb_post_h121b, disp_ldrb_post_h122, disp_ldrb_post_h122b, disp_ldrb_post_h123, disp_ldrb_post_h123b, disp_ldrb_post_h124, disp_ldrb_post_h124b, disp_ldrb_post_h125, disp_ldrb_post_h125b, disp_ldrb_post_h126, disp_ldrb_post_h126b, disp_ldrb_post_h127, disp_ldrb_post_h127b, disp_ldrb_post_h128, disp_ldrb_post_h128b, disp_ldrb_post_h129, disp_ldrb_post_h129b, disp_ldrb_post_h130, disp_ldrb_post_h130b, disp_ldrb_post_h131, disp_ldrb_post_h131b, disp_ldrb_post_h132, disp_ldrb_post_h133, disp_ldrb_post_h134, disp_ldrb_post_h135, disp_ldrb_post_h136, disp_ldrb_post_h137, disp_ldrb_post_h138, disp_ldrb_post_h139, disp_ldrb_post_h140, disp_ldrb_post_h141, disp_ldrb_post_h142, disp_ldrb_post_h143, disp_ldrb_post_h144, disp_ldrb_post_h145, disp_ldrb_post_h146, disp_ldrb_post_h147, disp_ldrb_post_h148, disp_ldrb_post_h149, disp_ldrb_post_h150, disp_ldrb_post_h151, disp_ldrb_post_h152, disp_ldrb_post_h153, disp_ldrb_post_h154, disp_ldrb_post_h155, disp_ldrb_post_h156, disp_ldrb_post_h157, disp_ldrb_post_h158, disp_ldrb_post_h159, disp_ldrb_post_h160, disp_ldrb_post_h161, disp_ldrb_post_h162, disp_ldrb_post_h163, disp_ldrb_post_h164, disp_ldrb_post_h165, disp_ldrb_post_h166, disp_ldrb_post_h167, disp_ldrb_post_h168, disp_ldrb_post_h169, disp_ldrb_post_h170, disp_ldrb_post_h171, disp_ldrb_post_h172, disp_ldrb_post_h173, disp_ldrb_post_h174, disp_ldrb_post_h175, disp_ldrb_post_h176, disp_ldrb_post_h177, disp_ldrb_post_h178, disp_ldrb_post_h179, disp_ldrb_post_h180, disp_ldrb_post_h181, disp_ldrb_post_h182, disp_ldrb_post_h183, disp_ldrb_post_h184, disp_ldrb_post_h185, disp_ldrb_post_h186, disp_ldrb_post_h187, disp_ldrb_post_h188, disp_ldrb_post_h189, disp_ldrb_post_h190, disp_ldrb_post_h191, disp_ldrb_post_h192, disp_ldrb_post_h193, disp_ldrb_post_h194, disp_ldrb_post_h195, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

  -- crux workspace addition: the segmented LoadStore decoder leaves a Bool-continuation bind; fold it.
  congr 1
  funext x
  split
  · simp only [bind_assoc, pure_bind, Bool.false_eq_true, ite_false, bind_pure_unit]
  · simp only [pure_bind, ite_true]

#print axioms disp_ldrb_post
end ArmCertMem.Disp
