import NativeEntryBodyDispatch.SubsImm32Word
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.CruxCore
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace NativeEntryBodyDispatch.SubsImm32
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 25 25) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h1 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 27 25) : BitVec 3) = 0#3 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h2 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 27 27) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h3 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 28 24) : BitVec 5) = 17#5 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h4 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 28 25) : BitVec 4) = 8#4 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h5 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 28 25) : BitVec 4) = 8#4 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h6 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 28 25) : BitVec 4) = 8#4 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h7 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 28 25) : BitVec 4) = 8#4 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h8 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 28 26) : BitVec 3) = 4#3 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h9 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 28 26) : BitVec 3) = 4#3 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h10 (imm12 : BitVec 12) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 18) : BitVec 13) = 1136#13) := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h10b (imm12 : BitVec 12) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 18) : BitVec 13) == 1136#13) = false := by
  have := dispatch_h10 imm12 Rn
  simpa using this

theorem dispatch_h11 (imm12 : BitVec 12) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 18) : BitVec 13) = 1137#13) := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h11b (imm12 : BitVec 12) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 18) : BitVec 13) == 1137#13) = false := by
  have := dispatch_h11 imm12 Rn
  simpa using this

theorem dispatch_h12 (imm12 : BitVec 12) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 18) : BitVec 13) = 1138#13) := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h12b (imm12 : BitVec 12) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 18) : BitVec 13) == 1138#13) = false := by
  have := dispatch_h12 imm12 Rn
  simpa using this

theorem dispatch_h13 (imm12 : BitVec 12) (Rn : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 18) : BitVec 13) = 1139#13) := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 4) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h13b (imm12 : BitVec 12) (Rn : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 18) : BitVec 13) == 1139#13) = false := by
  have := dispatch_h13 imm12 Rn
  simpa using this

theorem dispatch_h14 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h15 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h16 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h17 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h18 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h19 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h20 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h21 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h22 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h23 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h24 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h25 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h26 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h27 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h28 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 23) : BitVec 8) = 226#8 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h29 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 31 22) : BitVec 10) = 452#10 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h30 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 31 22) : BitVec 10) = 452#10 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h31 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 31 31) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h32 (imm12 : BitVec 12) (Rn : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 31 31) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h33 (imm12 : BitVec 12) (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 0 5 = 31#5 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h34 (imm12 : BitVec 12) (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 5 5 = Rn := by
    unfold NativeEntryBodyDispatch.SubsImm32.word BitVec.slice
    bv_field

theorem dispatch_h35 (imm12 : BitVec 12) (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 10 12 = imm12 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word BitVec.slice
    bv_field

theorem dispatch_h36 (imm12 : BitVec 12) (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 22 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h37 (imm12 : BitVec 12) (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 29 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h38 (imm12 : BitVec 12) (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 29 2 = 3#2 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h39 (imm12 : BitVec 12) (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 30 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h40 (imm12 : BitVec 12) (Rn : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) 31 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.SubsImm32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch (pc : Int) (imm12 : BitVec 12) (Rn : BitVec 5) :
    __DecodeA64 (real := real) pc (NativeEntryBodyDispatch.SubsImm32.word 0#1 1#1 1#1 34#6 0#1 imm12 Rn 31#5) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 21))
      if c = true then (do writeReg Register.SEE 21; decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 0#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_DataProcImm
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h1, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h15, dispatch_h16, dispatch_h17, dispatch_h18, dispatch_h19, dispatch_h20, dispatch_h21, dispatch_h22, dispatch_h23, dispatch_h24, dispatch_h25, dispatch_h26, dispatch_h27, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch

/- Internal actual-state selector. The canonical prelude/owner frame must derive
this SEE bound; it is not a public entry premise or a discarded fallback. -/
theorem dispatch_at (pc : Int) (Rn : BitVec 5) (imm12 : BitVec 12) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 21) :
    (__DecodeA64 (real := real) pc (NativeEntryBodyDispatch.SubsImm32.selected Rn imm12) : SailM Unit) s =
      (do writeReg Register.SEE 21; decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate 31#5 Rn imm12 0#1 1#1 1#1 0#1 : SailM Unit) s := by
  rw [NativeEntryBodyDispatch.SubsImm32.selected, dispatch real pc imm12 Rn]
  have h : (s.regs.bank_Int .SEE <b 21) = true := by simpa using see
  have read : ((do let x ← readReg Register.SEE; pure (x <b 21)) : SailM Bool) s =
      .ok (s.regs.bank_Int .SEE <b 21) s := by rfl
  rw [ArmBridge.CruxCore.bind_app, read]
  dsimp only []
  rw [if_pos h]

#print axioms dispatch_at
end NativeEntryBodyDispatch.SubsImm32
