import NativeEntryBodyDispatch.Tbnz32Word
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.CruxCore
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace NativeEntryBodyDispatch.Tbnz32
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 23 11) : BitVec 13) = 993#13) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h0b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 23 11) : BitVec 13) == 993#13) = false := by
  have := dispatch_h0 imm14 Rt
  simpa using this

theorem dispatch_h1 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 23 11) : BitVec 13) = 2017#13) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h1b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 23 11) : BitVec 13) == 2017#13) = false := by
  have := dispatch_h1 imm14 Rt
  simpa using this

theorem dispatch_h2 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 25 25) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h3 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 27 25) : BitVec 3) = 3#3 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h4 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 27 27) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h5 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 28 25) : BitVec 4) = 11#4 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h6 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 28 25) : BitVec 4) = 11#4 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h7 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 28 25) : BitVec 4) = 11#4 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h8 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 28 25) : BitVec 4) = 11#4 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h9 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 28 26) : BitVec 3) = 5#3 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h10 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 28 26) : BitVec 3) = 5#3 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h11 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 30 24) : BitVec 7) = 55#7 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h12 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 30 24) : BitVec 7) = 55#7 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h13 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 30 24) : BitVec 7) = 55#7 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h14 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 30 24) : BitVec 7) = 55#7 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h15 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 5) : BitVec 27) = 111679616#27) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 20) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h15b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 5) : BitVec 27) == 111679616#27) = false := by
  have := dispatch_h15 imm14 Rt
  simpa using this

theorem dispatch_h16 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 5) : BitVec 27) = 111679617#27) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 20) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h16b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 5) : BitVec 27) == 111679617#27) = false := by
  have := dispatch_h16 imm14 Rt
  simpa using this

theorem dispatch_h17 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 5) : BitVec 27) = 111745411#27) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 16) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h17b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 5) : BitVec 27) == 111745411#27) = false := by
  have := dispatch_h17 imm14 Rt
  simpa using this

theorem dispatch_h18 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 5) : BitVec 27) = 111745419#27) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 16) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h18b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 5) : BitVec 27) == 111745419#27) = false := by
  have := dispatch_h18 imm14 Rt
  simpa using this

theorem dispatch_h19 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 8) : BitVec 24) = 13959972#24) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 17) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h19b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 8) : BitVec 24) == 13959972#24) = false := by
  have := dispatch_h19 imm14 Rt
  simpa using this

theorem dispatch_h20 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 10) : BitVec 22) = 3489992#22) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 15) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h20b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 10) : BitVec 22) == 3489992#22) = false := by
  have := dispatch_h20 imm14 Rt
  simpa using this

theorem dispatch_h21 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 10) : BitVec 22) = 3508160#22) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h21b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 10) : BitVec 22) == 3508160#22) = false := by
  have := dispatch_h21 imm14 Rt
  simpa using this

theorem dispatch_h22 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 10) : BitVec 22) = 3510208#22) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h22b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 10) : BitVec 22) == 3510208#22) = false := by
  have := dispatch_h22 imm14 Rt
  simpa using this

theorem dispatch_h23 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 10) : BitVec 22) = 3512256#22) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h23b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 10) : BitVec 22) == 3512256#22) = false := by
  have := dispatch_h23 imm14 Rt
  simpa using this

theorem dispatch_h24 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 11) : BitVec 21) = 1756129#21) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h24b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 11) : BitVec 21) == 1756129#21) = false := by
  have := dispatch_h24 imm14 Rt
  simpa using this

theorem dispatch_h25 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 11) : BitVec 21) = 1758177#21) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h25b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 11) : BitVec 21) == 1758177#21) = false := by
  have := dispatch_h25 imm14 Rt
  simpa using this

theorem dispatch_h26 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 12) : BitVec 20) = 872498#20) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h26b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 12) : BitVec 20) == 872498#20) = false := by
  have := dispatch_h26 imm14 Rt
  simpa using this

theorem dispatch_h27 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 12) : BitVec 20) = 872499#20) := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h27b (imm14 : BitVec 14) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 12) : BitVec 20) == 872499#20) = false := by
  have := dispatch_h27 imm14 Rt
  simpa using this

theorem dispatch_h28 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 19) : BitVec 13) = 1760#13 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h29 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 19) : BitVec 13) = 1760#13 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h30 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 19) : BitVec 13) = 1760#13 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h31 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 19) : BitVec 13) = 1760#13 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h32 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 20) : BitVec 12) = 880#12 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h33 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 20) : BitVec 12) = 880#12 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h34 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 20) : BitVec 12) = 880#12 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h35 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 20) : BitVec 12) = 880#12 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h36 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 21) : BitVec 11) = 440#11 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h37 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 21) : BitVec 11) = 440#11 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h38 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 21) : BitVec 11) = 440#11 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h39 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 21) : BitVec 11) = 440#11 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h40 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 21) : BitVec 11) = 440#11 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h41 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 24) : BitVec 8) = 55#8 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h42 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 25) : BitVec 7) = 27#7 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h43 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 26) : BitVec 6) = 13#6 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h44 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 26) : BitVec 6) = 13#6 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h45 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 31) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h46 (imm14 : BitVec 14) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 31) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h47 (imm14 : BitVec 14) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 0 5 = Rt := by
    unfold NativeEntryBodyDispatch.Tbnz32.word BitVec.slice
    bv_field

theorem dispatch_h48 (imm14 : BitVec 14) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 5 14 = imm14 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word BitVec.slice
    bv_field

theorem dispatch_h49 (imm14 : BitVec 14) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 19 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h50 (imm14 : BitVec 14) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 19 5 = 0#5 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h51 (imm14 : BitVec 14) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 21 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h52 (imm14 : BitVec 14) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 21 2 = 0#2 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h53 (imm14 : BitVec 14) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 24 1 = 1#1 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h54 (imm14 : BitVec 14) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) 31 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.Tbnz32.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_hw55 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573563423#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw56 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573563455#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw57 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573563487#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw58 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573751839#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw59 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573751871#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw60 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573751903#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw61 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573751935#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw62 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573751967#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw63 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573751999#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw64 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573752031#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw65 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573752063#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw66 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573752351#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw67 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573752383#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw68 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573752415#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw69 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573752447#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw70 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573752479#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw71 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573752543#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw72 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573753119#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw73 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573756031#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw74 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3573756159#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw75 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3600745440#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 19) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_hw76 (imm14 : BitVec 14) (Rt : BitVec 5) :
    ¬ ((NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = 3602842592#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 19) h
    unfold NativeEntryBodyDispatch.Tbnz32.word at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch (pc : Int) (imm14 : BitVec 14) (Rt : BitVec 5) :
    __DecodeA64 (real := real) pc (NativeEntryBodyDispatch.Tbnz32.word 0#1 27#6 1#1 0#5 imm14 Rt) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 1009))
      if c = true then (do writeReg Register.SEE 1009; decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 0#5 1#1 0#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_hw55, dispatch_hw56, dispatch_hw57, dispatch_hw58, dispatch_hw59, dispatch_hw60, dispatch_hw61, dispatch_hw62, dispatch_hw63, dispatch_hw64, dispatch_hw65, dispatch_hw66, dispatch_hw67, dispatch_hw68, dispatch_hw69, dispatch_hw70, dispatch_hw71, dispatch_hw72, dispatch_hw73, dispatch_hw74, dispatch_hw75, dispatch_hw76, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_BranchExcSys
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h14, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h29, dispatch_h30, dispatch_h31, dispatch_h32, dispatch_h33, dispatch_h34, dispatch_h35, dispatch_h36, dispatch_h37, dispatch_h38, dispatch_h39, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_h46, dispatch_h47, dispatch_h48, dispatch_h49, dispatch_h50, dispatch_h51, dispatch_h52, dispatch_h53, dispatch_h54, dispatch_hw55, dispatch_hw56, dispatch_hw57, dispatch_hw58, dispatch_hw59, dispatch_hw60, dispatch_hw61, dispatch_hw62, dispatch_hw63, dispatch_hw64, dispatch_hw65, dispatch_hw66, dispatch_hw67, dispatch_hw68, dispatch_hw69, dispatch_hw70, dispatch_hw71, dispatch_hw72, dispatch_hw73, dispatch_hw74, dispatch_hw75, dispatch_hw76, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch

/- Internal actual-state selector. The canonical prelude/owner frame must derive
this SEE bound; it is not a public entry premise or a discarded fallback. -/
theorem dispatch_at (pc : Int) (Rt : BitVec 5) (imm14 : BitVec 14) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 1009) :
    (__DecodeA64 (real := real) pc (NativeEntryBodyDispatch.Tbnz32.selected Rt imm14) : SailM Unit) s =
      (do writeReg Register.SEE 1009; decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 0#5 1#1 0#1 : SailM Unit) s := by
  rw [NativeEntryBodyDispatch.Tbnz32.selected, dispatch real pc imm14 Rt]
  have h : (s.regs.bank_Int .SEE <b 1009) = true := by simpa using see
  have read : ((do let x ← readReg Register.SEE; pure (x <b 1009)) : SailM Bool) s =
      .ok (s.regs.bank_Int .SEE <b 1009) s := by rfl
  rw [ArmBridge.CruxCore.bind_app, read]
  dsimp only []
  rw [if_pos h]

#print axioms dispatch_at
end NativeEntryBodyDispatch.Tbnz32
