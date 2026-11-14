import NativeEntryBodyDispatch.StrWUoffWord
import ArmFull.Fn.M1475
import Bridge.Awc
import Bridge.CruxCore
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace NativeEntryBodyDispatch.StrWUoff
variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 22 21) : BitVec 2) = 2#2) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h0b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 22 21) : BitVec 2) == 2#2) = false := by
  have := dispatch_h0 imm12 Rn Rt
  simpa using this

theorem dispatch_h1 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 22 21) : BitVec 2) = 3#2) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h1b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 22 21) : BitVec 2) == 3#2) = false := by
  have := dispatch_h1 imm12 Rn Rt
  simpa using this

theorem dispatch_h2 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 22 22) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h3 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 22 22) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h4 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 25 25) : BitVec 1) = 0#1 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h5 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 27 25) : BitVec 3) = 4#3 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h6 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 27 27) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h7 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h8 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h9 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h10 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 28 25) : BitVec 4) = 12#4 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h <;> subst h <;> simp

theorem dispatch_h11 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 28 26) : BitVec 3) = 6#3 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h12 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 28 26) : BitVec 3) = 6#3 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h13 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) = 137183#20) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h13b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) == 137183#20) = false := by
  have := dispatch_h13 imm12 Rn Rt
  simpa using this

theorem dispatch_h14 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) = 137215#20) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h14b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) == 137215#20) = false := by
  have := dispatch_h14 imm12 Rn Rt
  simpa using this

theorem dispatch_h15 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) = 141279#20) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h15b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) == 141279#20) = false := by
  have := dispatch_h15 imm12 Rn Rt
  simpa using this

theorem dispatch_h16 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) = 141311#20) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h16b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) == 141311#20) = false := by
  have := dispatch_h16 imm12 Rn Rt
  simpa using this

theorem dispatch_h17 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) = 145375#20) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h17b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) == 145375#20) = false := by
  have := dispatch_h17 imm12 Rn Rt
  simpa using this

theorem dispatch_h18 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) = 145407#20) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h18b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) == 145407#20) = false := by
  have := dispatch_h18 imm12 Rn Rt
  simpa using this

theorem dispatch_h19 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) = 213089#20) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 16) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h19b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) == 213089#20) = false := by
  have := dispatch_h19 imm12 Rn Rt
  simpa using this

theorem dispatch_h20 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) = 217185#20) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h20b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) == 217185#20) = false := by
  have := dispatch_h20 imm12 Rn Rt
  simpa using this

theorem dispatch_h21 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) = 417794#20) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h21b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) == 417794#20) = false := by
  have := dispatch_h21 imm12 Rn Rt
  simpa using this

theorem dispatch_h22 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) = 421890#20) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h22b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) == 421890#20) = false := by
  have := dispatch_h22 imm12 Rn Rt
  simpa using this

theorem dispatch_h23 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) = 929776#20) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h23b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 10) : BitVec 20) == 929776#20) = false := by
  have := dispatch_h23 imm12 Rn Rt
  simpa using this

theorem dispatch_h24 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) = 49152#18) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h24b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) == 49152#18) = false := by
  have := dispatch_h24 imm12 Rn Rt
  simpa using this

theorem dispatch_h25 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) = 49156#18) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h25b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) == 49156#18) = false := by
  have := dispatch_h25 imm12 Rn Rt
  simpa using this

theorem dispatch_h26 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) = 49160#18) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h26b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) == 49160#18) = false := by
  have := dispatch_h26 imm12 Rn Rt
  simpa using this

theorem dispatch_h27 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) = 50176#18) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h27b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) == 50176#18) = false := by
  have := dispatch_h27 imm12 Rn Rt
  simpa using this

theorem dispatch_h28 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) = 50180#18) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h28b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) == 50180#18) = false := by
  have := dispatch_h28 imm12 Rn Rt
  simpa using this

theorem dispatch_h29 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) = 50184#18) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h29b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) == 50184#18) = false := by
  have := dispatch_h29 imm12 Rn Rt
  simpa using this

theorem dispatch_h30 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) = 54284#18) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h30b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) == 54284#18) = false := by
  have := dispatch_h30 imm12 Rn Rt
  simpa using this

theorem dispatch_h31 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) = 54286#18) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h31b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) == 54286#18) = false := by
  have := dispatch_h31 imm12 Rn Rt
  simpa using this

theorem dispatch_h32 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) = 54796#18) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h32b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) == 54796#18) = false := by
  have := dispatch_h32 imm12 Rn Rt
  simpa using this

theorem dispatch_h33 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) = 54798#18) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h33b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 12) : BitVec 18) == 54798#18) = false := by
  have := dispatch_h33 imm12 Rn Rt
  simpa using this

theorem dispatch_h34 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 15) : BitVec 15) = 4350#15) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h34b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 15) : BitVec 15) == 4350#15) = false := by
  have := dispatch_h34 imm12 Rn Rt
  simpa using this

theorem dispatch_h35 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 15) : BitVec 15) = 4351#15) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 7) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h35b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 15) : BitVec 15) == 4351#15) = false := by
  have := dispatch_h35 imm12 Rn Rt
  simpa using this

theorem dispatch_h36 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) = 3072#14) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h36b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) == 3072#14) = false := by
  have := dispatch_h36 imm12 Rn Rt
  simpa using this

theorem dispatch_h37 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) = 3136#14) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h37b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) == 3136#14) = false := by
  have := dispatch_h37 imm12 Rn Rt
  simpa using this

theorem dispatch_h38 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) = 3328#14) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h38b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) == 3328#14) = false := by
  have := dispatch_h38 imm12 Rn Rt
  simpa using this

theorem dispatch_h39 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) = 3360#14) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h39b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) == 3360#14) = false := by
  have := dispatch_h39 imm12 Rn Rt
  simpa using this

theorem dispatch_h40 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) = 3392#14) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h40b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) == 3392#14) = false := by
  have := dispatch_h40 imm12 Rn Rt
  simpa using this

theorem dispatch_h41 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) = 3424#14) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h41b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 16) : BitVec 14) == 3424#14) = false := by
  have := dispatch_h41 imm12 Rn Rt
  simpa using this

theorem dispatch_h42 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 64#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h42b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 64#9) = false := by
  have := dispatch_h42 imm12 Rn Rt
  simpa using this

theorem dispatch_h43 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 65#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h43b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 65#9) = false := by
  have := dispatch_h43 imm12 Rn Rt
  simpa using this

theorem dispatch_h44 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 100#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h44b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 100#9) = false := by
  have := dispatch_h44 imm12 Rn Rt
  simpa using this

theorem dispatch_h45 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 102#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h45b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 102#9) = false := by
  have := dispatch_h45 imm12 Rn Rt
  simpa using this

theorem dispatch_h46 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 108#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h46b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 108#9) = false := by
  have := dispatch_h46 imm12 Rn Rt
  simpa using this

theorem dispatch_h47 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 109#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h47b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 109#9) = false := by
  have := dispatch_h47 imm12 Rn Rt
  simpa using this

theorem dispatch_h48 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 110#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h48b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 110#9) = false := by
  have := dispatch_h48 imm12 Rn Rt
  simpa using this

theorem dispatch_h49 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 111#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h49b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 111#9) = false := by
  have := dispatch_h49 imm12 Rn Rt
  simpa using this

theorem dispatch_h50 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 200#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h50b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 200#9) = false := by
  have := dispatch_h50 imm12 Rn Rt
  simpa using this

theorem dispatch_h51 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 202#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h51b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 202#9) = false := by
  have := dispatch_h51 imm12 Rn Rt
  simpa using this

theorem dispatch_h52 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 448#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h52b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 448#9) = false := by
  have := dispatch_h52 imm12 Rn Rt
  simpa using this

theorem dispatch_h53 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 449#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h53b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 449#9) = false := by
  have := dispatch_h53 imm12 Rn Rt
  simpa using this

theorem dispatch_h54 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 450#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h54b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 450#9) = false := by
  have := dispatch_h54 imm12 Rn Rt
  simpa using this

theorem dispatch_h55 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) = 451#9) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h55b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 21) : BitVec 9) == 451#9) = false := by
  have := dispatch_h55 imm12 Rn Rt
  simpa using this

theorem dispatch_h56 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 22) : BitVec 8) = 228#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h57 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 22) : BitVec 8) = 228#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h58 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 22) : BitVec 8) = 228#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h59 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 22) : BitVec 8) = 228#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h60 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 22) : BitVec 8) = 228#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h61 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 22) : BitVec 8) = 228#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h62 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 22) : BitVec 8) = 228#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h63 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 22) : BitVec 8) = 228#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h64 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 22) : BitVec 8) = 228#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h65 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 22) : BitVec 8) = 228#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h66 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 23) : BitVec 7) = 114#7 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h67 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 23) : BitVec 7) = 114#7 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h68 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 24) : BitVec 6) = 57#6 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h69 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 24) : BitVec 6) = 57#6 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h70 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 24) : BitVec 6) = 57#6 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h71 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 24) : BitVec 6) = 57#6 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h72 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 24) : BitVec 6) = 57#6 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h73 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 24) : BitVec 6) = 57#6 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h74 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 29 24) : BitVec 6) = 57#6 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h75 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 30 22) : BitVec 9) = 228#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h76 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 30 22) : BitVec 9) = 228#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h77 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 30 22) : BitVec 9) = 228#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h78 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 30 22) : BitVec 9) = 228#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h79 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 30 22) : BitVec 9) = 228#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h80 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 30 22) : BitVec 9) = 228#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h81 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 30 22) : BitVec 9) = 228#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h82 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 30 22) : BitVec 9) = 228#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h83 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 137183#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h83b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 137183#22) = false := by
  have := dispatch_h83 imm12 Rn Rt
  simpa using this

theorem dispatch_h84 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 137215#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h84b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 137215#22) = false := by
  have := dispatch_h84 imm12 Rn Rt
  simpa using this

theorem dispatch_h85 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 141279#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h85b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 141279#22) = false := by
  have := dispatch_h85 imm12 Rn Rt
  simpa using this

theorem dispatch_h86 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 141311#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h86b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 141311#22) = false := by
  have := dispatch_h86 imm12 Rn Rt
  simpa using this

theorem dispatch_h87 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 145375#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h87b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 145375#22) = false := by
  have := dispatch_h87 imm12 Rn Rt
  simpa using this

theorem dispatch_h88 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 145407#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h88b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 145407#22) = false := by
  have := dispatch_h88 imm12 Rn Rt
  simpa using this

theorem dispatch_h89 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 929776#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h89b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 929776#22) = false := by
  have := dispatch_h89 imm12 Rn Rt
  simpa using this

theorem dispatch_h90 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 1185759#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h90b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 1185759#22) = false := by
  have := dispatch_h90 imm12 Rn Rt
  simpa using this

theorem dispatch_h91 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 1185791#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h91b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 1185791#22) = false := by
  have := dispatch_h91 imm12 Rn Rt
  simpa using this

theorem dispatch_h92 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 1189855#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h92b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 1189855#22) = false := by
  have := dispatch_h92 imm12 Rn Rt
  simpa using this

theorem dispatch_h93 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 1189887#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h93b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 1189887#22) = false := by
  have := dispatch_h93 imm12 Rn Rt
  simpa using this

theorem dispatch_h94 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 1193951#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h94b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 1193951#22) = false := by
  have := dispatch_h94 imm12 Rn Rt
  simpa using this

theorem dispatch_h95 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 1193983#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h95b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 1193983#22) = false := by
  have := dispatch_h95 imm12 Rn Rt
  simpa using this

theorem dispatch_h96 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 1978352#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 13) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h96b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 1978352#22) = false := by
  have := dispatch_h96 imm12 Rn Rt
  simpa using this

theorem dispatch_h97 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 3557315#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 19) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h97b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 3557315#22) = false := by
  have := dispatch_h97 imm12 Rn Rt
  simpa using this

theorem dispatch_h98 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 3557319#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 19) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h98b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 3557319#22) = false := by
  have := dispatch_h98 imm12 Rn Rt
  simpa using this

theorem dispatch_h99 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 3569664#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 12) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h99b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 3569664#22) = false := by
  have := dispatch_h99 imm12 Rn Rt
  simpa using this

theorem dispatch_h100 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) = 4067316#22) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 14) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h100b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 10) : BitVec 22) == 4067316#22) = false := by
  have := dispatch_h100 imm12 Rn Rt
  simpa using this

theorem dispatch_h101 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 64#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h101b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 64#11) = false := by
  have := dispatch_h101 imm12 Rn Rt
  simpa using this

theorem dispatch_h102 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 200#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h102b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 200#11) = false := by
  have := dispatch_h102 imm12 Rn Rt
  simpa using this

theorem dispatch_h103 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 202#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h103b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 202#11) = false := by
  have := dispatch_h103 imm12 Rn Rt
  simpa using this

theorem dispatch_h104 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 448#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h104b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 448#11) = false := by
  have := dispatch_h104 imm12 Rn Rt
  simpa using this

theorem dispatch_h105 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 449#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h105b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 449#11) = false := by
  have := dispatch_h105 imm12 Rn Rt
  simpa using this

theorem dispatch_h106 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 450#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h106b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 450#11) = false := by
  have := dispatch_h106 imm12 Rn Rt
  simpa using this

theorem dispatch_h107 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 451#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h107b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 451#11) = false := by
  have := dispatch_h107 imm12 Rn Rt
  simpa using this

theorem dispatch_h108 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 576#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h108b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 576#11) = false := by
  have := dispatch_h108 imm12 Rn Rt
  simpa using this

theorem dispatch_h109 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 712#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 8) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h109b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 712#11) = false := by
  have := dispatch_h109 imm12 Rn Rt
  simpa using this

theorem dispatch_h110 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 714#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h110b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 714#11) = false := by
  have := dispatch_h110 imm12 Rn Rt
  simpa using this

theorem dispatch_h111 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 960#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h111b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 960#11) = false := by
  have := dispatch_h111 imm12 Rn Rt
  simpa using this

theorem dispatch_h112 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 961#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h112b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 961#11) = false := by
  have := dispatch_h112 imm12 Rn Rt
  simpa using this

theorem dispatch_h113 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 962#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h113b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 962#11) = false := by
  have := dispatch_h113 imm12 Rn Rt
  simpa using this

theorem dispatch_h114 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 963#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h114b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 963#11) = false := by
  have := dispatch_h114 imm12 Rn Rt
  simpa using this

theorem dispatch_h115 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 1228#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h115b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 1228#11) = false := by
  have := dispatch_h115 imm12 Rn Rt
  simpa using this

theorem dispatch_h116 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 1476#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h116b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 1476#11) = false := by
  have := dispatch_h116 imm12 Rn Rt
  simpa using this

theorem dispatch_h117 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 1477#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h117b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 1477#11) = false := by
  have := dispatch_h117 imm12 Rn Rt
  simpa using this

theorem dispatch_h118 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 1739#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h118b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 1739#11) = false := by
  have := dispatch_h118 imm12 Rn Rt
  simpa using this

theorem dispatch_h119 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 1988#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h119b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 1988#11) = false := by
  have := dispatch_h119 imm12 Rn Rt
  simpa using this

theorem dispatch_h120 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) = 1989#11) := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 2) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    simp only [BitVec.getLsbD_append] at this
    simp at this

theorem dispatch_h120b (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 21) : BitVec 11) == 1989#11) = false := by
  have := dispatch_h120 imm12 Rn Rt
  simpa using this

theorem dispatch_h121 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 22) : BitVec 10) = 740#10 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h122 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 22) : BitVec 10) = 740#10 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h123 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 22) : BitVec 10) = 740#10 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h124 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 22) : BitVec 10) = 740#10 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h125 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 22) : BitVec 10) = 740#10 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h126 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 22) : BitVec 10) = 740#10 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h127 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 22) : BitVec 10) = 740#10 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h128 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 22) : BitVec 10) = 740#10 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h129 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 23) : BitVec 9) = 370#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h130 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 23) : BitVec 9) = 370#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h131 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 23) : BitVec 9) = 370#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h132 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 23) : BitVec 9) = 370#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h133 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 23) : BitVec 9) = 370#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h134 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 23) : BitVec 9) = 370#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h135 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 23) : BitVec 9) = 370#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h136 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 23) : BitVec 9) = 370#9 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h137 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 24) : BitVec 8) = 185#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h138 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 24) : BitVec 8) = 185#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h139 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 24) : BitVec 8) = 185#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h140 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 24) : BitVec 8) = 185#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h141 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 24) : BitVec 8) = 185#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h142 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 24) : BitVec 8) = 185#8 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h143 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h144 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h145 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 0 5 = Rt := by
    unfold NativeEntryBodyDispatch.StrWUoff.word BitVec.slice
    bv_field

theorem dispatch_h146 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 5 5 = Rn := by
    unfold NativeEntryBodyDispatch.StrWUoff.word BitVec.slice
    bv_field

theorem dispatch_h147 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 10 12 = imm12 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word BitVec.slice
    bv_field

theorem dispatch_h148 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 22 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h149 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 22 2 = 0#2 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp

theorem dispatch_h150 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 23 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h151 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 30 1 = 0#1 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h152 (imm12 : BitVec 12) (Rn : BitVec 5) (Rt : BitVec 5) :
    BitVec.slice (NativeEntryBodyDispatch.StrWUoff.word 2#2 57#6 0#2 imm12 Rn Rt) 30 2 = 2#2 := by
    unfold NativeEntryBodyDispatch.StrWUoff.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_append]
    rcases (by omega : i = 0 ∨ i = 1) with h | h <;> subst h <;> simp


/- Internal actual-state selector for a SEGMENTED decode group (see generator note).
The canonical prelude/owner frame must derive this SEE bound. -/
theorem dispatch_at (pc : Int) (Rt : BitVec 5) (Rn : BitVec 5) (imm12 : BitVec 12) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 648) :
    (__DecodeA64 (real := real) pc (NativeEntryBodyDispatch.StrWUoff.selected Rt Rn imm12) : SailM Unit) s =
      (do writeReg Register.SEE 648; decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 2#2 : SailM Unit) s := by
  rw [NativeEntryBodyDispatch.StrWUoff.selected]
  unfold __DecodeA64
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h83b, dispatch_h84, dispatch_h84b, dispatch_h85, dispatch_h85b, dispatch_h86, dispatch_h86b, dispatch_h87, dispatch_h87b, dispatch_h88, dispatch_h88b, dispatch_h89, dispatch_h89b, dispatch_h90, dispatch_h90b, dispatch_h91, dispatch_h91b, dispatch_h92, dispatch_h92b, dispatch_h93, dispatch_h93b, dispatch_h94, dispatch_h94b, dispatch_h95, dispatch_h95b, dispatch_h96, dispatch_h96b, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h115b, dispatch_h116, dispatch_h116b, dispatch_h117, dispatch_h117b, dispatch_h118, dispatch_h118b, dispatch_h119, dispatch_h119b, dispatch_h120, dispatch_h120b, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h83b, dispatch_h84, dispatch_h84b, dispatch_h85, dispatch_h85b, dispatch_h86, dispatch_h86b, dispatch_h87, dispatch_h87b, dispatch_h88, dispatch_h88b, dispatch_h89, dispatch_h89b, dispatch_h90, dispatch_h90b, dispatch_h91, dispatch_h91b, dispatch_h92, dispatch_h92b, dispatch_h93, dispatch_h93b, dispatch_h94, dispatch_h94b, dispatch_h95, dispatch_h95b, dispatch_h96, dispatch_h96b, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h115b, dispatch_h116, dispatch_h116b, dispatch_h117, dispatch_h117b, dispatch_h118, dispatch_h118b, dispatch_h119, dispatch_h119b, dispatch_h120, dispatch_h120b, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg0
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h83b, dispatch_h84, dispatch_h84b, dispatch_h85, dispatch_h85b, dispatch_h86, dispatch_h86b, dispatch_h87, dispatch_h87b, dispatch_h88, dispatch_h88b, dispatch_h89, dispatch_h89b, dispatch_h90, dispatch_h90b, dispatch_h91, dispatch_h91b, dispatch_h92, dispatch_h92b, dispatch_h93, dispatch_h93b, dispatch_h94, dispatch_h94b, dispatch_h95, dispatch_h95b, dispatch_h96, dispatch_h96b, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h115b, dispatch_h116, dispatch_h116b, dispatch_h117, dispatch_h117b, dispatch_h118, dispatch_h118b, dispatch_h119, dispatch_h119b, dispatch_h120, dispatch_h120b, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg1
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h83b, dispatch_h84, dispatch_h84b, dispatch_h85, dispatch_h85b, dispatch_h86, dispatch_h86b, dispatch_h87, dispatch_h87b, dispatch_h88, dispatch_h88b, dispatch_h89, dispatch_h89b, dispatch_h90, dispatch_h90b, dispatch_h91, dispatch_h91b, dispatch_h92, dispatch_h92b, dispatch_h93, dispatch_h93b, dispatch_h94, dispatch_h94b, dispatch_h95, dispatch_h95b, dispatch_h96, dispatch_h96b, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h115b, dispatch_h116, dispatch_h116b, dispatch_h117, dispatch_h117b, dispatch_h118, dispatch_h118b, dispatch_h119, dispatch_h119b, dispatch_h120, dispatch_h120b, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg2
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h83b, dispatch_h84, dispatch_h84b, dispatch_h85, dispatch_h85b, dispatch_h86, dispatch_h86b, dispatch_h87, dispatch_h87b, dispatch_h88, dispatch_h88b, dispatch_h89, dispatch_h89b, dispatch_h90, dispatch_h90b, dispatch_h91, dispatch_h91b, dispatch_h92, dispatch_h92b, dispatch_h93, dispatch_h93b, dispatch_h94, dispatch_h94b, dispatch_h95, dispatch_h95b, dispatch_h96, dispatch_h96b, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h115b, dispatch_h116, dispatch_h116b, dispatch_h117, dispatch_h117b, dispatch_h118, dispatch_h118b, dispatch_h119, dispatch_h119b, dispatch_h120, dispatch_h120b, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg3
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h83b, dispatch_h84, dispatch_h84b, dispatch_h85, dispatch_h85b, dispatch_h86, dispatch_h86b, dispatch_h87, dispatch_h87b, dispatch_h88, dispatch_h88b, dispatch_h89, dispatch_h89b, dispatch_h90, dispatch_h90b, dispatch_h91, dispatch_h91b, dispatch_h92, dispatch_h92b, dispatch_h93, dispatch_h93b, dispatch_h94, dispatch_h94b, dispatch_h95, dispatch_h95b, dispatch_h96, dispatch_h96b, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h115b, dispatch_h116, dispatch_h116b, dispatch_h117, dispatch_h117b, dispatch_h118, dispatch_h118b, dispatch_h119, dispatch_h119b, dispatch_h120, dispatch_h120b, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg4
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h83b, dispatch_h84, dispatch_h84b, dispatch_h85, dispatch_h85b, dispatch_h86, dispatch_h86b, dispatch_h87, dispatch_h87b, dispatch_h88, dispatch_h88b, dispatch_h89, dispatch_h89b, dispatch_h90, dispatch_h90b, dispatch_h91, dispatch_h91b, dispatch_h92, dispatch_h92b, dispatch_h93, dispatch_h93b, dispatch_h94, dispatch_h94b, dispatch_h95, dispatch_h95b, dispatch_h96, dispatch_h96b, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h115b, dispatch_h116, dispatch_h116b, dispatch_h117, dispatch_h117b, dispatch_h118, dispatch_h118b, dispatch_h119, dispatch_h119b, dispatch_h120, dispatch_h120b, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg5
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h83b, dispatch_h84, dispatch_h84b, dispatch_h85, dispatch_h85b, dispatch_h86, dispatch_h86b, dispatch_h87, dispatch_h87b, dispatch_h88, dispatch_h88b, dispatch_h89, dispatch_h89b, dispatch_h90, dispatch_h90b, dispatch_h91, dispatch_h91b, dispatch_h92, dispatch_h92b, dispatch_h93, dispatch_h93b, dispatch_h94, dispatch_h94b, dispatch_h95, dispatch_h95b, dispatch_h96, dispatch_h96b, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h115b, dispatch_h116, dispatch_h116b, dispatch_h117, dispatch_h117b, dispatch_h118, dispatch_h118b, dispatch_h119, dispatch_h119b, dispatch_h120, dispatch_h120b, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_LoadStore__seg6
  try simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h1b, dispatch_h2, dispatch_h3, dispatch_h4, dispatch_h5, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h9, dispatch_h10, dispatch_h11, dispatch_h12, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h40b, dispatch_h41, dispatch_h41b, dispatch_h42, dispatch_h42b, dispatch_h43, dispatch_h43b, dispatch_h44, dispatch_h44b, dispatch_h45, dispatch_h45b, dispatch_h46, dispatch_h46b, dispatch_h47, dispatch_h47b, dispatch_h48, dispatch_h48b, dispatch_h49, dispatch_h49b, dispatch_h50, dispatch_h50b, dispatch_h51, dispatch_h51b, dispatch_h52, dispatch_h52b, dispatch_h53, dispatch_h53b, dispatch_h54, dispatch_h54b, dispatch_h55, dispatch_h55b, dispatch_h56, dispatch_h57, dispatch_h58, dispatch_h59, dispatch_h60, dispatch_h61, dispatch_h62, dispatch_h63, dispatch_h64, dispatch_h65, dispatch_h66, dispatch_h67, dispatch_h68, dispatch_h69, dispatch_h70, dispatch_h71, dispatch_h72, dispatch_h73, dispatch_h74, dispatch_h75, dispatch_h76, dispatch_h77, dispatch_h78, dispatch_h79, dispatch_h80, dispatch_h81, dispatch_h82, dispatch_h83, dispatch_h83b, dispatch_h84, dispatch_h84b, dispatch_h85, dispatch_h85b, dispatch_h86, dispatch_h86b, dispatch_h87, dispatch_h87b, dispatch_h88, dispatch_h88b, dispatch_h89, dispatch_h89b, dispatch_h90, dispatch_h90b, dispatch_h91, dispatch_h91b, dispatch_h92, dispatch_h92b, dispatch_h93, dispatch_h93b, dispatch_h94, dispatch_h94b, dispatch_h95, dispatch_h95b, dispatch_h96, dispatch_h96b, dispatch_h97, dispatch_h97b, dispatch_h98, dispatch_h98b, dispatch_h99, dispatch_h99b, dispatch_h100, dispatch_h100b, dispatch_h101, dispatch_h101b, dispatch_h102, dispatch_h102b, dispatch_h103, dispatch_h103b, dispatch_h104, dispatch_h104b, dispatch_h105, dispatch_h105b, dispatch_h106, dispatch_h106b, dispatch_h107, dispatch_h107b, dispatch_h108, dispatch_h108b, dispatch_h109, dispatch_h109b, dispatch_h110, dispatch_h110b, dispatch_h111, dispatch_h111b, dispatch_h112, dispatch_h112b, dispatch_h113, dispatch_h113b, dispatch_h114, dispatch_h114b, dispatch_h115, dispatch_h115b, dispatch_h116, dispatch_h116b, dispatch_h117, dispatch_h117b, dispatch_h118, dispatch_h118b, dispatch_h119, dispatch_h119b, dispatch_h120, dispatch_h120b, dispatch_h121, dispatch_h122, dispatch_h123, dispatch_h124, dispatch_h125, dispatch_h126, dispatch_h127, dispatch_h128, dispatch_h129, dispatch_h130, dispatch_h131, dispatch_h132, dispatch_h133, dispatch_h134, dispatch_h135, dispatch_h136, dispatch_h137, dispatch_h138, dispatch_h139, dispatch_h140, dispatch_h141, dispatch_h142, dispatch_h143, dispatch_h144, dispatch_h145, dispatch_h146, dispatch_h147, dispatch_h148, dispatch_h149, dispatch_h150, dispatch_h151, dispatch_h152, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

  have h : (s.regs.bank_Int .SEE <b 648) = true := by simpa using see
  rw [ArmBridge.CruxCore.bind_app]
  have read : (readReg Register.SEE : SailM Int) s = .ok (s.regs.bank_Int .SEE) s := rfl
  rw [read]
  dsimp only []
  rw [if_pos h]
  simp only [bind_assoc, pure_bind, Bool.false_eq_true, ite_false, bind_pure_unit]

#print axioms dispatch_at
end NativeEntryBodyDispatch.StrWUoff
