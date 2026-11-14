import NativeEntryCallerDispatch.BlWord
import ArmFull.Fn.M1475
import Bridge.CruxCore
import Bridge.Awc
import Bridge.BvField
open Sail ArmFull ArmFull.Functions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
namespace NativeEntryCallerDispatch.Bl
theorem append_low {n m i : Nat} (x : BitVec n) (y : BitVec m) (hi : i < m) :
    (BitVec.append x y).getLsbD i = y.getLsbD i := by
  simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend,
    BitVec.getLsbD_setWidth']
  simp [hi]

variable (real : Type) [Sail.SailReal real]

theorem dispatch_h0 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 27 25) : BitVec 3) = 5#3) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h0b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 27 25) : BitVec 3) == 5#3) = false := by
  have := dispatch_h0 imm26
  simpa using this

theorem dispatch_h1 (imm26 : BitVec 26) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 27 27) : BitVec 1) = 0#1 := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth']
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h2 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 28 25) : BitVec 4) = 0#4) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h2b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 28 25) : BitVec 4) == 0#4) = false := by
  have := dispatch_h2 imm26
  simpa using this

theorem dispatch_h3 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 28 25) : BitVec 4) = 1#4) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 1) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h3b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 28 25) : BitVec 4) == 1#4) = false := by
  have := dispatch_h3 imm26
  simpa using this

theorem dispatch_h4 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 28 25) : BitVec 4) = 2#4) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h4b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 28 25) : BitVec 4) == 2#4) = false := by
  have := dispatch_h4 imm26
  simpa using this

theorem dispatch_h5 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 28 25) : BitVec 4) = 3#4) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 3) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h5b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 28 25) : BitVec 4) == 3#4) = false := by
  have := dispatch_h5 imm26
  simpa using this

theorem dispatch_h6 (imm26 : BitVec 26) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 28 26) : BitVec 3) = 5#3 := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth']
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h7 (imm26 : BitVec 26) :
    (Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 28 26) : BitVec 3) = 5#3 := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth']
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h <;> subst h <;> simp

theorem dispatch_h8 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 30 24) : BitVec 7) = 52#7) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h8b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 30 24) : BitVec 7) == 52#7) = false := by
  have := dispatch_h8 imm26
  simpa using this

theorem dispatch_h9 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 30 24) : BitVec 7) = 53#7) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h9b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 30 24) : BitVec 7) == 53#7) = false := by
  have := dispatch_h9 imm26
  simpa using this

theorem dispatch_h10 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 30 24) : BitVec 7) = 54#7) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h10b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 30 24) : BitVec 7) == 54#7) = false := by
  have := dispatch_h10 imm26
  simpa using this

theorem dispatch_h11 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 30 24) : BitVec 7) = 55#7) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h11b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 30 24) : BitVec 7) == 55#7) = false := by
  have := dispatch_h11 imm26
  simpa using this

theorem dispatch_h12 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 5) : BitVec 27) = 111679616#27) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 25) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h12b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 5) : BitVec 27) == 111679616#27) = false := by
  have := dispatch_h12 imm26
  simpa using this

theorem dispatch_h13 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 5) : BitVec 27) = 111679617#27) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 25) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h13b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 5) : BitVec 27) == 111679617#27) = false := by
  have := dispatch_h13 imm26
  simpa using this

theorem dispatch_h14 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 5) : BitVec 27) = 111745411#27) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 25) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h14b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 5) : BitVec 27) == 111745411#27) = false := by
  have := dispatch_h14 imm26
  simpa using this

theorem dispatch_h15 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 5) : BitVec 27) = 111745419#27) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 25) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h15b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 5) : BitVec 27) == 111745419#27) = false := by
  have := dispatch_h15 imm26
  simpa using this

theorem dispatch_h16 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 8) : BitVec 24) = 13959972#24) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 22) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h16b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 8) : BitVec 24) == 13959972#24) = false := by
  have := dispatch_h16 imm26
  simpa using this

theorem dispatch_h17 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 10) : BitVec 22) = 3489992#22) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 20) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h17b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 10) : BitVec 22) == 3489992#22) = false := by
  have := dispatch_h17 imm26
  simpa using this

theorem dispatch_h18 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 10) : BitVec 22) = 3508160#22) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 20) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h18b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 10) : BitVec 22) == 3508160#22) = false := by
  have := dispatch_h18 imm26
  simpa using this

theorem dispatch_h19 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 10) : BitVec 22) = 3510208#22) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 20) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h19b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 10) : BitVec 22) == 3510208#22) = false := by
  have := dispatch_h19 imm26
  simpa using this

theorem dispatch_h20 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 10) : BitVec 22) = 3512256#22) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 20) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h20b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 10) : BitVec 22) == 3512256#22) = false := by
  have := dispatch_h20 imm26
  simpa using this

theorem dispatch_h21 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 11) : BitVec 21) = 1756129#21) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 19) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h21b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 11) : BitVec 21) == 1756129#21) = false := by
  have := dispatch_h21 imm26
  simpa using this

theorem dispatch_h22 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 11) : BitVec 21) = 1758177#21) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 19) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h22b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 11) : BitVec 21) == 1758177#21) = false := by
  have := dispatch_h22 imm26
  simpa using this

theorem dispatch_h23 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 12) : BitVec 20) = 872498#20) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 18) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h23b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 12) : BitVec 20) == 872498#20) = false := by
  have := dispatch_h23 imm26
  simpa using this

theorem dispatch_h24 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 12) : BitVec 20) = 872499#20) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 18) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h24b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 12) : BitVec 20) == 872499#20) = false := by
  have := dispatch_h24 imm26
  simpa using this

theorem dispatch_h25 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 19) : BitVec 13) = 6816#13) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 11) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h25b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 19) : BitVec 13) == 6816#13) = false := by
  have := dispatch_h25 imm26
  simpa using this

theorem dispatch_h26 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 19) : BitVec 13) = 6817#13) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 11) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h26b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 19) : BitVec 13) == 6817#13) = false := by
  have := dispatch_h26 imm26
  simpa using this

theorem dispatch_h27 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 19) : BitVec 13) = 6821#13) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 11) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h27b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 19) : BitVec 13) == 6821#13) = false := by
  have := dispatch_h27 imm26
  simpa using this

theorem dispatch_h28 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 19) : BitVec 13) = 6825#13) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 11) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h28b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 19) : BitVec 13) == 6825#13) = false := by
  have := dispatch_h28 imm26
  simpa using this

theorem dispatch_h29 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 20) : BitVec 12) = 3409#12) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h29b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 20) : BitVec 12) == 3409#12) = false := by
  have := dispatch_h29 imm26
  simpa using this

theorem dispatch_h30 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 20) : BitVec 12) = 3411#12) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h30b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 20) : BitVec 12) == 3411#12) = false := by
  have := dispatch_h30 imm26
  simpa using this

theorem dispatch_h31 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 20) : BitVec 12) = 3413#12) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h31b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 20) : BitVec 12) == 3413#12) = false := by
  have := dispatch_h31 imm26
  simpa using this

theorem dispatch_h32 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 20) : BitVec 12) = 3415#12) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 10) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h32b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 20) : BitVec 12) == 3415#12) = false := by
  have := dispatch_h32 imm26
  simpa using this

theorem dispatch_h33 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 21) : BitVec 11) = 1696#11) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h33b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 21) : BitVec 11) == 1696#11) = false := by
  have := dispatch_h33 imm26
  simpa using this

theorem dispatch_h34 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 21) : BitVec 11) = 1697#11) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h34b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 21) : BitVec 11) == 1697#11) = false := by
  have := dispatch_h34 imm26
  simpa using this

theorem dispatch_h35 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 21) : BitVec 11) = 1698#11) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h35b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 21) : BitVec 11) == 1698#11) = false := by
  have := dispatch_h35 imm26
  simpa using this

theorem dispatch_h36 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 21) : BitVec 11) = 1699#11) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h36b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 21) : BitVec 11) == 1699#11) = false := by
  have := dispatch_h36 imm26
  simpa using this

theorem dispatch_h37 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 21) : BitVec 11) = 1701#11) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 9) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h37b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 21) : BitVec 11) == 1701#11) = false := by
  have := dispatch_h37 imm26
  simpa using this

theorem dispatch_h38 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 24) : BitVec 8) = 84#8) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 6) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h38b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 24) : BitVec 8) == 84#8) = false := by
  have := dispatch_h38 imm26
  simpa using this

theorem dispatch_h39 (imm26 : BitVec 26) :
    ¬ ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 25) : BitVec 7) = 107#7) := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    intro h; have := congrArg (fun v => BitVec.getLsbD v 5) h
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_h39b (imm26 : BitVec 26) :
    ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 25) : BitVec 7) == 107#7) = false := by
  have := dispatch_h39 imm26
  simpa using this

theorem dispatch_h40 (imm26 : BitVec 26) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 26) : BitVec 6) = 37#6 := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth']
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h41 (imm26 : BitVec 26) :
    (Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 26) : BitVec 6) = 37#6 := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth']
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with h | h | h | h | h | h <;> subst h <;> simp

theorem dispatch_h42 (imm26 : BitVec 26) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth']
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h43 (imm26 : BitVec 26) :
    (Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb (NativeEntryCallerDispatch.Bl.word imm26) 31 31) : BitVec 1) = 1#1 := by
    unfold NativeEntryCallerDispatch.Bl.word
    rw [ArmBridge.Awc.castWidth_of_eq (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_cast, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb']
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth']
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_h44 (imm26 : BitVec 26) :
    BitVec.slice (NativeEntryCallerDispatch.Bl.word imm26) 0 26 = imm26 := by
    unfold NativeEntryCallerDispatch.Bl.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', Nat.zero_add]
    simpa [hi] using (append_low (37#6) imm26 hi)

theorem dispatch_h45 (imm26 : BitVec 26) :
    BitVec.slice (NativeEntryCallerDispatch.Bl.word imm26) 31 1 = 1#1 := by
    unfold NativeEntryCallerDispatch.Bl.word BitVec.slice
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb']
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth']
    rcases (by omega : i = 0) with h <;> subst h <;> simp

theorem dispatch_hw46 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573563423#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw47 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573563455#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw48 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573563487#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw49 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573751839#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw50 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573751871#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw51 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573751903#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw52 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573751935#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw53 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573751967#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw54 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573751999#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw55 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573752031#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw56 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573752063#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw57 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573752351#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw58 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573752383#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw59 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573752415#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw60 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573752447#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw61 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573752479#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw62 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573752543#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw63 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573753119#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw64 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573756031#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw65 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3573756159#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw66 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3600745440#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch_hw67 (imm26 : BitVec 26) :
    ¬ ((NativeEntryCallerDispatch.Bl.word imm26) = 3602842592#32) := by
    intro h
    have := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    unfold NativeEntryCallerDispatch.Bl.word at this
    try simp only [BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth'] at this
    simp at this

theorem dispatch (pc : Int) (imm26 : BitVec 26) :
    __DecodeA64 (real := real) pc (NativeEntryCallerDispatch.Bl.word imm26) = (do
      let c ← (do let x ← readReg Register.SEE; pure (x <b 68))
      if c = true then (do writeReg Register.SEE 68; decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1)
      else sailThrow (exception.Error_Undefined ())) := by
  unfold __DecodeA64
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h2, dispatch_h2b, dispatch_h3, dispatch_h3b, dispatch_h4, dispatch_h4b, dispatch_h5, dispatch_h5b, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_hw46, dispatch_hw47, dispatch_hw48, dispatch_hw49, dispatch_hw50, dispatch_hw51, dispatch_hw52, dispatch_hw53, dispatch_hw54, dispatch_hw55, dispatch_hw56, dispatch_hw57, dispatch_hw58, dispatch_hw59, dispatch_hw60, dispatch_hw61, dispatch_hw62, dispatch_hw63, dispatch_hw64, dispatch_hw65, dispatch_hw66, dispatch_hw67, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]
  unfold __DecodeA64_BranchExcSys
  simp (config := {decide := true}) only [dispatch_h0, dispatch_h0b, dispatch_h1, dispatch_h2, dispatch_h2b, dispatch_h3, dispatch_h3b, dispatch_h4, dispatch_h4b, dispatch_h5, dispatch_h5b, dispatch_h6, dispatch_h7, dispatch_h8, dispatch_h8b, dispatch_h9, dispatch_h9b, dispatch_h10, dispatch_h10b, dispatch_h11, dispatch_h11b, dispatch_h12, dispatch_h12b, dispatch_h13, dispatch_h13b, dispatch_h14, dispatch_h14b, dispatch_h15, dispatch_h15b, dispatch_h16, dispatch_h16b, dispatch_h17, dispatch_h17b, dispatch_h18, dispatch_h18b, dispatch_h19, dispatch_h19b, dispatch_h20, dispatch_h20b, dispatch_h21, dispatch_h21b, dispatch_h22, dispatch_h22b, dispatch_h23, dispatch_h23b, dispatch_h24, dispatch_h24b, dispatch_h25, dispatch_h25b, dispatch_h26, dispatch_h26b, dispatch_h27, dispatch_h27b, dispatch_h28, dispatch_h28b, dispatch_h29, dispatch_h29b, dispatch_h30, dispatch_h30b, dispatch_h31, dispatch_h31b, dispatch_h32, dispatch_h32b, dispatch_h33, dispatch_h33b, dispatch_h34, dispatch_h34b, dispatch_h35, dispatch_h35b, dispatch_h36, dispatch_h36b, dispatch_h37, dispatch_h37b, dispatch_h38, dispatch_h38b, dispatch_h39, dispatch_h39b, dispatch_h40, dispatch_h41, dispatch_h42, dispatch_h43, dispatch_h44, dispatch_h45, dispatch_hw46, dispatch_hw47, dispatch_hw48, dispatch_hw49, dispatch_hw50, dispatch_hw51, dispatch_hw52, dispatch_hw53, dispatch_hw54, dispatch_hw55, dispatch_hw56, dispatch_hw57, dispatch_hw58, dispatch_hw59, dispatch_hw60, dispatch_hw61, dispatch_hw62, dispatch_hw63, dispatch_hw64, dispatch_hw65, dispatch_hw66, dispatch_hw67, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, beq_self_eq_true, beq_iff_eq, decide_false, decide_true,
    reduceIte, pure_bind, bind_assoc, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, Bool.not_true, Bool.not_false]

#print axioms dispatch

/- The canonical actual prelude must derive this internal SEE bound. -/
theorem dispatch_at (pc : Int) (imm26 : BitVec 26) (s : ArmBridge.Draft.NativeState)
    (see : s.regs.bank_Int .SEE < 68) :
    (__DecodeA64 (real := real) pc (word imm26) : SailM Unit) s =
      (do writeReg Register.SEE 68; decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 1#1 : SailM Unit) s := by
  rw [dispatch real pc imm26]
  have h : (s.regs.bank_Int .SEE <b 68) = true := by simpa using see
  have read : ((do let x ← readReg Register.SEE; pure (x <b 68)) : SailM Bool) s =
      .ok (s.regs.bank_Int .SEE <b 68) s := by rfl
  rw [ArmBridge.CruxCore.bind_app, read]
  dsimp only []
  rw [if_pos h]

#print axioms dispatch_at
end NativeEntryCallerDispatch.Bl
