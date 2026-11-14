import NativeAccess.StpSplit
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace NativeAccess.PairGeometry
open MemM1.MemReadD MemM1.MemReadD2

def joinTest (a : BitVec 64) : Bool :=
  Align_bits (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1) 16 == Align_bits a 16

/-- A naturally aligned16 access cannot wrap its last byte. This is derived,
not an extra whole-range no-wrap premise. -/
theorem join_of_mod16 (a : BitVec 64) (aligned : a.toNat % 16 = 0) : joinTest a = true := by
  have hx : Align_bits (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1) (16 : Int) =
      BitVec.ofNat 64 ((BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1).toNat / 16 * 16) :=
    align_lit _ 16 (by decide)
  have hx' : Align_bits a (16 : Int) = BitVec.ofNat 64 (a.toNat / 16 * 16) := align_lit a 16 (by decide)
  have hlt := a.isLt
  have finish : (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1).toNat = a.toNat + 15 := by
    simp [BitVec.subInt,BitVec.addInt,BitVec.toNat_add,BitVec.toNat_sub]
    omega
  unfold joinTest
  rw [hx,hx',finish]
  have block : (a.toNat + 15) / 16 * 16 = a.toNat / 16 * 16 := by omega
  rw [block]
  simp

/-- The failing join test also covers the final partial block before modular
VA wraparound; no global no-wrap hypothesis is used. -/
theorem join_false_of_mod16 (a : BitVec 64) (unaligned : a.toNat % 16 ≠ 0) : joinTest a = false := by
  have hx : Align_bits (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1) (16 : Int) =
      BitVec.ofNat 64 ((BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1).toNat / 16 * 16) :=
    align_lit _ 16 (by decide)
  have hx' : Align_bits a (16 : Int) = BitVec.ofNat 64 (a.toNat / 16 * 16) := align_lit a 16 (by decide)
  have hlt := a.isLt
  have finish : (BitVec.subInt (BitVec.addInt a ((16 : Nat) : Int)) 1).toNat =
      (a.toNat + 15) % 2 ^ 64 := by
    simp [BitVec.subInt,BitVec.addInt,BitVec.toNat_add,BitVec.toNat_sub]
    omega
  unfold joinTest
  rw [hx,hx',finish,beq_eq_false_iff_ne]
  intro equal
  have bits := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat] at bits
  omega

theorem aligned8_false (a : BitVec 64) (unaligned : a.toNat % 8 ≠ 0) :
    IsAligned__1 a ((8 : Nat) : Int) = false := by
  have hx := align_lit a 8 (by decide)
  unfold IsAligned__1
  rw [hx,beq_eq_false_iff_ne]
  intro equal
  have bits := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat] at bits
  have hlt := a.isLt
  omega

theorem pairAligned_false (a : BitVec 64) (unaligned : a.toNat % 8 ≠ 0) :
    Logical.accessAligned a 16 true = false := by
  change IsAligned__1 a ((8 : Nat) : Int) = false
  exact aligned8_false a unaligned

inductive Case where
  | one16 | two8 | bytes
  deriving DecidableEq

def selected (a : BitVec 64) : Case :=
  if a.toNat % 16 = 0 then .one16 else if a.toNat % 8 = 0 then .two8 else .bytes

/-- Exhaustive pure branch selectors for the actual LSE2true pair paths.
All three cases retain the same arbitrary 64-bit starting address. -/
theorem selected_spec (a : BitVec 64) :
    match selected a with
    | .one16 => Read.Within16 a ((16 : Nat) : Int)
    | .two8 => a.toNat % 8 = 0 ∧ a.toNat % 16 ≠ 0
    | .bytes => Logical.accessAligned a 16 true = false ∧ joinTest a = false := by
  by_cases aligned16 : a.toNat % 16 = 0
  · simp only [selected,if_pos aligned16]
    exact join_of_mod16 a aligned16
  · by_cases aligned8 : a.toNat % 8 = 0
    · simp only [selected,if_neg aligned16,if_pos aligned8]
      exact ⟨aligned8,aligned16⟩
    · simp only [selected,if_neg aligned16,if_neg aligned8]
      exact ⟨pairAligned_false a aligned8,join_false_of_mod16 a aligned16⟩

theorem join_disabled (a : BitVec 64) (feature : Bool) (not16 : a.toNat % 16 ≠ 0) :
    (feature && joinTest a) = false := by rw [join_false_of_mod16 a not16,Bool.and_false]

#print axioms selected_spec
#print axioms join_disabled
end NativeAccess.PairGeometry
