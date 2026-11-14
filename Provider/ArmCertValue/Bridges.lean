-- H-P1 Release bridges (certiffi): the value layer's region bytes / input table vs Release.Functional's
-- bufByte / inputValue, and the body-entry agreement `Agrees … σ0` built from the actual state.
import ArmCertValue.HP1Run
import Bridge.CruxGenGuarded.ReleaseHeadline
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue.HeapV2Plan
open ArmCertValue
open HeapV2StepCerts.RegBind (Reg St regVal)
open ArmBridge.Draft ArmCert.Translate ArmCert.Translate.Model

/-! ## Region bytes = Release.bufByte -/

theorem regionByte_eq_bufByte (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (s : St)
    (pin w j : Nat) :
    regionByte mapping pinv s ⟨pin, 0, w⟩ j = ArmBridge.CruxGenGuarded.Release.bufByte mapping s (pinv pin) j := by
  unfold regionByte ArmBridge.CruxGenGuarded.Release.bufByte
  have h : ((pinv pin : Int) + (0 : Int) + (j : Int)) = ((pinv pin + j : Nat) : Int) := by push_cast; omega
  simp only [h, BitVec.ofInt_natCast]

/-! ## Input value: Release.inputValue (foldr) = little-endian sum -/

theorem foldr_range_le (b : Nat → Nat) :
    ∀ (n a : Nat), (List.range n).foldr (fun i acc => acc * 256 + b i) a =
      a * 256 ^ n + ((List.range n).map fun j => 256 ^ j * b j).sum := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
    intro a
    rw [List.range_succ, List.foldr_append, List.map_append, List.sum_append]
    simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero]
    rw [ih]
    have key : (a * 256 + b n) * 256 ^ n = a * 256 ^ (n + 1) + 256 ^ n * b n := by
      rw [Nat.add_mul, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ n), Nat.mul_comm (b n)]
    rw [key]
    omega

theorem inputValue_eq_sum (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins) (s : NativeState) :
    ArmBridge.CruxGenGuarded.Release.inputValue mapping pins s =
      ((List.range 32).map fun j =>
        256 ^ j * ((ArmBridge.CruxGenGuarded.Release.bufByte mapping s pins.x1 j).getD 0#8).toNat).sum := by
  unfold ArmBridge.CruxGenGuarded.Release.inputValue
  rw [foldr_range_le (fun i => ((ArmBridge.CruxGenGuarded.Release.bufByte mapping s pins.x1 i).getD 0#8).toNat) 32 0]
  simp

theorem p256k1_eq : TranslateValue.HP1.p256k1 = ArmBridge.CruxGenGuarded.Release.p256k1 := by
  unfold TranslateValue.HP1.p256k1 ArmBridge.CruxGenGuarded.Release.p256k1; omega

/-! ## Body-entry inputs and the initial agreement -/

/-- The 68 table inputs at body entry: 32 input bytes, x0..x30, sp, N Z C V. -/
def inputVal (s : St) (bytes : Nat → BitVec 8) (t : Nat) : BitVec 64 :=
  if t < 32 then (bytes t).setWidth 64
  else if h : t < 63 then regVal s (.x ⟨t - 32, by omega⟩)
  else if t = 63 then regVal s .sp
  else if t = 64 then s.regs.PSTATE.N.setWidth 64
  else if t = 65 then s.regs.PSTATE.Z.setWidth 64
  else if t = 66 then s.regs.PSTATE.C.setWidth 64
  else s.regs.PSTATE.V.setWidth 64

def mkInputs (s : St) (bytes : Nat → BitVec 8) : List (BitVec 64) := List.ofFn (n := 68) fun t => inputVal s bytes t.val

theorem mkInputs_length (s : St) (bytes : Nat → BitVec 8) : (mkInputs s bytes).length = 68 := by
  simp [mkInputs]

theorem mkInputs_getD (s : St) (bytes : Nat → BitVec 8) (t : Nat) (ht : t < 68) :
    (mkInputs s bytes).getD t 0 = inputVal s bytes t := by
  unfold mkInputs
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [ht]

theorem mkInputs_bytes (s : St) (bytes : Nat → BitVec 8) :
    ∀ i, i < 32 → ((mkInputs s bytes).getD i 0).toNat < 256 := by
  intro i hi
  rw [mkInputs_getD s bytes i (by omega)]
  simp only [inputVal, if_pos hi, BitVec.toNat_setWidth]
  have := (bytes i).isLt
  omega

/-- The body-entry agreement: tracked registers/flags are the state's own, and input byte j is `bytes j`. -/
theorem agrees_σ0 (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (s : St) (bytes : Nat → BitVec 8)
    (hI : ∀ j, j < 32 → regionByte mapping pinv s I j = some (bytes j)) :
    Agrees mapping pinv (mkInputs s bytes) σ0 s := by
  refine ⟨?_, ?_, ?_⟩
  · intro r i h
    cases r with
    | x k =>
      simp only [σ0, Option.some.injEq] at h
      subst h
      rw [mkInputs_getD s bytes _ (by omega)]
      simp only [inputVal, if_neg (show ¬ 32 + k.val < 32 by omega), dif_pos (show 32 + k.val < 63 by omega)]
      congr 2
      exact Fin.ext (by simp)
    | sp =>
      simp only [σ0, Option.some.injEq] at h
      subst h
      rw [mkInputs_getD s bytes _ (by omega)]
      simp [inputVal]
  · intro n z c v h
    simp only [σ0, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mkInputs_getD s bytes _ (by omega)] <;> simp [inputVal]
  · intro g j i k h
    simp only [σ0] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h2; subst h1
      obtain ⟨rfl, hj⟩ := hc
      rw [hI j hj, mkInputs_getD s bytes j (by omega)]
      simp only [inputVal, if_pos hj, Nat.mul_zero, BitVec.ushiftRight_zero]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      have := (bytes j).isLt
      omega
    · cases h

/-- inVal of the body-entry inputs = Release.inputValue at the caller entry, given the input bytes
are read through bufByte at entry (the shim does not touch I). -/
theorem inVal_mkInputs (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins) (s : St) (e : NativeState)
    (bytes : Nat → BitVec 8)
    (hb : ∀ j, j < 32 → ArmBridge.CruxGenGuarded.Release.bufByte mapping e pins.x1 j = some (bytes j)) :
    TranslateValue.HP1.inVal (mkInputs s bytes) = ArmBridge.CruxGenGuarded.Release.inputValue mapping pins e := by
  rw [inputValue_eq_sum]
  unfold TranslateValue.HP1.inVal
  congr 1
  apply List.map_congr_left
  intro j mj
  have hj := List.mem_range.1 mj
  rw [hb j hj, mkInputs_getD s bytes j (by omega)]
  simp only [inputVal, if_pos hj, BitVec.toNat_setWidth, Option.getD_some]
  have := (bytes j).isLt
  rw [Nat.mod_eq_of_lt (by omega), show (2 : Nat) ^ (8 * j) = 256 ^ j by rw [Nat.pow_mul]]

end ArmCertValue.HeapV2Plan
