-- physical SSA program outputs and entry agreement. Compile/input layouts are reused unchanged.
import ArmCertValue.ReleaseGen
import ArmCertValue.PhysicalGlue
set_option autoImplicit false
namespace ArmCertValue.Physical
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.RegBind (St)
open ArmBridge.Draft

theorem output_bytes_of_plan (real : Type) [Sail.SailReal real]
    (bytePA : BytePA) (regions : List Region) (plan : List StepV)
    (σ0 σf : Sym) (inputs : List (BitVec 64)) (D : List Def) (e : NativeState)
    (Inv : Nat → NativeState → Prop) (O : Region) (n : Nat) (outs : Nat → Nat × Nat) (spec : Nat → BitVec 8)
    (hc : compileRun regions σ0 inputs.length plan = some (D, σf))
    (hout : ∀ j, j < n → σf.memB O j = some ((outs j).1, (outs j).2))
    (hmath : ∀ j, j < n → (((extend inputs D).getD (outs j).1 0) >>> (8 * (outs j).2)).setWidth 8 = spec j)
    (hA0 : Agrees bytePA inputs σ0 e) (hB0 : σ0.Bounded inputs.length)
    (hinv : ∀ k, k < plan.length → Inv k (stateAt real e k))
    (hsteps : ∀ k (h : k < plan.length), StepFact real Inv bytePA regions plan k h) :
    ∀ j, j < n → regionByte bytePA (stateAt real e plan.length) O j = some (spec j) := by
  have hplan := planHolds_of_steps real Inv bytePA regions plan e hinv hsteps
  have hrun := run_agrees bytePA regions (stateAt real e) plan 0 inputs σ0 σf D
    hA0 hB0 hplan hc
  rw [Nat.zero_add] at hrun
  intro j hj
  rw [hrun.1.2.2 O j _ _ (hout j hj), hmath j hj]


theorem ret_reg_gen (bytePA : BytePA) (vals : List (BitVec 64))
    (σf : Sym) (sEnd fin : St) (r : HeapV2StepCerts.RegBind.Reg) (i : Nat) (v : BitVec 64)
    (hA : Agrees bytePA vals σf sEnd) (hσ : σf.regs r = some i) (hv : vals.getD i 0 = v)
    (hframe : HeapV2StepCerts.RegBind.regVal fin r = HeapV2StepCerts.RegBind.regVal sEnd r) :
    HeapV2StepCerts.RegBind.regVal fin r = v := by
  rw [hframe, hA.1 r i hσ, hv]


theorem agrees_σ0G (bytePA : BytePA) (s : St) (R : Region) (nb : Nat)
    (bytes : Nat → BitVec 8) (hI : ∀ j, j < nb → regionByte bytePA s R j = some (bytes j)) :
    Agrees bytePA (mkInputsG s nb bytes) (σ0G R nb) s := by
  refine ⟨?_, ?_, ?_⟩
  · intro r i h
    cases r with
    | x k =>
      simp only [σ0G, Option.some.injEq] at h
      subst h
      rw [mkInputsG_getD s nb bytes _ (by omega)]
      simp only [inputValG, if_neg (show ¬ nb + k.val < nb by omega), dif_pos (show nb + k.val < nb + 31 by omega)]
      congr 2
      exact Fin.ext (by simp)
    | sp =>
      simp only [σ0G, Option.some.injEq] at h
      subst h
      rw [mkInputsG_getD s nb bytes _ (by omega)]
      simp [inputValG]
      all_goals (try (intro h; omega))
  · intro n z c v h
    simp only [σ0G, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mkInputsG_getD s nb bytes _ (by omega)] <;> simp [inputValG] <;>
      (try (intro h; omega))
  · intro g j i k h
    simp only [σ0G] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h2; subst h1
      obtain ⟨rfl, hj⟩ := hc
      rw [hI j hj, mkInputsG_getD s nb bytes j (by omega)]
      simp only [inputValG, if_pos hj, Nat.mul_zero, BitVec.ushiftRight_zero]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      have := (bytes j).isLt
      omega
    · cases h


theorem agrees_σ0L (bytePA : BytePA) (s : St)
    (rs : List (Region × Nat)) (bytes : Nat → BitVec 8)
    (hI : ∀ g j i k, memBL rs 0 g j = some (i, k) → regionByte bytePA s g j = some (bytes i)) :
    Agrees bytePA (mkInputsL s rs bytes) (σ0L rs) s := by
  refine ⟨?_, ?_, ?_⟩
  · intro r i h
    unfold mkInputsL
    cases r with
    | x k =>
      simp only [σ0L, Option.some.injEq] at h
      subst h
      rw [mkInputsG_getD s _ bytes _ (by omega)]
      simp only [inputValG, if_neg (show ¬ totalL rs + k.val < totalL rs by omega),
        dif_pos (show totalL rs + k.val < totalL rs + 31 by omega)]
      congr 2
      exact Fin.ext (by simp)
    | sp =>
      simp only [σ0L, Option.some.injEq] at h
      subst h
      rw [mkInputsG_getD s _ bytes _ (by omega)]
      simp [inputValG]
      all_goals (try (intro h; omega))
  · intro n z c v h
    unfold mkInputsL
    simp only [σ0L, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mkInputsG_getD s _ bytes _ (by omega)] <;> simp [inputValG] <;>
      (try (intro h; omega))
  · intro g j i k h
    obtain ⟨rfl, -, hi⟩ := memBL_spec rs 0 g j i k h
    rw [hI g j i 0 h]
    unfold mkInputsL
    rw [mkInputsG_getD s (totalL rs) bytes i (by omega)]
    simp only [inputValG, if_pos (show i < totalL rs by omega), Nat.mul_zero, BitVec.ushiftRight_zero]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := (bytes i).isLt
    omega


/-- Byte of the physical run issued by one actual translated access. -/
def spanByte (mapping : BitVec 64 → Option Nat) (s : St) (start : BitVec 64) (i : Nat) : Option (BitVec 8) :=
  (mapping start).bind fun pa => s.mem[pa + i]?

theorem regionByte_eq_spanByte (mapping : BitVec 64 → Option Nat) (bytePA : BytePA) (s : St)
    (r : Region) (j0 i : Nat) (start : BitVec 64)
    (view : bytePA r (j0 + i) = spanPA mapping start i) :
    regionByte bytePA s r (j0 + i) = spanByte mapping s start i := by
  unfold regionByte
  rw [view]
  unfold spanPA spanByte
  cases mapping start <;> rfl

/-- The physical output facts transport through an epilogue preserving those same physical bytes. -/
theorem out_bytes_frame (bytePA : BytePA) (sEnd fin : St) (r : Region) (n : Nat) (spec : Nat → BitVec 8)
    (hbody : ∀ j, j < n → regionByte bytePA sEnd r j = some (spec j))
    (hframe : ∀ j, j < n → regionByte bytePA fin r j = regionByte bytePA sEnd r j) :
    ∀ j, j < n → regionByte bytePA fin r j = some (spec j) := by
  intro j hj
  rw [hframe j hj]
  exact hbody j hj

#print axioms output_bytes_of_plan
#print axioms agrees_σ0G
#print axioms agrees_σ0L
#print axioms regionByte_eq_spanByte
#print axioms out_bytes_frame
end ArmCertValue.Physical
