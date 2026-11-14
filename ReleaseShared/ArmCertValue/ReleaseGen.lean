-- ArmCert VALUE LAYER, a design decision P6 template (certiffi): program-generic "output bytes = spec" on the
-- actual Sail run. A generated program instance supplies its plan / compile result / output map / math
-- lemma / per-step facts / entry agreement; heap-v2's hp1_run + functional_of_value are one instance.
import ArmCertValue.Glue
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.RegBind (St)
open ArmBridge.Draft

/-- **Generic program output theorem.** For any program whose plan compiles (from σ0 over the `inputs`
table) to `D` with final symbolic state `σf`, if every output byte j < n of region `O` is tracked by `σf`
as byte `(outs j).2` of table entry `(outs j).1`, and the math lemma says that byte equals `spec j`, then
— given the per-step value facts and the entry agreement — output byte j at the end of the run is `spec j`. -/
theorem output_bytes_of_plan (real : Type) [Sail.SailReal real]
    (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (regions : List Region) (plan : List StepV)
    (σ0 σf : Sym) (inputs : List (BitVec 64)) (D : List Def) (e : NativeState)
    (Inv : Nat → NativeState → Prop) (O : Region) (n : Nat) (outs : Nat → Nat × Nat) (spec : Nat → BitVec 8)
    (hc : compileRun regions σ0 inputs.length plan = some (D, σf))
    (hout : ∀ j, j < n → σf.memB O j = some ((outs j).1, (outs j).2))
    (hmath : ∀ j, j < n → (((extend inputs D).getD (outs j).1 0) >>> (8 * (outs j).2)).setWidth 8 = spec j)
    (hcoh : RegionCoherent mapping pinv)
    (hA0 : Agrees mapping pinv inputs σ0 e) (hB0 : σ0.Bounded inputs.length)
    (hinv : ∀ k, k < plan.length → Inv k (stateAt real e k))
    (hsteps : ∀ k (h : k < plan.length), StepFact real Inv mapping pinv regions plan k h) :
    ∀ j, j < n → regionByte mapping pinv (stateAt real e plan.length) O j = some (spec j) := by
  have hplan := planHolds_of_steps real Inv mapping pinv regions plan e hinv hsteps
  have hrun := run_agrees mapping pinv regions (stateAt real e) hcoh plan 0 inputs σ0 σf D
    hA0 hB0 hplan hc
  rw [Nat.zero_add] at hrun
  intro j hj
  rw [hrun.1.2.2 O j _ _ (hout j hj), hmath j hj]

#print axioms output_bytes_of_plan

/-! ## P6: from region bytes at the body's end to buffer bytes at the caller's return -/

/-- Byte i of the buffer at VA va (the shape of every program's Functional, e.g. Release.bufByte). -/
def bufByteG (mapping : BitVec 64 → Option Nat) (s : St) (va i : Nat) : Option (BitVec 8) :=
  (mapping (BitVec.ofNat 64 (va + i))).bind fun pa => s.mem[pa]?

theorem regionByte_eq_bufByteG (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (s : St)
    (pin w j : Nat) : regionByte mapping pinv s ⟨pin, 0, w⟩ j = bufByteG mapping s (pinv pin) j := by
  unfold regionByte bufByteG
  have h : ((pinv pin : Int) + (0 : Int) + (j : Int)) = ((pinv pin + j : Nat) : Int) := by push_cast; omega
  simp only [h, BitVec.ofInt_natCast]

/-- **Generic P6 output bridge.** If the program's output region is ⟨pin, 0, w⟩ and the epilogue (body end
`sEnd` → caller return `fin`) leaves the output buffer unchanged, the output-byte facts at the body's end
(`output_bytes_of_plan`) become buffer-byte facts at the caller's return — the shape of every program's
Functional output conjunct. -/
theorem out_bufBytes_gen (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (sEnd fin : St)
    (pin w n : Nat) (spec : Nat → BitVec 8)
    (hbody : ∀ j, j < n → regionByte mapping pinv sEnd ⟨pin, 0, w⟩ j = some (spec j))
    (hframe : ∀ j, j < n → bufByteG mapping fin (pinv pin) j = bufByteG mapping sEnd (pinv pin) j) :
    ∀ j, j < n → bufByteG mapping fin (pinv pin) j = some (spec j) := by
  intro j hj
  rw [hframe j hj, ← regionByte_eq_bufByteG]
  exact hbody j hj

#print axioms out_bufBytes_gen

/-! ## Return-register facts (from the value layer, e.g. a scrubbed x0 tracked as a constant) -/

/-- A register tracked at the body's end with a known table value, unchanged by the epilogue, has that
value at the caller's return. -/
theorem ret_reg_gen (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (vals : List (BitVec 64))
    (σf : Sym) (sEnd fin : St) (r : HeapV2StepCerts.RegBind.Reg) (i : Nat) (v : BitVec 64)
    (hA : Agrees mapping pinv vals σf sEnd) (hσ : σf.regs r = some i) (hv : vals.getD i 0 = v)
    (hframe : HeapV2StepCerts.RegBind.regVal fin r = HeapV2StepCerts.RegBind.regVal sEnd r) :
    HeapV2StepCerts.RegBind.regVal fin r = v := by
  rw [hframe, hA.1 r i hσ, hv]

/-! ## Generic entry agreement: nb input bytes from region R, then x0..x30, sp, N Z C V -/

/-- Entry symbolic state: inputs 0..nb-1 = bytes of region R, nb..nb+30 = x0..x30, nb+31 = sp,
nb+32..nb+35 = N Z C V. -/
def σ0G (R : Region) (nb : Nat) : Sym where
  regs := fun r => match r with | .x i => some (nb + i.val) | .sp => some (nb + 31)
  nzcv := some (nb + 32, nb + 33, nb + 34, nb + 35)
  memB := fun g j => if g = R ∧ j < nb then some (j, 0) else none

def inputValG (s : St) (nb : Nat) (bytes : Nat → BitVec 8) (t : Nat) : BitVec 64 :=
  if t < nb then (bytes t).setWidth 64
  else if h : t < nb + 31 then HeapV2StepCerts.RegBind.regVal s (.x ⟨t - nb, by omega⟩)
  else if t = nb + 31 then HeapV2StepCerts.RegBind.regVal s .sp
  else if t = nb + 32 then s.regs.PSTATE.N.setWidth 64
  else if t = nb + 33 then s.regs.PSTATE.Z.setWidth 64
  else if t = nb + 34 then s.regs.PSTATE.C.setWidth 64
  else s.regs.PSTATE.V.setWidth 64

def mkInputsG (s : St) (nb : Nat) (bytes : Nat → BitVec 8) : List (BitVec 64) :=
  List.ofFn (n := nb + 36) fun t => inputValG s nb bytes t.val

theorem mkInputsG_length (s : St) (nb : Nat) (bytes : Nat → BitVec 8) : (mkInputsG s nb bytes).length = nb + 36 := by
  simp [mkInputsG]

theorem mkInputsG_getD (s : St) (nb : Nat) (bytes : Nat → BitVec 8) (t : Nat) (ht : t < nb + 36) :
    (mkInputsG s nb bytes).getD t 0 = inputValG s nb bytes t := by
  unfold mkInputsG
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [ht]

theorem σ0G_bounded (R : Region) (nb : Nat) : (σ0G R nb).Bounded (nb + 36) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r i h
    cases r with
    | x k => simp only [σ0G, Option.some.injEq] at h; omega
    | sp => simp only [σ0G, Option.some.injEq] at h; omega
  · intro a b c d h
    simp only [σ0G, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · intro g j i k h
    simp only [σ0G] at h
    split at h
    · next hc => simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · cases h

theorem agrees_σ0G (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (s : St) (R : Region) (nb : Nat)
    (bytes : Nat → BitVec 8) (hI : ∀ j, j < nb → regionByte mapping pinv s R j = some (bytes j)) :
    Agrees mapping pinv (mkInputsG s nb bytes) (σ0G R nb) s := by
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

theorem mkInputsG_bytes (s : St) (nb : Nat) (bytes : Nat → BitVec 8) :
    ∀ i, i < nb → ((mkInputsG s nb bytes).getD i 0).toNat < 256 := by
  intro i hi
  rw [mkInputsG_getD s nb bytes i (by omega)]
  simp only [inputValG, if_pos hi, BitVec.toNat_setWidth]
  have := (bytes i).isLt
  omega

#print axioms agrees_σ0G

/-! ## Multi-region entry agreement: bytes of R_0, then R_1, …, then x0..x30, sp, N Z C V -/

/-- Table position of byte j of region g in the concatenated region list (first match), from `base`. -/
def memBL : List (Region × Nat) → Nat → Region → Nat → Option (Nat × Nat)
  | [], _, _, _ => none
  | (R, nb) :: t, base, g, j => if g = R ∧ j < nb then some (base + j, 0) else memBL t (base + nb) g j

def totalL (rs : List (Region × Nat)) : Nat := (rs.map (·.2)).sum

theorem memBL_spec : ∀ (rs : List (Region × Nat)) (base : Nat) (g : Region) (j i k : Nat),
    memBL rs base g j = some (i, k) → k = 0 ∧ base ≤ i ∧ i < base + totalL rs := by
  intro rs
  induction rs with
  | nil => intro base g j i k h; simp [memBL] at h
  | cons p t ih =>
    obtain ⟨R, nb⟩ := p
    intro base g j i k h
    simp only [memBL] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, by omega, ?_⟩
      simp only [totalL, List.map_cons, List.sum_cons]; omega
    · obtain ⟨hk, h1, h2⟩ := ih (base + nb) g j i k h
      refine ⟨hk, by omega, ?_⟩
      simp only [totalL, List.map_cons, List.sum_cons] at h2 ⊢; omega

/-- Entry symbolic state for a region list. -/
def σ0L (rs : List (Region × Nat)) : Sym where
  regs := fun r => match r with | .x i => some (totalL rs + i.val) | .sp => some (totalL rs + 31)
  nzcv := some (totalL rs + 32, totalL rs + 33, totalL rs + 34, totalL rs + 35)
  memB := fun g j => memBL rs 0 g j

/-- The entry inputs: `bytes t` for the t-th region byte (t < totalL rs), then registers and flags. -/
def mkInputsL (s : St) (rs : List (Region × Nat)) (bytes : Nat → BitVec 8) : List (BitVec 64) :=
  mkInputsG s (totalL rs) bytes

theorem σ0L_bounded (rs : List (Region × Nat)) : (σ0L rs).Bounded (totalL rs + 36) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r i h
    cases r with
    | x k => simp only [σ0L, Option.some.injEq] at h; omega
    | sp => simp only [σ0L, Option.some.injEq] at h; omega
  · intro a b c d h
    simp only [σ0L, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · intro g j i k h
    have := memBL_spec rs 0 g j i k h
    omega

/-- The multi-region entry agreement: `hI` says each tracked region byte is the corresponding `bytes`. -/
theorem agrees_σ0L (mapping : BitVec 64 → Option Nat) (pinv : Nat → Nat) (s : St)
    (rs : List (Region × Nat)) (bytes : Nat → BitVec 8)
    (hI : ∀ g j i k, memBL rs 0 g j = some (i, k) → regionByte mapping pinv s g j = some (bytes i)) :
    Agrees mapping pinv (mkInputsL s rs bytes) (σ0L rs) s := by
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

#print axioms agrees_σ0L
#print axioms ret_reg_gen

end ArmCertValue
