import TranslateValue.HP1Certs

/-! H-P1 (, /): functional correctness of the heap-v2 value table D.
On the actual table `evalDefs inputs D`, with the 32 input bytes as inputs 0..31, the four output words
(ids 733, 738, 743, 748; region O bytes 0..31 per `HeapV2Plan.outs`) hold I² mod p as little-endian 64-bit
limbs, where I = Σ 2^(8 j) · byte_j and p = 2^256 − 2^32 − 977 (secp256k1).

Proof: the normalized symbolic table is a literal (`HP1Tables`), kernel-checked entry by entry against the
normalizer's one-step rule (`checkP_sound`), so every value equals its polynomial. Seven quotient variables are
pinned by bound certificates (`PosCert`, kernel-checked in `HP1Certs`): Q565 = Q580 = Q591 = 0 (local),
Q661 = 0 (the 512-bit square has no carry out: Σ 2^(64i) r_i + (U − I)(U + I) ≡ U² − 2^512·Q661, U = 2^256 − 1),
Q708 = Q709 = 0, Q748 = 1 (no final borrow, by cases on the reduction carry 730). With these, the kernel
checks the ideal identity Σ 2^(64i) out_i − I² = p·K, and a certificate (again by cases on 730) gives
Σ 2^(64i) out_i ≤ p − 1. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateValue.HP1
open ArmCertValue

def p256k1 : Nat := 2 ^ 256 - 2 ^ 32 - 977

/-- The input value: the 32 input bytes, little-endian. -/
def inVal (inputs : List (BitVec 64)) : Nat :=
  ((List.range 32).map fun j => 2 ^ (8 * j) * (inputs.getD j 0).toNat).sum

/-- The output value: the four output words, little-endian. -/
def outVal (vals : List (BitVec 64)) : Nat :=
  (vals.getD 733 0).toNat + 2 ^ 64 * (vals.getD 738 0).toNat + 2 ^ 128 * (vals.getD 743 0).toNat +
    2 ^ 192 * (vals.getD 748 0).toNat

theorem D_len : HeapV2Plan.D.length = 706 := by decide +kernel
theorem iw_len : iw.length = 68 := by decide +kernel
theorem iw_at : ∀ i, i < 68 → iw.getD i (64, 0) = if i < 32 then (8, 0) else (64, 0) := by decide +kernel

theorem D_wf : WF 68 HeapV2Plan.D = true :=
  WF_of_all 68 HeapV2Plan.D (fun k hk => WF_all k (by rw [D_len] at hk; exact hk))

theorem W_eq : widthTable iw HeapV2Plan.D = W :=
  checkW_eq iw HeapV2Plan.D W W_head (fun k hk => W_all k (by rw [D_len] at hk; exact hk))

theorem le_of_bound (K C s m : Int) (hK : 0 < K) (hC : C < K * (m + 1)) (h : 0 ≤ C - K * s) : s ≤ m := by
  rcases Int.lt_or_le m s with hs | hs
  · have : K * (m + 1) ≤ K * s := Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hK)
    omega
  · exact hs

theorem eval_lin (env : Nat → Int) (c : Nat → Int) : ∀ xs : List Nat,
    Poly.eval env (xs.map fun j => (c j, [j])) = (xs.map fun j => c j * env j).sum
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, Poly.eval_cons, Mono.eval_cons, Mono.eval_nil, Int.mul_one]
    rw [eval_lin env c xs]

theorem sum_cast (f : Nat → Nat) : ∀ xs : List Nat, (((xs.map f).sum : Nat) : Int) = (xs.map fun j => (f j : Int)).sum
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, List.sum_cons]; push_cast; rw [sum_cast f xs]

section
variable (inputs : List (BitVec 64)) (hlen : inputs.length = 68)
  (hbytes : ∀ i, i < 32 → (inputs.getD i 0).toNat < 256)

include hlen hbytes in
theorem hin : ∀ i, i < inputs.length → WidthOK (inputs.getD i 0) (iw.getD i (64, 0)) := by
  intro i hi
  rw [hlen] at hi
  rw [iw_at i hi]
  split
  · next h => exact ⟨by have := hbytes i h; simpa using this, by simp⟩
  · exact widthOK_64 _

include hlen hbytes in
theorem L_sound : ∀ t, t < inputs.length + HeapV2Plan.D.length →
    (((evalDefs inputs HeapV2Plan.D).getD t 0).toNat : Int) = Poly.eval (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) (L.getD t []) :=
  checkP_sound inputs HeapV2Plan.D iw W L (by rw [iw_len, hlen]) (hin inputs hlen hbytes)
    (by rw [hlen]; exact D_wf) (by rw [hlen, D_len]; decide) W_eq (by rw [hlen]; exact L_head)
    (fun k hk => by rw [hlen]; exact L_all k (by rw [D_len] at hk; exact hk))

include hlen hbytes in
theorem ctx_ok : ctx.Sound (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) := by
  have hc : (⟨inputs.length, HeapV2Plan.D, W, L⟩ : Ctx) = ctx := by rw [hlen]; rfl
  have := ctx_sound inputs HeapV2Plan.D iw W L (by rw [iw_len, hlen]) (hin inputs hlen hbytes)
    (by rw [hlen]; exact D_wf) (by rw [hlen, D_len]; decide) W_eq (L_sound inputs hlen hbytes)
    (by rw [hlen, D_len]; decide +kernel)
  rw [hc] at this; exact this

/-- A quotient variable is ≥ 0. -/
theorem quot_nonneg (hs : ctx.Sound (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D))) (t : Nat) : 0 ≤ (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) (BIG + t) := by
  have := hs.atom (.quot t); simpa [Atom.poly, Poly.eval_var] using this

theorem zero_of_chk (hs : ctx.Sound (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D))) (t : Nat) (K C : Int) (subs : List (Nat × Int)) (ce : Cert)
    (hK : 0 < K) (hC : C < K * (0 + 1))
    (h : Cert.check ctx (Poly.sub (Poly.const C) (Poly.scale K (Poly.var (BIG + t)))) subs ce = true)
    (hsub : ∀ s ∈ subs, (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) s.1 = s.2) : (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) (BIG + t) = 0 := by
  have := Cert.sound ctx _ hs _ subs ce h hsub
  rw [Poly.eval_sub, Poly.eval_const, Poly.eval_scale, Poly.eval_var] at this
  have := le_of_bound K C _ 0 hK hC this
  have := quot_nonneg inputs hs t
  omega

include hlen hbytes in
/-- The quotient facts. -/
theorem quots :
    (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) (BIG + 565) = 0 ∧ (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) (BIG + 580) = 0 ∧ (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) (BIG + 591) = 0 ∧ (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) (BIG + 661) = 0 ∧
      (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) (BIG + 708) = 0 ∧ (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) (BIG + 709) = 0 ∧ (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) (BIG + 748) = 1 := by
  have hs := ctx_ok inputs hlen hbytes
  have h565 := zero_of_chk inputs hs 565 _ _ _ _ (by decide) (by decide) chk_q565 (by simp [subs_q565])
  have h580 := zero_of_chk inputs hs 580 _ _ _ _ (by decide) (by decide) chk_q580 (by simp [subs_q580])
  have h591 := zero_of_chk inputs hs 591 _ _ _ _ (by decide) (by decide) chk_q591 (by simp [subs_q591])
  have h661 := zero_of_chk inputs hs 661 _ _ _ _ (by decide) (by decide) chk_q661
    (by simp only [subs_q661, List.forall_mem_cons]; exact ⟨h565, h580, h591, by simp⟩)
  have h708 := zero_of_chk inputs hs 708 _ _ _ _ (by decide) (by decide) chk_q708
    (by simp only [subs_q708, List.forall_mem_cons]; exact ⟨h565, h580, h591, h661, by simp⟩)
  have h709 := zero_of_chk inputs hs 709 _ _ _ _ (by decide) (by decide) chk_q709
    (by simp only [subs_q709, List.forall_mem_cons]; exact ⟨h565, h580, h591, h661, h708, by simp⟩)
  have z6 : ∀ s ∈ subs_q748lo, (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) s.1 = s.2 := by
    simp only [subs_q748lo, List.forall_mem_cons]; exact ⟨h565, h580, h591, h661, h708, h709, by simp⟩
  have lo := Cert.sound ctx _ hs _ _ _ chk_q748lo z6
  rw [Poly.eval_add, Poly.eval_scale, Poly.eval_var, Poly.eval_const] at lo
  have lo := one_le_of_bound K_q748lo C_q748lo _ (by decide) (by decide) lo
  have hi := Cert.sound ctx _ hs _ _ _ chk_q748hi z6
  rw [Poly.eval_sub, Poly.eval_const, Poly.eval_scale, Poly.eval_var] at hi
  have hi := le_of_bound K_q748hi C_q748hi _ 1 (by decide) (by decide) hi
  exact ⟨h565, h580, h591, h661, h708, h709, by omega⟩

include hlen hbytes in
theorem eval_S : Poly.eval (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) Spoly = (outVal (evalDefs inputs HeapV2Plan.D) : Int) := by
  have hL := L_sound inputs hlen hbytes
  have l : ∀ t, t < 774 → Poly.eval (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) (L.getD t []) = (((evalDefs inputs HeapV2Plan.D).getD t 0).toNat : Int) := by
    intro t ht; rw [hL t (by rw [hlen, D_len]; exact ht)]
  unfold Spoly
  rw [Poly.eval_append, Poly.eval_append, Poly.eval_append, Poly.eval_scale, Poly.eval_scale, Poly.eval_scale,
    Poly.eval_scale]
  rw [l 733 (by decide), l 738 (by decide), l 743 (by decide), l 748 (by decide)]
  have p1 : (((2 ^ 64 : Nat)) : Int) = 18446744073709551616 := by decide
  have p2 : (((2 ^ 128 : Nat)) : Int) = 340282366920938463463374607431768211456 := by decide
  have p3 : (((2 ^ 192 : Nat)) : Int) = 6277101735386680763835789423207666416102355444464034512896 := by decide
  unfold outVal
  rw [Int.natCast_add, Int.natCast_add, Int.natCast_add, Int.natCast_mul, Int.natCast_mul, Int.natCast_mul, p1, p2, p3]
  omega

set_option maxRecDepth 4000 in
include hlen in
theorem eval_I : Poly.eval (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) Ipoly = (inVal inputs : Int) := by
  unfold Ipoly
  rw [eval_lin, inVal, sum_cast]
  have hf : ∀ j ∈ List.range 32, (2 : Int) ^ (8 * j) * envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D) j =
      (((2 ^ (8 * j) * (inputs.getD j 0).toNat : Nat)) : Int) := by
    intro j hj
    have hj : j < 32 := List.mem_range.1 hj
    rw [env_low inputs HeapV2Plan.D j (by unfold BIG; omega)]
    have : (evalDefs inputs HeapV2Plan.D).getD j 0 = inputs.getD j 0 := by
      unfold evalDefs extend; exact foldlApp_prefix _ _ _ _ _ (by omega)
    rw [this, Int.natCast_mul, Int.natCast_pow]; rfl
  exact congrArg List.sum (List.map_congr_left hf)

include hlen hbytes in
/-- **H-P1.** The heap-v2 value table squares modulo the secp256k1 prime. -/
theorem hp1_square : outVal (evalDefs inputs HeapV2Plan.D) = inVal inputs ^ 2 % p256k1 := by
  obtain ⟨h565, h580, h591, h661, h708, h709, h748⟩ := quots inputs hlen hbytes
  have hs := ctx_ok inputs hlen hbytes
  have zfin : ∀ s ∈ subs_fin, (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) s.1 = s.2 := by
    simp only [subs_fin, List.forall_mem_cons]
    exact ⟨h565, h580, h591, h661, h708, h709, h748, by simp⟩
  have fin := Poly.eval_of_eqF fin_ok (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D))
  rw [eval_substAll _ _ _ zfin, Poly.eval_sub, Poly.eval_mul, Poly.eval_scale, eval_S inputs hlen hbytes,
    eval_I inputs hlen] at fin
  have rng := Cert.sound ctx _ hs _ _ _ chk_range zfin
  rw [Poly.eval_sub, Poly.eval_const, Poly.eval_scale, eval_S inputs hlen hbytes] at rng
  have rng := le_of_bound K_range C_range _ (p256k1 - 1 : Nat) (by decide) (by decide) rng
  -- out = I² + p·k with 0 ≤ out ≤ p − 1, hence out = I² mod p
  have hp : (p256k1 : Int) = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
    decide
  have goal : ((outVal (evalDefs inputs HeapV2Plan.D) : Nat) : Int) = (((inVal inputs * inVal inputs) % p256k1 : Nat) : Int) := by
    push_cast
    rw [hp]
    have e : (inVal inputs : Int) * (inVal inputs : Int) =
        (outVal (evalDefs inputs HeapV2Plan.D) : Int) + 115792089237316195423570985008687907853269984665640564039457584007908834671663 *
          (-(Poly.eval (envOf inputs.length HeapV2Plan.D (evalDefs inputs HeapV2Plan.D)) Kfin)) := by
      rw [Int.mul_neg]; omega
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [Nat.pow_two]
  exact_mod_cast goal
/-! ### Per byte (: the Agrees memB clause for region O) -/

theorem pow256 (m : Nat) : (2 : Nat) ^ (8 * m) = 256 ^ m := by rw [Nat.pow_mul]

/-- Low limb: below byte 8, the higher limbs do not reach. -/
theorem byte_lo (w R k : Nat) (hk : k < 8) : (w + 2 ^ 64 * R) / 256 ^ k % 256 = w / 256 ^ k % 256 := by
  have e : 2 ^ 64 * R = 256 ^ k * (256 * (256 ^ (7 - k) * R)) := by
    rw [← pow256, ← pow256, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.mul_assoc, ← Nat.mul_assoc,
      ← Nat.pow_add, ← Nat.pow_add]
    congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.add_mul_mod_self_left]

/-- From byte 8 on, the low limb is gone. -/
theorem byte_hi (w R j : Nat) (hw : w < 2 ^ 64) (hj : 8 ≤ j) :
    (w + 2 ^ 64 * R) / 256 ^ j % 256 = R / 256 ^ (j - 8) % 256 := by
  have e : 256 ^ j = 2 ^ 64 * 256 ^ (j - 8) := by
    rw [show (2 : Nat) ^ 64 = 256 ^ 8 from rfl, ← Nat.pow_add]; congr 1; omega
  rw [e, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hw, Nat.zero_add]

theorem outs_at : ∀ j, j < 32 → HeapV2Plan.outs.getD j (0, 0) = ([733, 738, 743, 748].getD (j / 8) 0, j % 8) := by
  decide

include hlen hbytes in
/-- **H-P1, per output byte** (certiffi's target): output byte j = byte j of I² mod p. -/
theorem hp1_bytes : ∀ j, j < 32 →
    (((evalDefs inputs HeapV2Plan.D).getD (HeapV2Plan.outs.getD j (0, 0)).1 0 >>> (8 * (HeapV2Plan.outs.getD j (0, 0)).2)).setWidth 8)
      = BitVec.ofNat 8 ((inVal inputs ^ 2 % p256k1) / 256 ^ j) := by
  intro j hj
  rw [outs_at j hj, ← hp1_square inputs hlen hbytes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, pow256]
  have b0 := ((evalDefs inputs HeapV2Plan.D).getD 733 0).isLt
  have b1 := ((evalDefs inputs HeapV2Plan.D).getD 738 0).isLt
  have b2 := ((evalDefs inputs HeapV2Plan.D).getD 743 0).isLt
  have form : outVal (evalDefs inputs HeapV2Plan.D) =
      ((evalDefs inputs HeapV2Plan.D).getD 733 0).toNat + 2 ^ 64 * (((evalDefs inputs HeapV2Plan.D).getD 738 0).toNat +
        2 ^ 64 * (((evalDefs inputs HeapV2Plan.D).getD 743 0).toNat + 2 ^ 64 * ((evalDefs inputs HeapV2Plan.D).getD 748 0).toNat)) := by
    unfold outVal; simp only [Nat.reducePow] at *; omega
  rw [form, show (2 : Nat) ^ 8 = 256 from rfl]
  have hk : j % 8 < 8 := Nat.mod_lt _ (by decide)
  rcases (by omega : j / 8 = 0 ∨ j / 8 = 1 ∨ j / 8 = 2 ∨ j / 8 = 3) with h | h | h | h <;> rw [h]
  · rw [show j = j % 8 by omega, byte_lo _ _ _ hk]; simp
  · rw [byte_hi _ _ _ b0 (by omega), show j - 8 = j % 8 by omega, byte_lo _ _ _ hk]; simp
  · rw [byte_hi _ _ _ b0 (by omega), byte_hi _ _ _ b1 (by omega), show j - 8 - 8 = j % 8 by omega, byte_lo _ _ _ hk]; simp
  · rw [byte_hi _ _ _ b0 (by omega), byte_hi _ _ _ b1 (by omega), byte_hi _ _ _ b2 (by omega),
      show j - 8 - 8 - 8 = j % 8 by omega]; simp
end

#print axioms hp1_square
#print axioms hp1_bytes
end TranslateValue.HP1
