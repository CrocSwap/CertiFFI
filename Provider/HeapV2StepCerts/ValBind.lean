-- Memory (certiffi P1,): ValBind = value bindings + B.cond decisions, the normal-path guard, and the
-- decision lemmas the generated per-step carries / per-branch dec_k (ValBindSteps) instantiate.
import HeapV2StepCerts.ValBindData
import HeapV2StepCerts.RegBind
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
namespace HeapV2StepCerts.ValBind
open HeapV2StepCerts.RegBind ArmBridge.Draft

/-- The heap-v2 normal path's entry guard: exactly the outcomes of the six guard sites
(CBZ x0, CBZ x1, TST x0,#7; B.NE, TST x1,#7; B.NE, CMP x2,#32; B.LO, CMP x3,#32; B.NE). -/
def NormalPath (p : HeapV2E17.Pins) (q : Inputs) : Prop :=
  BitVec.ofInt 64 (p.x0 : Int) ≠ 0#64 ∧ BitVec.ofInt 64 (p.x1 : Int) ≠ 0#64 ∧
  BitVec.ofInt 64 (p.x0 : Int) &&& 7#64 = 0#64 ∧ BitVec.ofInt 64 (p.x1 : Int) &&& 7#64 = 0#64 ∧
  32 ≤ q.x2.toNat ∧ q.x3 = 32#64

/-- The ChainInv v4 field: value bindings and the B.cond decision at state k. -/
def ValBind (q : Inputs) (k : Nat) (x : NativeState) : Prop :=
  BindsHold (vpin q) (vtab k) x ∧ Decision decRows k x

/-- The value effect of step k (fetched/entry state s, successor f). -/
def VEff (k : Nat) (s f : NativeState) : Prop := (effAt k).holds s f

theorem VEff.of_prefix {k : Nat} {x f y : NativeState} (gpr : f.regs.gpr = x.regs.gpr) (h : VEff k f y) : VEff k x y :=
  Eff.of_prefix gpr h

theorem veff_none {k : Nat} (h : effAt k = .none) (s f : NativeState) : VEff k s f := by
  unfold VEff; rw [h]; trivial

theorem initial (s : NativeState) : ValBind ⟨regVal s (.x 2), regVal s (.x 3)⟩ 0 s := by
  refine ⟨?_, ?_⟩
  · intro b member
    have h0 : vtab 0 = [(.x 2, 1, 0), (.x 3, 2, 0)] := by decide
    rw [h0] at member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> simp [vpin]
  · intro d member hd
    exact absurd hd (by have := List.all_eq_true.1 (show decRows.all (·.1 ≠ 0) = true by decide) d member; simpa using this)

theorem dec_none {k : Nat} {x : NativeState} (h : decRows.all (·.1 ≠ k) = true) : Decision decRows k x := by
  intro d member hd
  have := List.all_eq_true.1 h d member
  simp only [ne_eq, decide_eq_true_eq] at this
  exact absurd hd this

theorem toNat_const {c : Int} (hc : 0 ≤ c ∧ c < 2 ^ 64) : (BitVec.ofInt 64 ((0 : Nat) + c)).toNat = c.toNat := by
  rw [BitVec.toNat_ofInt]; congr 1; rw [show ((0 : Nat) : Int) + c = c by omega]; exact Int.emod_eq_of_lt hc.1 hc.2

theorem toNat_pin (n : Nat) (hn : n < 2 ^ 64) : (BitVec.ofInt 64 ((n : Int) + 0)).toNat = n := by
  rw [Int.add_zero, BitVec.toNat_ofInt]; omega

/-- Loop step: SUBS Xd, Xn, #imm with Xn a known constant c, then B.NE. -/
theorem dec_subs {k : Nat} (d n : Fin 31) (imm : Nat) (t : Bool) (c : Int) {q : Inputs} {s f : NativeState}
    (he : effAt k = .subs d n imm) (hrow : decRows.all (fun r => r.1 != k + 1 || r == (k + 1, 1#4, t)) = true)
    (hb : (.x n, 0, c) ∈ vtab k) (ht : (0 ≤ c ∧ c < 2 ^ 64) ∧ t = !(decide (c = imm)))
    (vb : ValBind q k s) (eff : VEff k s f) : Decision decRows (k + 1) f := by
  intro r member hr
  have hr' := List.all_eq_true.1 hrow r member
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hr'
  rcases hr' with h | h
  · exact absurd hr h
  subst h
  unfold VEff at eff; rw [he] at eff
  have hv := vb.1 _ hb
  simp only at hv
  have hz := eff.2.1
  rw [hv, show vpin q 0 = 0 from rfl, toNat_const ht.1] at hz
  rw [bcond1, hz, ht.2]
  constructor
  · intro h; simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega
  · intro h; simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h; omega

/-- k = 6: CMP x2, #32; B.LO — not taken since the entry x2 ≥ 32. -/
theorem dec_cmp_lo {k : Nat} {p : HeapV2E17.Pins} {q : Inputs} {s f : NativeState}
    (he : effAt k = .cmp 2 32) (hrow : decRows.all (fun r => r.1 != k + 1 || r == (k + 1, 3#4, false)) = true)
    (hb : ((.x 2 : Reg), 1, (0 : Int)) ∈ vtab k)
    (np : NormalPath p q) (vb : ValBind q k s) (eff : VEff k s f) : Decision decRows (k + 1) f := by
  intro r member hr
  have hr' := List.all_eq_true.1 hrow r member
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hr'
  rcases hr' with h | h
  · exact absurd hr h
  subst h
  unfold VEff at eff; rw [he] at eff
  have hv := vb.1 _ hb
  simp only at hv
  have hc := eff.2
  rw [hv, show vpin q 1 = q.x2.toNat from rfl, toNat_pin _ q.x2.isLt] at hc
  rw [bcond3, hc.2 np.2.2.2.2.1]
  simp

/-- k = 8: CMP x3, #32; B.NE — not taken since the entry x3 = 32. -/
theorem dec_cmp_ne3 {k : Nat} {p : HeapV2E17.Pins} {q : Inputs} {s f : NativeState}
    (he : effAt k = .cmp 3 32) (hrow : decRows.all (fun r => r.1 != k + 1 || r == (k + 1, 1#4, false)) = true)
    (hb : ((.x 3 : Reg), 2, (0 : Int)) ∈ vtab k)
    (np : NormalPath p q) (vb : ValBind q k s) (eff : VEff k s f) : Decision decRows (k + 1) f := by
  intro r member hr
  have hr' := List.all_eq_true.1 hrow r member
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hr'
  rcases hr' with h | h
  · exact absurd hr h
  subst h
  unfold VEff at eff; rw [he] at eff
  have hv := vb.1 _ hb
  simp only at hv
  have hz := eff.1
  rw [hv, show vpin q 2 = q.x3.toNat from rfl, toNat_pin _ q.x3.isLt, np.2.2.2.2.2] at hz
  rw [bcond1, hz.2 rfl]
  simp

/-- k = 2 / 4: TST x0/x1, #7; B.NE — not taken since the pins are 8-byte aligned. -/
theorem dec_tst {k : Nat} (n : Fin 31) (i : Nat) {p : HeapV2E17.Pins} {s f : NativeState}
    (he : effAt k = .tst n) (hrow : decRows.all (fun r => r.1 != k + 1 || r == (k + 1, 1#4, false)) = true)
    (hb : ((.x n : Reg), i, (0 : Int)) ∈ binds k)
    (aligned : BitVec.ofInt 64 ((HeapV2E17.pin p i : Int)) &&& 7#64 = 0#64)
    (rb : RegBind.RegBind p k s) (eff : VEff k s f) : Decision decRows (k + 1) f := by
  intro r member hr
  have hr' := List.all_eq_true.1 hrow r member
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hr'
  rcases hr' with h | h
  · exact absurd hr h
  subst h
  unfold VEff at eff; rw [he] at eff
  have hv := rb _ hb
  simp only [Int.add_zero] at hv
  have eff' : f.regs.PSTATE.Z = 1#1 ↔ regVal s (.x n) &&& 7#64 = 0#64 := eff
  rw [bcond1, eff', hv, aligned]
  simp

/-- CBZ on a pinned entry register (x0 / x1): not taken since the pin is nonzero. -/
theorem cbz_pin {k : Nat} (Rt : BitVec 5) (n : Fin 31) (i : Nat) {p : HeapV2E17.Pins} {x : NativeState}
    (hkey : GPRSummary.key Rt.toNat = n ∧ Rt.toNat < 31) (hb : ((.x n : Reg), i, (0 : Int)) ∈ binds k)
    (nz : BitVec.ofInt 64 ((HeapV2E17.pin p i : Int)) ≠ 0#64) (rb : RegBind.RegBind p k x) :
    (Crypto.CruxCbz.cbzC 1#1 Rt x ↔ false = true) := by
  rw [cbz_iff Rt hkey.2]
  obtain ⟨hk, _⟩ := hkey
  subst hk
  have hv := rb _ hb
  simp only [Int.add_zero] at hv
  change regVal x (.x (GPRSummary.key Rt.toNat)) = 0#64 ↔ _
  rw [hv]; simp only [Bool.false_eq_true, iff_false]; exact nz

/-- CBZ on a register holding a known nonzero constant (x2 = 32). -/
theorem cbz_const {k : Nat} (Rt : BitVec 5) (n : Fin 31) (c : Int) {q : Inputs} {x : NativeState}
    (hkey : GPRSummary.key Rt.toNat = n ∧ Rt.toNat < 31) (hb : ((.x n : Reg), 0, c) ∈ vtab k)
    (hc : 0 < c ∧ c < 2 ^ 64) (vb : ValBind q k x) :
    (Crypto.CruxCbz.cbzC 1#1 Rt x ↔ false = true) := by
  rw [cbz_iff Rt hkey.2]
  obtain ⟨hk, _⟩ := hkey
  subst hk
  have hv := vb.1 _ hb
  change regVal x (.x (GPRSummary.key Rt.toNat)) = 0#64 ↔ _
  rw [hv]
  simp only [Bool.false_eq_true, iff_false]
  intro h
  have := congrArg BitVec.toNat h
  rw [show vpin q 0 = 0 from rfl, toNat_const ⟨by omega, hc.2⟩] at this
  simp at this; omega

#print axioms initial
#print axioms dec_subs
#print axioms dec_cmp_lo
#print axioms dec_cmp_ne3
#print axioms dec_tst
#print axioms cbz_pin
#print axioms cbz_const
end HeapV2StepCerts.ValBind
