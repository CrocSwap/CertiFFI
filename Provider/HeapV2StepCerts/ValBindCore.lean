-- Memory (certiffi P1,): value binding for the heap-v2 normal path's branch decisions.
-- Generic part: entry inputs x2/x3, the normal-path guard, value bindings (pin 0 = constant 0,
-- pin 1 = entry x2, pin 2 = entry x3, carried like RegBind), the B.cond decision at each state,
-- and the value effects of the flag setters / MOVZ #32 (VEff).
import HeapV2StepCerts.RegBindCore
import Crypto.BcondCore
import Crypto.CruxCbz
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
namespace HeapV2StepCerts.ValBind
open HeapV2StepCerts.RegBind

/-- Entry values of x2 (length) and x3 (the second length) the guards test. -/
structure Inputs where
  x2 : BitVec 64
  x3 : BitVec 64

/-- Value pins: 0 is the constant 0, 1 the entry x2, 2 the entry x3. -/
def vpin (q : Inputs) : Nat → Nat
  | 0 => 0
  | 1 => q.x2.toNat
  | _ => q.x3.toNat

/-- The value effect of one step (only the steps whose values feed a decision). -/
inductive Eff where
  | none
  | subs (d n : Fin 31) (imm : Nat)
  | cmp (n : Fin 31) (imm : Nat)
  | tst (n : Fin 31)
  | movz32 (d : Fin 31)
  | movz0 (d : Fin 31)
  deriving DecidableEq, Repr

def Eff.holds : Eff → St → St → Prop
  | .none, _, _ => True
  | .subs d n imm, s, f => regVal f (.x d) = regVal s (.x n) - BitVec.ofNat 64 imm ∧
      (f.regs.PSTATE.Z = 1#1 ↔ (regVal s (.x n)).toNat = imm) ∧
      (f.regs.PSTATE.C = 1#1 ↔ imm ≤ (regVal s (.x n)).toNat)
  | .cmp n imm, s, f => (f.regs.PSTATE.Z = 1#1 ↔ (regVal s (.x n)).toNat = imm) ∧
      (f.regs.PSTATE.C = 1#1 ↔ imm ≤ (regVal s (.x n)).toNat)
  | .tst n, s, f => (f.regs.PSTATE.Z = 1#1 ↔ regVal s (.x n) &&& 7#64 = 0#64)
  | .movz32 d, _, f => regVal f (.x d) = 32#64
  | .movz0 d, _, f => regVal f (.x d) = 0#64

/-- Effects read the source only through its GPRs, so they move across the actual fetch. -/
theorem Eff.of_prefix {e : Eff} {x f y : St} (gpr : f.regs.gpr = x.regs.gpr) (h : e.holds f y) : e.holds x y := by
  have rv : ∀ i : Fin 31, regVal f (.x i) = regVal x (.x i) := fun i => by simp only [regVal, gpr]
  cases e with
  | none => trivial
  | subs d n imm => simpa only [Eff.holds, rv] using h
  | cmp n imm => simpa only [Eff.holds, rv] using h
  | tst n => simpa only [Eff.holds, rv] using h
  | movz32 d => exact h
  | movz0 d => exact h

/-- A value binding derivable at the next step through the step's effect. -/
def effDerives (e : Eff) (bs : List Bind) (b : Bind) : Bool :=
  match e with
  | .movz32 d => b == (.x d, 0, 32)
  | .movz0 d => b == (.x d, 0, 0)
  | .subs d n imm => b.1 == .x d && bs.any fun b' => b'.1 == .x n && b'.2.1 == b.2.1 && b'.2.2 - imm == b.2.2
  | _ => false

theorem ofInt_sub_ofNat (a : Int) (m : Nat) :
    BitVec.ofInt 64 a - BitVec.ofNat 64 m = BitVec.ofInt 64 (a - m) := by
  rw [show BitVec.ofNat 64 m = BitVec.ofInt 64 (m : Int) by simp]
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- The value-binding carry: each next binding is kept (Derives under the RegBind update) or produced by
the step's value effect. -/
theorem carry_vals {pinv : Nat → Nat} (h0 : pinv 0 = 0) {us : List (Reg × Upd)} {e : Eff} {bs bs' : List Bind}
    {x y : St} (ok : bs'.all (fun b => Derives us bs b || effDerives e bs b) = true)
    (holds : Holds us x y) (eff : e.holds x y) (bound : BindsHold pinv bs x) : BindsHold pinv bs' y := by
  intro b member
  have d := List.all_eq_true.1 ok b member
  simp only [Bool.or_eq_true] at d
  rcases d with d | d
  · exact carry (bs' := [b]) (by simp [d]) holds bound b (List.mem_singleton_self b)
  · unfold effDerives at d
    split at d
    · next dd =>
      have hb : b = (.x dd, 0, 32) := by simpa using d
      subst hb
      show regVal y (.x dd) = BitVec.ofInt 64 ((pinv 0 : Int) + 32)
      rw [h0]; exact eff
    · next dd =>
      have hb : b = (.x dd, 0, 0) := by simpa using d
      subst hb
      show regVal y (.x dd) = BitVec.ofInt 64 ((pinv 0 : Int) + 0)
      rw [h0]; exact eff
    · next dd nn imm =>
      simp only [Bool.and_eq_true, beq_iff_eq] at d
      obtain ⟨hd, d⟩ := d
      obtain ⟨b', mem', cond⟩ := List.any_eq_true.1 d
      simp only [Bool.and_eq_true, beq_iff_eq] at cond
      obtain ⟨⟨hn, hp⟩, hc⟩ := cond
      rw [hd, eff.1, ← hn, bound b' mem', ofInt_sub_ofNat, hp, ← hc]
      congr 1; omega
    · exact absurd d (by simp)

/-- The branch decision table: at a B.cond step, its condition and whether the path takes it. -/
abbrev DecRow := Nat × BitVec 4 × Bool

def Decision (rows : List DecRow) (k : Nat) (x : St) : Prop :=
  ∀ d ∈ rows, d.1 = k → (Crypto.BcondCore.bcondC d.2.1 x.regs ↔ d.2.2 = true)

theorem bcond1 (r : ArmFull.Regs) : Crypto.BcondCore.bcondC 1#4 r ↔ ¬ r.PSTATE.Z = 1#1 := by
  unfold Crypto.BcondCore.bcondC; simp [Sail.BitVec.join1, Sail.BitVec.access]; decide
theorem bcond3 (r : ArmFull.Regs) : Crypto.BcondCore.bcondC 3#4 r ↔ ¬ r.PSTATE.C = 1#1 := by
  unfold Crypto.BcondCore.bcondC; simp [Sail.BitVec.join1, Sail.BitVec.access]; decide

/-- CBZ (64-bit) tests the register for zero. -/
theorem cbz_iff (Rt : BitVec 5) (hRt : Rt.toNat < 31) (t : St) :
    Crypto.CruxCbz.cbzC 1#1 Rt t ↔ t.regs.gpr[(GPRSummary.key Rt.toNat).val] = 0#64 := by
  unfold Crypto.CruxCbz.cbzC
  have h : ¬ ((Rt.toNat : Nat) : Int) = 31 := by omega
  simp [h, IsZero, Sail.BitVec.castWidth, Sail.BitVec.extractLsb, Sail.Int.toNatChecked]
  have hx : ∀ g : BitVec 64, BitVec.extractLsb 63 0 g = g := fun g => by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb, BitVec.extractLsb'_toNat]
  simp only [BEq.beq, decide_eq_true_eq]
  constructor
  · intro h; rw [← hx t.regs.gpr[(GPRSummary.key Rt.toNat).val]]; exact h
  · intro h; exact (hx _).trans h

#print axioms carry_vals
#print axioms bcond1
#print axioms cbz_iff
end HeapV2StepCerts.ValBind
