-- Memory: the trap paths' branch decisions. Trap path L (L = 1, 2, 4, 6, 8, 10) runs the normal
-- path's guard prefix k = 0 .. L-1; every guard passes except the last (k = L-1), which is taken to certiffi_trap.
-- ValBindT L = the normal path's value bindings with the trap path's decision rows; TrapPath L = its input condition.
import HeapV2StepCerts.ValBind
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
namespace HeapV2StepCerts.ValBind
open HeapV2StepCerts.RegBind ArmBridge.Draft

/-- Trap path L's input condition: the guards before k = L-1 pass, the guard at L-1 fails. -/
def TrapPath : Nat → HeapV2E17.Pins → Inputs → Prop
  | 1, p, _ => BitVec.ofInt 64 (p.x0 : Int) = 0#64
  | 2, p, _ => BitVec.ofInt 64 (p.x0 : Int) ≠ 0#64 ∧ BitVec.ofInt 64 (p.x1 : Int) = 0#64
  | 4, p, _ => BitVec.ofInt 64 (p.x0 : Int) ≠ 0#64 ∧ BitVec.ofInt 64 (p.x1 : Int) ≠ 0#64 ∧
      ¬ BitVec.ofInt 64 (p.x0 : Int) &&& 7#64 = 0#64
  | 6, p, _ => BitVec.ofInt 64 (p.x0 : Int) ≠ 0#64 ∧ BitVec.ofInt 64 (p.x1 : Int) ≠ 0#64 ∧
      BitVec.ofInt 64 (p.x0 : Int) &&& 7#64 = 0#64 ∧ ¬ BitVec.ofInt 64 (p.x1 : Int) &&& 7#64 = 0#64
  | 8, p, q => BitVec.ofInt 64 (p.x0 : Int) ≠ 0#64 ∧ BitVec.ofInt 64 (p.x1 : Int) ≠ 0#64 ∧
      BitVec.ofInt 64 (p.x0 : Int) &&& 7#64 = 0#64 ∧ BitVec.ofInt 64 (p.x1 : Int) &&& 7#64 = 0#64 ∧ q.x2.toNat < 32
  | 10, p, q => BitVec.ofInt 64 (p.x0 : Int) ≠ 0#64 ∧ BitVec.ofInt 64 (p.x1 : Int) ≠ 0#64 ∧
      BitVec.ofInt 64 (p.x0 : Int) &&& 7#64 = 0#64 ∧ BitVec.ofInt 64 (p.x1 : Int) &&& 7#64 = 0#64 ∧
      32 ≤ q.x2.toNat ∧ q.x3 ≠ 32#64
  | _, _, _ => False

/-- Trap path L's B.cond rows: the normal rows before L-1, then the taken guard at L-1. -/
def trapRows (L : Nat) : List DecRow :=
  decRows.filter (·.1 < L - 1) ++
    (if L = 4 then [(3, 1#4, true)] else if L = 6 then [(5, 1#4, true)] else
     if L = 8 then [(7, 3#4, true)] else if L = 10 then [(9, 1#4, true)] else [])

def ValBindT (L : Nat) (q : Inputs) (k : Nat) (x : NativeState) : Prop :=
  BindsHold (vpin q) (vtab k) x ∧ Decision (trapRows L) k x

theorem decT_none {rows : List DecRow} {k : Nat} {x : NativeState} (h : rows.all (·.1 ≠ k) = true) : Decision rows k x := by
  intro d member hd
  have := List.all_eq_true.1 h d member
  simp only [ne_eq, decide_eq_true_eq] at this
  exact absurd hd this

theorem initialT (L : Nat) (h : (trapRows L).all (·.1 ≠ 0) = true) (s : NativeState) :
    ValBindT L ⟨regVal s (.x 2), regVal s (.x 3)⟩ 0 s :=
  ⟨(initial s).1, decT_none h⟩

private theorem row_eq {rows : List DecRow} {k : Nat} {c : BitVec 4} {t : Bool} {r : DecRow}
    (hrow : rows.all (fun r => r.1 != k || r == (k, c, t)) = true) (member : r ∈ rows) (hr : r.1 = k) : r = (k, c, t) := by
  have hr' := List.all_eq_true.1 hrow r member
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hr'
  rcases hr' with h | h
  · exact absurd hr h
  · exact h

/-- TST Xn, #7; B.NE with the taken bit t ↔ misaligned. -/
theorem decT_tst {k : Nat} (rows : List DecRow) (t : Bool) (n : Fin 31) (i : Nat) {p : HeapV2E17.Pins} {s f : NativeState}
    (he : effAt k = .tst n) (hrow : rows.all (fun r => r.1 != k + 1 || r == (k + 1, 1#4, t)) = true)
    (hb : ((.x n : Reg), i, (0 : Int)) ∈ binds k)
    (cnd : BitVec.ofInt 64 ((HeapV2E17.pin p i : Int)) &&& 7#64 = 0#64 ↔ t = false)
    (rb : RegBind.RegBind p k s) (eff : VEff k s f) : Decision rows (k + 1) f := by
  intro r member hr
  rw [row_eq hrow member hr]
  unfold VEff at eff; rw [he] at eff
  have hv := rb _ hb
  simp only [Int.add_zero] at hv
  have eff' : f.regs.PSTATE.Z = 1#1 ↔ regVal s (.x n) &&& 7#64 = 0#64 := eff
  rw [bcond1, eff', hv, cnd]
  cases t <;> simp

/-- CMP x2, #32; B.LO with the taken bit t ↔ x2 < 32. -/
theorem decT_cmp_lo {k : Nat} (rows : List DecRow) (t : Bool) {q : Inputs} {s f : NativeState}
    (he : effAt k = .cmp 2 32) (hrow : rows.all (fun r => r.1 != k + 1 || r == (k + 1, 3#4, t)) = true)
    (hb : ((.x 2 : Reg), 1, (0 : Int)) ∈ vtab k) (cnd : 32 ≤ q.x2.toNat ↔ t = false)
    (vals : BindsHold (vpin q) (vtab k) s) (eff : VEff k s f) : Decision rows (k + 1) f := by
  intro r member hr
  rw [row_eq hrow member hr]
  unfold VEff at eff; rw [he] at eff
  have hv := vals _ hb
  simp only at hv
  have hc := eff.2
  rw [hv, show vpin q 1 = q.x2.toNat from rfl, toNat_pin _ q.x2.isLt] at hc
  rw [bcond3, hc, cnd]
  cases t <;> simp

/-- CMP x3, #32; B.NE with the taken bit t ↔ x3 ≠ 32. -/
theorem decT_cmp_ne3 {k : Nat} (rows : List DecRow) (t : Bool) {q : Inputs} {s f : NativeState}
    (he : effAt k = .cmp 3 32) (hrow : rows.all (fun r => r.1 != k + 1 || r == (k + 1, 1#4, t)) = true)
    (hb : ((.x 3 : Reg), 2, (0 : Int)) ∈ vtab k) (cnd : q.x3.toNat = 32 ↔ t = false)
    (vals : BindsHold (vpin q) (vtab k) s) (eff : VEff k s f) : Decision rows (k + 1) f := by
  intro r member hr
  rw [row_eq hrow member hr]
  unfold VEff at eff; rw [he] at eff
  have hv := vals _ hb
  simp only at hv
  have hz := eff.1
  rw [hv, show vpin q 2 = q.x3.toNat from rfl, toNat_pin _ q.x3.isLt] at hz
  rw [bcond1, hz, cnd]
  cases t <;> simp

/-- CBZ on a pinned entry register with taken bit t ↔ the pin is 0. -/
theorem cbzT_pin {k : Nat} (t : Bool) (Rt : BitVec 5) (n : Fin 31) (i : Nat) {p : HeapV2E17.Pins} {x : NativeState}
    (hkey : GPRSummary.key Rt.toNat = n ∧ Rt.toNat < 31) (hb : ((.x n : Reg), i, (0 : Int)) ∈ binds k)
    (cnd : BitVec.ofInt 64 ((HeapV2E17.pin p i : Int)) = 0#64 ↔ t = true) (rb : RegBind.RegBind p k x) :
    (Crypto.CruxCbz.cbzC 1#1 Rt x ↔ t = true) := by
  rw [cbz_iff Rt hkey.2]
  obtain ⟨hk, _⟩ := hkey
  subst hk
  have hv := rb _ hb
  simp only [Int.add_zero] at hv
  change regVal x (.x (GPRSummary.key Rt.toNat)) = 0#64 ↔ _
  rw [hv, cnd]

theorem x3_iff {q : Inputs} : q.x3.toNat = 32 ↔ q.x3 = 32#64 :=
  ⟨fun h => BitVec.eq_of_toNat_eq (by simpa using h), fun h => by rw [h]; rfl⟩

#print axioms initialT
#print axioms decT_tst
#print axioms decT_cmp_lo
#print axioms decT_cmp_ne3
#print axioms cbzT_pin
end HeapV2StepCerts.ValBind
