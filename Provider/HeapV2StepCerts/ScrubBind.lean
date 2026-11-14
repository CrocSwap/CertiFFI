-- Memory (B1 (c), / e01e): the epilogue scrub as constants.
-- * x0..x17 = 0 on every state 350..357 (MOVZ Xd, #0 at 332..349 are ValBind movz0 effects; nothing writes x0..x17 after).
-- * ZBind: PSTATE.Z = 1 on every state 351..357. Produced at 350 by the TST x1, #7 effect (x1 = 0 there), kept by the
--   NZCV frames of steps 351..356 (MemRE for the memory steps 351..355, TailWE.ClassTailWFAt for the ADD sp at 356).
--   Per flag: N/C/V (B1b, the TST root extension) add NBind/CBind/VBind beside it without touching any R type.
import HeapV2StepCerts.ValBindX1
import HeapV2StepCerts.Flags
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
namespace HeapV2StepCerts.ValBind
open HeapV2StepCerts.RegBind ArmBridge.Draft

theorem bind_zero {k : Nat} {r : Reg} (hk : (r, 0, (0 : Int)) ∈ vtab k) {q : Inputs} {x : NativeState}
    (vb : ValBind q k x) : regVal x r = 0#64 := by
  have h := vb.1 _ hk
  simpa [vpin] using h

theorem scrub_rows : ∀ j < 8, ∀ i : Fin 18, ((.x (Fin.castLE (by decide) i) : Reg), 0, (0 : Int)) ∈ vtab (350 + j) := by
  decide +kernel

/-- The scrub: x0..x17 = 0 on every state from 350 (the TST) to 357 (the RET). -/
theorem scrub_at {k : Nat} (lo : 350 ≤ k) (hi : k ≤ 357) {q : Inputs} {x : NativeState} (vb : ValBind q k x)
    (i : Fin 18) : regVal x (.x (Fin.castLE (by decide) i)) = 0#64 := by
  have h := scrub_rows (k - 350) (by omega) i
  rw [show 350 + (k - 350) = k by omega] at h
  exact bind_zero h vb

/-- The scrubbed registers at the RET state 357. -/
theorem scrub_at_357 {q : Inputs} {x : NativeState} (vb : ValBind q 357 x) (i : Fin 18) :
    regVal x (.x (Fin.castLE (by decide) i)) = 0#64 :=
  scrub_at (by decide) (by decide) vb i

/-- PSTATE.Z = 1 on the states 351..357. -/
def ZBind (k : Nat) (x : NativeState) : Prop := 351 ≤ k → k ≤ 357 → x.regs.PSTATE.Z = 1#1

theorem zbind_init (x : NativeState) : ZBind 0 x := fun h => absurd h (by decide)

/-- Produced at 350: TST x1, #7 with x1 = 0 sets Z. -/
theorem zbind_350 {q : Inputs} {s f : NativeState} (vb : ValBind q 350 s) (eff : VEff 350 s f) : ZBind (350 + 1) f := by
  intro _ _
  have he : effAt 350 = .tst 1 := by decide +kernel
  unfold VEff at eff; rw [he] at eff
  exact eff.mpr (by rw [x1_at_350 vb]; decide)

/-- Kept by an NZCV frame (steps 351..356). -/
theorem zbind_keep {k : Nat} {s f : NativeState} (lo : 351 ≤ k) (h : ZBind k s)
    (fl : Flags.nzcv f.regs = Flags.nzcv s.regs) : ZBind (k + 1) f := by
  intro _ hi
  have hz := congrArg (fun t => t.2.1) fl
  simp only [Flags.nzcv] at hz
  rw [hz]; exact h lo (by omega)

/-- Vacuous outside 351..357 (every other step carries it for free). -/
theorem zbind_out {k : Nat} (f : NativeState) (hk : k < 350 ∨ 357 ≤ k) : ZBind (k + 1) f :=
  fun lo hi => absurd hk (by omega)

#print axioms scrub_at_357
#print axioms zbind_350
#print axioms zbind_keep
end HeapV2StepCerts.ValBind
