-- CT2 (Heap v1.2): register frame along the trap guard prefix (upds k = [] for k < 10).
import HeapV2StepCerts.RegBind
set_option autoImplicit false
namespace CT2Heap
open HeapV2StepCerts.RegBind

/-- Every register (x0..x30, sp) of `x` equals its value in `E`. -/
def FrameAt (E x : ArmBridge.Draft.NativeState) : Prop := ∀ r : Reg, regVal x r = regVal E r

theorem frameAt_refl (E : ArmBridge.Draft.NativeState) : FrameAt E E := fun _ => rfl

theorem frame_carry {k : Nat} {E s f : ArmBridge.Draft.NativeState} (h : upds k = []) (holds : Holds (upds k) s f)
    (v : FrameAt E s) : FrameAt E f := fun r => by
  have hr := holds r
  rw [h] at hr
  exact (show regVal f r = regVal s r from hr).trans (v r)

/-- The heap-v2 guard prefix (steps 0..9, every trap path L <= 10) writes no register. -/
theorem upds_nil : ∀ k, k < 10 → upds k = [] := by decide +kernel

/-- Trap cases: GPRs equal across runs at the stop point (x0/x1 = pins, x30 = shim return address). -/
def publicFinal : List Nat := [0, 1, 30]
/-- Trap cases: GPRs equal to the run's own entry value at the stop point (all but x9 / x30). -/
def sameFinal : List Nat := (List.range 30).filter (· != 9)

/-- Per-run register facts at the stop state `s` of a run from `e` (run_K_r0's conclusion shape). -/
theorem pair_r0 {s1 s2 e1 e2 : ArmBridge.Draft.NativeState} {x30 sp a0 a1 : BitVec 64} {d1 d2 : BitVec 64}
    (h1 : (∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 → s1.regs.gpr[i.val] = e1.regs.gpr[i.val]) ∧ s1.regs.gpr[9] = d1 ∧
      s1.regs.gpr[30] = x30 ∧ s1.regs.SP_EL0 = sp ∧ regVal s1 (.x 0) = a0 ∧ regVal s1 (.x 1) = a1)
    (h2 : (∀ i : Fin 31, i.val ≠ 9 → i.val ≠ 30 → s2.regs.gpr[i.val] = e2.regs.gpr[i.val]) ∧ s2.regs.gpr[9] = d2 ∧
      s2.regs.gpr[30] = x30 ∧ s2.regs.SP_EL0 = sp ∧ regVal s2 (.x 0) = a0 ∧ regVal s2 (.x 1) = a1) :
    (∀ i : Fin 31, i.val ∈ publicFinal → s1.regs.gpr[i.val] = s2.regs.gpr[i.val]) ∧
    (∀ i : Fin 31, i.val ∈ sameFinal → s1.regs.gpr[i.val] = e1.regs.gpr[i.val] ∧ s2.regs.gpr[i.val] = e2.regs.gpr[i.val]) ∧
    (s1.regs.gpr[9] = d1 ∧ s2.regs.gpr[9] = d2) ∧
    s1.regs.SP_EL0 = s2.regs.SP_EL0 := by
  obtain ⟨k1, n1, l1, p1, z1, o1⟩ := h1
  obtain ⟨k2, n2, l2, p2, z2, o2⟩ := h2
  refine ⟨fun i hi => ?_, fun i hi => ?_, ⟨n1, n2⟩, p1.trans p2.symm⟩
  · simp only [publicFinal, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h
    · have e : i = 0 := Fin.ext h
      subst e; exact z1.trans z2.symm
    · have e : i = 1 := Fin.ext h
      subst e; exact o1.trans o2.symm
    · have e : i = 30 := Fin.ext h
      subst e; exact l1.trans l2.symm
  · have hr : i.val < 30 ∧ i.val ≠ 9 := by
      simp only [sameFinal, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq] at hi; exact hi
    exact ⟨k1 i hr.2 (by omega), k2 i hr.2 (by omega)⟩

/-- Factory case (RET at 369): GPRs equal across runs (the body zeroes x0..x17; x9 is restored by the epilogue). -/
def publicFinalCt : List Nat := (List.range 18).filter (· != 9)
/-- Factory case: GPRs equal to the run's own entry value (callee-saved x18..x30). -/
def sameFinalCt : List Nat := (List.range 13).map (· + 18)

theorem pair_ct_r0 {s1 s2 e1 e2 : ArmBridge.Draft.NativeState} {sp d1 d2 : BitVec 64}
    (h1 : (∀ i : Fin 31, i.val < 18 → i.val ≠ 9 → s1.regs.gpr[i.val] = 0#64) ∧
      (∀ i : Fin 31, 18 ≤ i.val → i.val ≠ 30 → s1.regs.gpr[i.val] = e1.regs.gpr[i.val]) ∧
      s1.regs.gpr[30] = e1.regs.gpr[30] ∧ s1.regs.gpr[9] = d1 ∧ s1.regs.SP_EL0 = sp)
    (h2 : (∀ i : Fin 31, i.val < 18 → i.val ≠ 9 → s2.regs.gpr[i.val] = 0#64) ∧
      (∀ i : Fin 31, 18 ≤ i.val → i.val ≠ 30 → s2.regs.gpr[i.val] = e2.regs.gpr[i.val]) ∧
      s2.regs.gpr[30] = e2.regs.gpr[30] ∧ s2.regs.gpr[9] = d2 ∧ s2.regs.SP_EL0 = sp) :
    (∀ i : Fin 31, i.val ∈ publicFinalCt → s1.regs.gpr[i.val] = s2.regs.gpr[i.val]) ∧
    (∀ i : Fin 31, i.val ∈ sameFinalCt → s1.regs.gpr[i.val] = e1.regs.gpr[i.val] ∧ s2.regs.gpr[i.val] = e2.regs.gpr[i.val]) ∧
    (s1.regs.gpr[9] = d1 ∧ s2.regs.gpr[9] = d2) ∧
    s1.regs.SP_EL0 = s2.regs.SP_EL0 := by
  obtain ⟨z1, k1, l1, n1, p1⟩ := h1
  obtain ⟨z2, k2, l2, n2, p2⟩ := h2
  refine ⟨fun i hi => ?_, fun i hi => ?_, ⟨n1, n2⟩, p1.trans p2.symm⟩
  · have hr : i.val < 18 ∧ i.val ≠ 9 := by
      simp only [publicFinalCt, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq] at hi; exact hi
    exact (z1 i hr.1 hr.2).trans (z2 i hr.1 hr.2).symm
  · have hr : 18 ≤ i.val := by
      simp only [sameFinalCt, List.mem_map, List.mem_range] at hi; omega
    by_cases h30 : i.val = 30
    · have e : i = 30 := Fin.ext h30
      subst e; exact ⟨l1, l2⟩
    · exact ⟨k1 i hr h30, k2 i hr h30⟩

end CT2Heap
#print axioms CT2Heap.pair_ct_r0
#print axioms CT2Heap.pair_r0
#print axioms CT2Heap.frame_carry
#print axioms CT2Heap.upds_nil
