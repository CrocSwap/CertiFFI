-- CT2.R0 for route-7 memmove (two runs sharing d, s, n, returnPC; the copied bytes are the secret).
import CT2Route7.MoveRun
set_option autoImplicit false
namespace Route7Move.CT2
open ArmBridge.Draft ArmCertLoop ArmCertLoop.ContractDraft

/-- The memmove path is a function of the public (d, s, n), so both runs take the same path. -/
theorem path_eq (c1 c2 : Context) (hd : c1.d = c2.d) (hs : c1.s = c2.s) (hn : c1.n = c2.n) : c1.path = c2.path := by
  simp only [Context.path, hd, hs, hn]

/-- **CT2.R0 (held part), memmove**, per path.
* empty / same: every GPR returned unchanged (x0 = d, x1 = s, x2 = n public via Args; x3.. caller-owned / callee-saved).
* forward: public x0 = d, x1 = s+n, x2 = 0, x3 = d+n; per run x5..x30 unchanged. Finding: x4 (last copied byte).
* backward: public x0 = d, x1 = s (unchanged), x2 = 0, x3 = d, x4 = s; per run x6..x30 unchanged. Finding: x5 (last
  copied byte). -/
theorem memmove_r0 (c1 c2 : Context) (hd : c1.d = c2.d) (hs : c1.s = c2.s) (hn : c1.n = c2.n)
    (e1 e2 f1 f2 : NativeState) (a1 : Args c1.d c1.s c1.returnPC c1.n e1) (a2 : Args c2.d c2.s c2.returnPC c2.n e2)
    (p1 : MovePost c1.mapping c1.d c1.s c1.returnPC c1.n e1 f1 ∧ ExtraM c1 e1 f1)
    (p2 : MovePost c2.mapping c2.d c2.s c2.returnPC c2.n e2 f2 ∧ ExtraM c2 e2 f2) :
    f1.regs.gpr[0] = f2.regs.gpr[0] ∧ f1.regs.gpr[1] = f2.regs.gpr[1] ∧ f1.regs.gpr[2] = f2.regs.gpr[2] ∧
    (c1.path = .forward ∨ c1.path = .backward → f1.regs.gpr[3] = f2.regs.gpr[3]) ∧
    (c1.path = .backward → f1.regs.gpr[4] = f2.regs.gpr[4]) ∧
    ((c1.path = .empty ∨ c1.path = .same) → f1.regs.gpr = e1.regs.gpr ∧ f2.regs.gpr = e2.regs.gpr) ∧
    (c1.path = .forward → ∀ r : Fin 31, 5 ≤ r.val →
      f1.regs.gpr[r.val] = e1.regs.gpr[r.val] ∧ f2.regs.gpr[r.val] = e2.regs.gpr[r.val]) ∧
    (c1.path = .backward → ∀ r : Fin 31, 6 ≤ r.val →
      f1.regs.gpr[r.val] = e1.regs.gpr[r.val] ∧ f2.regs.gpr[r.val] = e2.regs.gpr[r.val]) ∧
    f1.regs.SP_EL0 = e1.regs.SP_EL0 ∧ f2.regs.SP_EL0 = e2.regs.SP_EL0 := by
  have hp := path_eq c1 c2 hd hs hn
  obtain ⟨⟨_, x0a, _, _, _, spa, _⟩, ua, fa, ba⟩ := p1
  obtain ⟨⟨_, x0b, _, _, _, spb, _⟩, ub, fb, bb⟩ := p2
  obtain ⟨_, s1, n1, _⟩ := a1
  obtain ⟨_, s2, n2, _⟩ := a2
  change e1.regs.gpr[1] = c1.s at s1; change e2.regs.gpr[1] = c2.s at s2
  change e1.regs.gpr[2].toNat = c1.n at n1; change e2.regs.gpr[2].toNat = c2.n at n2
  change f1.regs.gpr[0] = c1.d at x0a; change f2.regs.gpr[0] = c2.d at x0b
  have q0 : f1.regs.gpr[0] = f2.regs.gpr[0] := by rw [x0a, x0b, hd]
  rcases h : c1.path with _ | _ | _ | _
  all_goals have h2 : c2.path = c1.path := hp.symm
  all_goals rw [h] at h2
  · -- empty
    have g1 := ua (Or.inl h); have g2 := ub (Or.inl h2)
    refine ⟨q0, by rw [g1, g2, s1, s2, hs], BitVec.eq_of_toNat_eq (by rw [g1, g2, n1, n2, hn]),
      fun hh => (by rcases hh with hh | hh <;> cases hh), fun hh => (by cases hh), fun _ => ⟨g1, g2⟩,
      fun hh => (by cases hh), fun hh => (by cases hh), spa, spb⟩
  · -- same
    have g1 := ua (Or.inr h); have g2 := ub (Or.inr h2)
    refine ⟨q0, by rw [g1, g2, s1, s2, hs], BitVec.eq_of_toNat_eq (by rw [g1, g2, n1, n2, hn]),
      fun hh => (by rcases hh with hh | hh <;> cases hh), fun hh => (by cases hh), fun _ => ⟨g1, g2⟩,
      fun hh => (by cases hh), fun hh => (by cases hh), spa, spb⟩
  · -- forward
    obtain ⟨y1, y2, y3, yk⟩ := fa h; obtain ⟨z1, z2, z3, zk⟩ := fb h2
    refine ⟨q0, by rw [y1, z1, hs, hn], BitVec.eq_of_toNat_eq (by rw [y2, z2]),
      fun _ => (by rw [y3, z3, hd, hn]), fun hh => (by cases hh), fun hh => (by rcases hh with hh | hh <;> cases hh),
      fun _ r hr => ⟨yk r hr, zk r hr⟩, fun hh => (by cases hh), spa, spb⟩
  · -- backward
    obtain ⟨y1, y2, y3, y4, yk⟩ := ba h; obtain ⟨z1, z2, z3, z4, zk⟩ := bb h2
    refine ⟨q0, by rw [y1, z1, s1, s2, hs], BitVec.eq_of_toNat_eq (by rw [y2, z2]),
      fun _ => (by rw [y3, z3, hd, hn]), fun _ => (by rw [y4, z4, hs, hn]), fun hh => (by rcases hh with hh | hh <;> cases hh),
      fun hh => (by cases hh), fun _ r hr => ⟨yk r hr, zk r hr⟩, spa, spb⟩

#print axioms memmove_r0
end Route7Move.CT2
