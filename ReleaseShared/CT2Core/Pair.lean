-- (CT2): two runs at the same ValuePlan step agree on every location whose table id is public.
import CT2Core.PubMask
import ArmCertPipe.ValuePlan
set_option autoImplicit false
namespace CT2Core
open ArmCertValue HeapV2StepCerts.RegBind

/-- Both runs' AgreesAt at the same step k share one compiled (defs, σ), since compileRun is pure. -/
theorem agreesAt_pair {language : ArmCertPipe.ValuePlan.Language} {view1 view2 : Physical.BytePA}
    {regions : List Region} {σ0 : Sym} {v1 v2 : List (BitVec 64)}
    {plan : List (ArmCertPipe.ValuePlan.Step language)} {k : Nat} {s1 s2 : St}
    (h1 : ArmCertPipe.ValuePlan.AgreesAt language view1 regions σ0 v1 plan k s1)
    (h2 : ArmCertPipe.ValuePlan.AgreesAt language view2 regions σ0 v2 plan k s2)
    (hl : v1.length = v2.length) :
    ∃ ds σ, ArmCertPipe.ValuePlan.compileRun language regions σ0 v1.length (plan.take k) = some (ds, σ) ∧
      Physical.Agrees view1 (extend v1 ds) σ s1 ∧ Physical.Agrees view2 (extend v2 ds) σ s2 := by
  obtain ⟨d1, r1, c1, a1, _⟩ := h1
  obtain ⟨d2, r2, c2, a2, _⟩ := h2
  rw [← hl] at c2
  rw [c1] at c2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c2)
  exact ⟨d1, r1, c1, a1, a2⟩

/-- Registers: a tracked register whose id is public is equal across the runs. -/
theorem reg_eq {view1 view2 : Physical.BytePA} {v1 v2 : List (BitVec 64)} {ds : List Def} {σ : Sym}
    {s1 s2 : St} {p : List Bool}
    (a1 : Physical.Agrees view1 (extend v1 ds) σ s1) (a2 : Physical.Agrees view2 (extend v2 ds) σ s2)
    (hA : AgreeOn p v1 v2) (r : Reg) (i : Nat) (hr : σ.regs r = some i)
    (hp : (pubExtend p ds).getD i false = true) : regVal s1 r = regVal s2 r := by
  rw [a1.1 r i hr, a2.1 r i hr]
  exact (agreeOn_extend ds p v1 v2 hA).2.2 i hp

/-- NZCV: if all four flag ids are public, the flags are equal across the runs. -/
theorem nzcv_eq {view1 view2 : Physical.BytePA} {v1 v2 : List (BitVec 64)} {ds : List Def} {σ : Sym}
    {s1 s2 : St} {p : List Bool}
    (a1 : Physical.Agrees view1 (extend v1 ds) σ s1) (a2 : Physical.Agrees view2 (extend v2 ds) σ s2)
    (hA : AgreeOn p v1 v2) (n z c v : Nat) (hf : σ.nzcv = some (n, z, c, v))
    (hn : (pubExtend p ds).getD n false = true) (hz : (pubExtend p ds).getD z false = true)
    (hc : (pubExtend p ds).getD c false = true) (hv : (pubExtend p ds).getD v false = true) :
    s1.regs.PSTATE.N.setWidth 64 = s2.regs.PSTATE.N.setWidth 64 ∧
    s1.regs.PSTATE.Z.setWidth 64 = s2.regs.PSTATE.Z.setWidth 64 ∧
    s1.regs.PSTATE.C.setWidth 64 = s2.regs.PSTATE.C.setWidth 64 ∧
    s1.regs.PSTATE.V.setWidth 64 = s2.regs.PSTATE.V.setWidth 64 := by
  have E := (agreeOn_extend ds p v1 v2 hA).2.2
  obtain ⟨n1, z1, c1, v1'⟩ := a1.2.1 n z c v hf
  obtain ⟨n2, z2, c2, v2'⟩ := a2.2.1 n z c v hf
  exact ⟨by rw [n1, n2, E n hn], by rw [z1, z2, E z hz], by rw [c1, c2, E c hc], by rw [v1', v2', E v hv]⟩

/-- Tracked memory bytes: a byte whose table id is public reads equal across the runs (each through its own view). -/
theorem byte_eq {view1 view2 : Physical.BytePA} {v1 v2 : List (BitVec 64)} {ds : List Def} {σ : Sym}
    {s1 s2 : St} {p : List Bool}
    (a1 : Physical.Agrees view1 (extend v1 ds) σ s1) (a2 : Physical.Agrees view2 (extend v2 ds) σ s2)
    (hA : AgreeOn p v1 v2) (r : Region) (j i k : Nat) (hm : σ.memB r j = some (i, k))
    (hp : (pubExtend p ds).getD i false = true) :
    ∃ b, Physical.regionByte view1 s1 r j = some b ∧ Physical.regionByte view2 s2 r j = some b := by
  refine ⟨_, a1.2.2 r j i k hm, ?_⟩
  rw [a2.2.2 r j i k hm, (agreeOn_extend ds p v1 v2 hA).2.2 i hp]

#print axioms agreesAt_pair
#print axioms reg_eq
#print axioms nzcv_eq
#print axioms byte_eq
end CT2Core
