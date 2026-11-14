-- physical-byte variant of the generic prefix agreement invariant.
import ArmCertPipe.Prefix
import ArmCertValue.PhysicalSSA
set_option autoImplicit false
namespace ArmCertPipe.Physical
open ArmCertValue
open HeapV2StepCerts.RegBind (St)

def AgreesAt (bytePA : ArmCertValue.Physical.BytePA) (regions : List Region) (σ0 : Sym)
    (inputs : List (BitVec 64)) (plan : List StepV) (k : Nat) (x : St) : Prop :=
  ∃ ds σ, compileRun regions σ0 inputs.length (plan.take k) = some (ds, σ) ∧
    ArmCertValue.Physical.Agrees bytePA (extend inputs ds) σ x ∧ σ.Bounded (extend inputs ds).length

/-- At k = 0: the entry agreement. -/
theorem agreesAt_zero {bytePA : ArmCertValue.Physical.BytePA} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {x : St}
    (hA : ArmCertValue.Physical.Agrees bytePA inputs σ0 x) (hB : σ0.Bounded inputs.length) :
    AgreesAt bytePA regions σ0 inputs plan 0 x :=
  ⟨[], σ0, by simp [compileRun], by simpa [extend] using hA, by simpa [extend] using hB⟩

/-- **The chain extra is preserved** by any step satisfying its plan entry's VHolds and MemVHolds, as long as the whole
    plan compiles (P1's compiles_D). -/
theorem agreesAt_succ {bytePA : ArmCertValue.Physical.BytePA} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {k : Nat} {x y : St}
    (hk : k < plan.length)
    (hall : (compileRun regions σ0 inputs.length plan).isSome = true)
    (h : AgreesAt bytePA regions σ0 inputs plan k x)
    (hv : VHolds plan[k].us plan[k].fl x y) (hm : ArmCertValue.Physical.MemVHolds bytePA regions plan[k].mem x y) :
    AgreesAt bytePA regions σ0 inputs plan (k + 1) y := by
  obtain ⟨ds, σ, hc, hA, hB⟩ := h
  have split : plan = plan.take k ++ (plan[k] :: plan.drop (k + 1)) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  -- the k-th step compiles (from the whole plan compiling)
  have hstep : ∃ ds' σ', compile σ (inputs.length + ds.length) regions plan[k] = some (ds', σ') := by
    rw [split, compileRun_append, hc] at hall
    simp only [Option.bind_some, Option.isSome_map, compileRun] at hall
    cases h1 : compile σ (inputs.length + ds.length) regions plan[k] with
    | none => rw [h1] at hall; simp at hall
    | some p => exact ⟨p.1, p.2, rfl⟩
  obtain ⟨ds', σ', h1⟩ := hstep
  have hlen : (extend inputs ds).length = inputs.length + ds.length := extend_length inputs ds
  have hc' : compile σ (extend inputs ds).length regions plan[k] = some (ds', σ') := by rw [hlen]; exact h1
  obtain ⟨hA', hB'⟩ := ArmCertValue.Physical.step_agrees hA hB hv hm hc'
  refine ⟨ds ++ ds', σ', ?_, by rw [extend_append]; exact hA', by rw [extend_append]; exact hB'⟩
  rw [List.take_succ_eq_append_getElem hk, compileRun_append, hc]
  simp [compileRun, h1]

theorem regVal_of_agreesAt {bytePA : ArmCertValue.Physical.BytePA} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {k : Nat} {x : St} {D : List Def} {σf : Sym}
    (h : AgreesAt bytePA regions σ0 inputs plan k x)
    (hall : compileRun regions σ0 inputs.length plan = some (D, σf))
    {r : HeapV2StepCerts.RegBind.Reg} {i : Nat}
    (hr : (compileRun regions σ0 inputs.length (plan.take k)).map (fun p => p.2.regs r) = some (some i)) :
    HeapV2StepCerts.RegBind.regVal x r = (extend inputs D).getD i 0 := by
  obtain ⟨ds, σ, hc, hA, hB⟩ := h
  rw [hc] at hr
  simp only [Option.map_some, Option.some.injEq] at hr
  have hv := hA.1 r i hr
  have hlt := hB.1 r i hr
  -- D = ds ++ rest
  have split := compileRun_append regions (plan.take k) (plan.drop k) σ0 inputs.length
  rw [List.take_append_drop, hall, hc] at split
  simp only [Option.bind_some] at split
  cases hrest : compileRun regions σ (inputs.length + ds.length) (plan.drop k) with
  | none => rw [hrest] at split; simp at split
  | some q =>
    rw [hrest] at split
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at split
    rw [hv, split.1, extend_append, getD_extend_input _ _ hlt]


#print axioms agreesAt_succ
#print axioms regVal_of_agreesAt
end ArmCertPipe.Physical
