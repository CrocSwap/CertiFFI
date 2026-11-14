-- d199 pipeline: release outputs. At the run's end (AgreesAt plan.length, from runG) the whole plan's final
-- symbolic state agrees with the machine: tracked output registers and region bytes are D-table values (P5 shape;
-- certiffi's output_bytes_of_plan / ret_reg_gen consume these, or the math lemma rewrites them to the spec).
import ArmCertPipe.Dispatch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft
set_option autoImplicit false
namespace ArmCertPipe
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.RegBind (St)

/-- At the plan's end, AgreesAt is Agrees against the whole plan's final table and symbolic state. -/
theorem agrees_end {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {x : St} {D : List Def} {σf : Sym}
    (h : AgreesAt mapping pinv regions σ0 inputs plan plan.length x)
    (hall : compileRun regions σ0 inputs.length plan = some (D, σf)) :
    Agrees mapping pinv (extend inputs D) σf x := by
  obtain ⟨ds, σ, hc, hA, _⟩ := h
  rw [List.take_length, hall] at hc
  have e := Option.some.inj hc
  simp only [Prod.mk.injEq] at e
  rw [e.1, e.2]; exact hA

/-- Every tracked output location (g, j) ↦ some (i, b) holds byte b of table entry i at the end. -/
theorem outMem_end {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {vals : List (BitVec 64)} {σf : Sym}
    {x : St} (hA : Agrees mapping pinv vals σf x) :
    ∀ (locs : List (Region × Nat)) (outs : List (Option (Nat × Nat))),
      locs.map (fun (g, j) => σf.memB g j) = outs →
      ∀ q ∈ locs.zip outs, ∀ i b, q.2 = some (i, b) →
        regionByte mapping pinv x q.1.1 q.1.2 = some (((vals.getD i 0) >>> (8 * b)).setWidth 8)
  | [], _, _ => by intro q hq; simp at hq
  | (g, j) :: ls, outs, h => by
    cases outs with
    | nil => simp at h
    | cons o os =>
      simp only [List.map_cons, List.cons.injEq] at h
      intro q hq i b hqb
      simp only [List.zip_cons_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hA.2.2 _ _ _ _ (by rw [h.1]; exact hqb)
      · exact outMem_end hA ls os h.2 q hq i b hqb

#print axioms agrees_end
#print axioms outMem_end
end ArmCertPipe
