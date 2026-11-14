-- d207 runtime14: the physical-byte analogues of generic ArmCertPipe.Dispatch (NextOb, runG) and
-- ArmCertPipe.Release (agrees_end, outMem_end), over Memory's ArmCertPipe.Physical {InvG, AgreesAt, stepG, chainG}.
-- Same statements with `mapping pinv` replaced by a physical byte view `bytePA`; runG needs NO RegionCoherent premise.
import ArmCertPipe.PhysicalDeploy
import ArmCertPipe.Release
import ArmCertPipe.Prefix
import ArmCertValue.PhysicalMemory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft
set_option autoImplicit false
namespace ArmCertPipe.Physical
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
open ArmCertValue.Physical (BytePA StepFact)
open HeapV2StepCerts.RegBind (St)

/-- The `next` obligation of step k (the argument of `stepG`), as a named Prop. -/
abbrev NextOb (real : Type) [Sail.SailReal real] (Inv : Nat → NativeState → Prop) (bytePA : BytePA)
    (regions : List Region) (σ0 : Sym) (inputs : List (BitVec 64)) (plan : List StepV) (k : Nat) : Prop :=
  ∀ x, Inv k x → (∀ fin, modelStep real x = .ok () fin → AgreesAt bytePA regions σ0 inputs plan (k + 1) fin) →
    ∃ fin, modelStep real x = .ok () fin ∧ Inv (k + 1) fin

/-- The whole run (physical): invariant at every step k < plan.length and AgreesAt plan.length after the last step. -/
theorem runG (real : Type) [Sail.SailReal real] {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop} {image : MemReloc.Image}
    {loadBase : MemReloc.Word} {base : BitVec 64} {offset : Nat → BitVec 64} {budget : Nat}
    {bytePA : BytePA} {regions : List Region} {σ0 : Sym} {inputs : List (BitVec 64)} {plan : List StepV}
    (entry : NativeState) (hne : 0 < plan.length)
    (init : InvG spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan 0 entry)
    (hall : (compileRun regions σ0 inputs.length plan).isSome = true)
    (route : ∀ k (hk : k < plan.length),
      StepFact real (InvG spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan)
        bytePA regions plan k hk)
    (next : ∀ k, k + 1 < plan.length →
      NextOb real (InvG spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan)
        bytePA regions σ0 inputs plan k) :
    (∀ k, k < plan.length →
      InvG spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan k
        (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan.length - 1)) = .ok () fin ∧
      AgreesAt bytePA regions σ0 inputs plan plan.length fin := by
  have chain := chainG real _ entry (plan.length - 1) init
    (fun k hk => stepG real hall k (by omega) (route k (by omega)) (next k (by omega)))
  refine ⟨fun k hk => chain k (by omega), ?_⟩
  have hj : plan.length - 1 < plan.length := by omega
  have inv := chain (plan.length - 1) (Nat.le_refl _)
  obtain ⟨fin, run, hv, hm⟩ := route (plan.length - 1) hj _ inv
  refine ⟨fin, run, ?_⟩
  have h := agreesAt_succ hj hall inv.extra hv hm
  rwa [Nat.sub_add_cancel hne] at h

/-- At the plan's end, AgreesAt is Agrees against the whole plan's final table and symbolic state. -/
theorem agrees_end {bytePA : BytePA} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {x : St} {D : List Def} {σf : Sym}
    (h : AgreesAt bytePA regions σ0 inputs plan plan.length x)
    (hall : compileRun regions σ0 inputs.length plan = some (D, σf)) :
    ArmCertValue.Physical.Agrees bytePA (extend inputs D) σf x := by
  obtain ⟨ds, σ, hc, hA, _⟩ := h
  rw [List.take_length, hall] at hc
  have e := Option.some.inj hc
  simp only [Prod.mk.injEq] at e
  rw [e.1, e.2]; exact hA

/-- Every tracked output location (g, j) ↦ some (i, b) holds byte b of table entry i at the end (physical bytes). -/
theorem outMem_end {bytePA : BytePA} {vals : List (BitVec 64)} {σf : Sym}
    {x : St} (hA : ArmCertValue.Physical.Agrees bytePA vals σf x) :
    ∀ (locs : List (Region × Nat)) (outs : List (Option (Nat × Nat))),
      locs.map (fun (g, j) => σf.memB g j) = outs →
      ∀ q ∈ locs.zip outs, ∀ i b, q.2 = some (i, b) →
        ArmCertValue.Physical.regionByte bytePA x q.1.1 q.1.2 = some (((vals.getD i 0) >>> (8 * b)).setWidth 8)
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


/-- NZCV analogue of regVal_of_agreesAt (PipeR14Next.flags_of_agreesAt), physical AgreesAt. -/
theorem flags_of_agreesAt {bytePA : BytePA} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {k : Nat} {x : HeapV2StepCerts.RegBind.St} {D : List Def} {σf : Sym}
    (h : AgreesAt bytePA regions σ0 inputs plan k x)
    (hall : compileRun regions σ0 inputs.length plan = some (D, σf))
    {n z c v : Nat}
    (hr : (compileRun regions σ0 inputs.length (plan.take k)).map (fun p => p.2.nzcv) = some (some (n, z, c, v))) :
    x.regs.PSTATE.N.setWidth 64 = (extend inputs D).getD n 0 ∧ x.regs.PSTATE.Z.setWidth 64 = (extend inputs D).getD z 0 ∧
    x.regs.PSTATE.C.setWidth 64 = (extend inputs D).getD c 0 ∧ x.regs.PSTATE.V.setWidth 64 = (extend inputs D).getD v 0 := by
  obtain ⟨ds, σ, hc, hA, hB⟩ := h
  rw [hc] at hr
  simp only [Option.map_some, Option.some.injEq] at hr
  obtain ⟨vn, vz, vc, vv⟩ := hA.2.1 n z c v hr
  obtain ⟨ln, lz, lc, lv⟩ := hB.2.1 n z c v hr
  have split := compileRun_append regions (plan.take k) (plan.drop k) σ0 inputs.length
  rw [List.take_append_drop, hall, hc] at split
  simp only [Option.bind_some] at split
  cases hrest : compileRun regions σ (inputs.length + ds.length) (plan.drop k) with
  | none => rw [hrest] at split; simp at split
  | some q =>
    rw [hrest] at split
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at split
    rw [split.1, extend_append]
    exact ⟨by rw [vn, ArmCertPipe.getD_extend_input _ _ ln], by rw [vz, ArmCertPipe.getD_extend_input _ _ lz],
      by rw [vc, ArmCertPipe.getD_extend_input _ _ lc], by rw [vv, ArmCertPipe.getD_extend_input _ _ lv]⟩

#print axioms flags_of_agreesAt

#print axioms runG
#print axioms agrees_end
#print axioms outMem_end
end ArmCertPipe.Physical
