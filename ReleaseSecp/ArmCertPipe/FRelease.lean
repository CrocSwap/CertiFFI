-- Generic finite-run composition for physical F plans, with explicit extra-state continuations.
import ArmCertPipe.FDeploy
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
namespace ArmCertPipe.F

theorem agrees_end {bytePA : ArmCertValue.Physical.BytePA} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List ArmCertValue.F.Step} {x : NativeState} {D : List Def} {σf : Sym}
    (h : AgreesAt bytePA regions σ0 inputs plan plan.length x)
    (compiled : ArmCertValue.F.compileRun regions σ0 inputs.length plan = some (D,σf)) :
    ArmCertValue.Physical.Agrees bytePA (extend inputs D) σf x := by
  obtain ⟨ds,σ,hc,agree,_⟩ := h
  simp only [List.take_length] at hc
  have e : (ds,σ) = (D,σf) := Option.some.inj (hc.symm.trans compiled)
  cases e
  exact agree

theorem runExtra (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig} {rows : List PermissionRow}
    {mapping : BitVec 64 → Option Nat} {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {scope : Nat → Prop} {image : MemReloc.Image} {loadBase base : BitVec 64} {offset : Nat → BitVec 64}
    {budget : Nat} {bytePA : ArmCertValue.Physical.BytePA} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List ArmCertValue.F.Step} {Extra : Nat → NativeState → Prop}
    (entry : NativeState) (nonempty : 0 < plan.length)
    (compiled : (ArmCertValue.F.compileRun regions σ0 inputs.length plan).isSome = true)
    (init : InvExtra spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan Extra 0 entry)
    (route : ∀ k (hk : k < plan.length), ArmCertPipe.F.StepExtraFact real
      (InvExtra spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan Extra)
      bytePA regions plan Extra k hk)
    (next : ∀ k, k+1 < plan.length → ∀ x,
      InvExtra spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan Extra k x →
      (∀ fin, modelStep real x = .ok () fin → AgreesAt bytePA regions σ0 inputs plan (k+1) fin ∧ Extra (k+1) fin) →
      ∃ fin, modelStep real x = .ok () fin ∧
        InvExtra spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan Extra (k+1) fin) :
    (∀ k, k < plan.length → InvExtra spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan Extra k (stateAt real entry k)) ∧
    ∃ fin, modelStep real (stateAt real entry (plan.length-1)) = .ok () fin ∧
      AgreesAt bytePA regions σ0 inputs plan plan.length fin ∧ Extra plan.length fin := by
  have step : ∀ k, k < plan.length-1 → ∀ x,
      InvExtra spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan Extra k x →
      ∃ fin, modelStep real x = .ok () fin ∧
        InvExtra spec config rows mapping m scope image loadBase base offset budget bytePA regions σ0 inputs plan Extra (k+1) fin := by
    intro k hk
    have hkp : k < plan.length := by omega
    exact stepExtra real compiled k hkp (route k hkp) (next k (by omega))
  have reached := chainG real _ entry (plan.length-1) init step
  have last := reached (plan.length-1) (Nat.le_refl _)
  have bound : plan.length-1 < plan.length := by omega
  obtain ⟨fin,run,holds,extra⟩ := route (plan.length-1) bound _ last
  have finalIndex : plan.length-1+1 = plan.length := by omega
  refine ⟨fun k hk => reached k (by omega),fin,run,?_,?_⟩
  · have h := agreesAt_succ bound compiled last.extra.1 holds
    simpa only [finalIndex] using h
  · simpa only [finalIndex] using extra
#print axioms agrees_end
#print axioms runExtra
end ArmCertPipe.F
