import Bridge.CruxGenGuarded.ChainInvV4
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.ChainInvV4
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.ChainInvV3
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! Pointwise lift: a step whose premises need ChainInv v4 fields at the step's own state
(Memory's branch decisions dec_k read ValBind; BL CallerControls reads the residue) is
given as `at`, a successor for each v4 state with ChainInv3 at k+1 and the step relation R. -/

run_cmd do
  IO.eprintln "CURRENT_DECL ChainInvV4.step4_of_at"
  (← IO.getStderr).flush

theorem step4_of_at (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins)
    (q : HeapV2StepCerts.ValBind.Inputs) (v19 v30 : BitVec 64) (k : Nat)
    (R : NativeState → NativeState → Prop)
    (at_ : ∀ x, ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 k x →
      ∃ fin, modelStep real x = .ok () fin ∧
        ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1) fin ∧ R x fin)
    (vcarry : ∀ s f, HeapV2StepCerts.RegBind.RegBind p k s → HeapV2StepCerts.ValBind.ValBind q k s →
      R s f → HeapV2StepCerts.ValBind.ValBind q (k + 1) f)
    (lcarry : ∀ s f, R s f → RtSaved2.LrField p mapping base v19 v30 k s → RtSaved2.LrField p mapping base v19 v30 (k + 1) f)
    (gcs : ∀ s f, R s f → GcsFrame s f) :
    Uget.Chain.Step real
      (ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 k)
      (ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 (k + 1)) := by
  intro x inv
  obtain ⟨fin, run, inv3, rel⟩ := at_ x inv
  exact ⟨fin, run, ⟨inv3, vcarry x fin inv.v3.regBind inv.valBind rel, lcarry x fin rel inv.lr,
    RtBl.CallerInv.residue_carry (gcs x fin rel) inv.residue⟩⟩

/-- A ChainInv v4 state gives the BL caller controls (residue + step and branch pins). -/
theorem controls_of_v4 {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} {scope : Nat → Prop}
    {image : MemReloc.Image} {loadBase : MemReloc.Word} {base : BitVec 64}
    {offset : Nat → BitVec 64} {budget : Nat} {p : HeapV2E17.Pins} {q : HeapV2StepCerts.ValBind.Inputs}
    {v19 v30 : BitVec 64} {k : Nat} {x : NativeState}
    (h : ChainInv4 spec config rows mapping m scope image loadBase base offset budget p q v19 v30 k x) :
    NativeEntryCallerParts.CallerControls x :=
  RtBl.CallerInv.callerControls_of_inv3 h.v3 h.residue

#print axioms step4_of_at
#print axioms controls_of_v4
end ArmBridge.CruxGenGuarded.ChainInvV4
