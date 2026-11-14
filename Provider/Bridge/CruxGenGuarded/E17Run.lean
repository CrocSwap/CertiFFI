import Bridge.CruxGenGuarded.E17StateFacts
import ArmCertTranslateModel.TranslationAgreesCurrent
import CertiFFI.Prog.Generic.ModelRunView
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.E17Run
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! E17 retirement run join (; ae1428e5). For ANY run invariant
`Inv` that Core's chained actual steps preserve (each step is a `Uget.Chain.Step`,
e.g. `entry_class_next(_at)` packaged per plan index) and that projects to the
chain facts, decision-32 `TranslationAgrees m` holds at EVERY reached actual
state of the run. Remaining per-state input: `ClosedMembershipAt` (the actual
accesses' declared queries with current access data); static input:
`ConsumerMapAgrees`. No new premise; TranslationAgrees is concluded, not assumed. -/

theorem e17_along_steps (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (agrees : ConsumerMapAgrees spec mapping m)
    (Inv : Nat → NativeState → Prop) (len : Nat) (entry : NativeState)
    (steps : ∀ k, k < len → Uget.Chain.Step real (Inv k) (Inv (k + 1)))
    (initial : Inv 0 entry)
    (chain : ∀ k x, Inv k x →
      NativeEntryTail.EntryPins x ∧ EntryFeatures x.regs ∧ E11Debug.E11CheckDebug x.regs ∧
        CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState x))
    (closed : ∀ k x, Inv k x → ClosedMembershipAt spec config rows mapping m x) :
    ∀ k, k ≤ len →
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees m (stateAt real entry k) := by
  have reachedInv := invariant_prefixes real Inv len steps entry initial
  refine translation_agrees_along spec config rows mapping m (· ≤ len) (stateAt real entry) agrees ?_
  intro k hk
  have inv := reachedInv k hk
  obtain ⟨pins, features, e11, current⟩ := chain k _ inv
  obtain ⟨cur, mode, f4, debug, spe⟩ :=
    E17StateFacts.state_facts (stateAt real entry k) pins features e11 current
  exact ⟨cur, mode, f4, debug, spe, closed k _ inv⟩

#print axioms e17_along_steps
end ArmBridge.CruxGenGuarded.E17Run
