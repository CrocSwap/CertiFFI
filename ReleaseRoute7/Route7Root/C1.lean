-- Route 7 / memcpy C1 roots (loops): source-bound, no invariant premise. The entry invariant comes from
-- generic Route7Entry.invG_at_entry (212 atoms produced from the actual-entry agreement / SourceSpec /
-- TimersQuiet, 10 in EntryResidual), the run from Route7Copy.run_r via Route7Root.memcpy_of_env.
import Route7Root.Rows
import Route7Entry.Entry
import Route7Root.Image
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ReleaseProfile.MachineSource ReleaseProfile.GB10
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Route7Root
open ArmCertLoop ArmCertLoop.CopyNative ArmCertLoop.ContractDraft Route7Copy CertiFFI.Claim

/-- The consumer map of the copy at the root's data (= Context.consumer). -/
abbrev memcpyConsumer {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base d s : BitVec 64) (n : Nat) : ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  SpanMap.consumerMap (spans d s n ++ []) (Image.codeVAs base Generated.imageStart Generated.imageWords)
    mapping (rowsFootprint spec.imageRows).byte

/-- EnvR at the actual entry from the source-bound entry premises (generic lemma at memcpy's
offset / budget / capacity 2n / memPast). -/
theorem memcpy_env_at_entry {domain : QueryDomain} (spec : TopologyImageSpec domain) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base d s returnPC : BitVec 64) (n : Nat)
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : NativeState) (ag : AgreesAt cfg e.regs) (sspec : SourceSpec rho caller spec)
    (timers : TimersQuiet e.regs (Schedule.copySteps n))
    (rws : MemcpyRows spec mapping base d s returnPC n e)
    (res : Route7Entry.EntryResidual spec rows mapping (memcpyConsumer spec mapping base d s n) codeScope image base
      (offset base returnPC n) rho caller e)
    (statusRows : DeploymentObligation "loop:memcpy:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e (e.choiceOcc.getD 1354 0) (2 * n))) :
    EnvR (rws.context (sourceAttributes rho caller) rows) (sourceCatalogue rho caller) e 0 e :=
  Route7Entry.invG_at_entry spec rows mapping (memcpyConsumer spec mapping base d s n) codeScope image base
    (offset base returnPC n) rho caller e (Schedule.copySteps n) (2 * n) (memPast n) cfg ag sspec timers res
    ⟨statusRows.holds⟩

/-- **memcpy C1**: from the canonical source and the actual entry, the reviewed memcpy runs exactly
copySteps n steps to the step-determined final state stateAt e (copySteps n), which satisfies CopyPost (return to returnPC, x0 = d, ∀ i < n, byte(d+i) = entry byte(s+i), frame outside
the destination footprint, callee-saved registers / SP / FP control kept). No invariant, step fact or run is assumed. -/
theorem memcpyFromSource (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base d s returnPC : BitVec 64) (n : Nat)
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : NativeState) (ag : AgreesAt cfg e.regs) (sspec : SourceSpec rho caller spec)
    (timers : TimersQuiet e.regs (Schedule.copySteps n))
    (rws : MemcpyRows spec mapping base d s returnPC n e)
    (res : Route7Entry.EntryResidual spec rows mapping (memcpyConsumer spec mapping base d s n) codeScope image base
      (offset base returnPC n) rho caller e)
    (statusRows : DeploymentObligation "loop:memcpy:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e (e.choiceOcc.getD 1354 0) (2 * n))) :
    Uget.Chain.modelRun real (Schedule.copySteps n) e =
        .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real e (Schedule.copySteps n)) ∧
      CopyPost mapping d s returnPC n e (CertiFFI.Prog.Generic.ModelRunView.stateAt real e (Schedule.copySteps n)) := by
  obtain ⟨fin, run, post, _, _⟩ := memcpy_of_env real rws (sourceAttributes rho caller) rows (sourceCatalogue rho caller)
    (memcpy_env_at_entry spec rows mapping base d s returnPC n rho caller cfg e ag sspec timers rws res statusRows)
  have final := CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (Schedule.copySteps n) e fin run
  rw [final]
  exact ⟨run, post⟩

/-- Fetched-PC evidence root for memcpy (same premises as the C1): every state of the exact run is at a reviewed
memcpy word (0x1a4 + 4j, j < 9) or at returnPC after the final RET. -/
theorem memcpy_fetch_covered_src (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base d s returnPC : BitVec 64) (n : Nat)
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : NativeState) (ag : AgreesAt cfg e.regs) (sspec : SourceSpec rho caller spec)
    (timers : TimersQuiet e.regs (Schedule.copySteps n))
    (rws : MemcpyRows spec mapping base d s returnPC n e)
    (res : Route7Entry.EntryResidual spec rows mapping (memcpyConsumer spec mapping base d s n) codeScope image base
      (offset base returnPC n) rho caller e)
    (statusRows : DeploymentObligation "loop:memcpy:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e (e.choiceOcc.getD 1354 0) (2 * n))) :
    ∀ k, k ≤ Schedule.copySteps n → ∃ z, Uget.Chain.modelRun real k e = .ok () z ∧
      PcOk (rws.context (sourceAttributes rho caller) rows) z := by
  obtain ⟨_, _, _, cov, _⟩ := memcpy_of_env real rws (sourceAttributes rho caller) rows (sourceCatalogue rho caller)
    (memcpy_env_at_entry spec rows mapping base d s returnPC n rho caller cfg e ag sspec timers rws res statusRows)
  exact cov

end Route7Root
#print axioms Route7Root.memcpy_env_at_entry
#print axioms Route7Root.memcpyFromSource
#print axioms Route7Root.memcpy_fetch_covered_src
