-- Route 7 / memset C1 roots (loops): card rows as typed claim inputs, the memset Context from them, the entry
-- invariant from Route7Entry.invG_at_entry (capacity n, setPast, setSteps), the run from Route7Set.run_s.
import Route7Set.Run
import Route7Entry.Entry
import CertiFFIClaim.Kinds
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ReleaseProfile.MachineSource ReleaseProfile.GB10
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Route7Root
open ArmCertLoop ArmCertLoop.SetNative ArmCertLoop.ContractDraft Route7Set CertiFFI.Claim

/-- memset card rows (caller contracts, loader / deployment obligations, E34). -/
structure MemsetRows {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base d fill returnPC : BitVec 64) (n : Nat) (e : NativeState) : Prop where
  page : DeploymentObligation "loop:load-base-page" (base.toNat % 4096 = 0)
  low : DeploymentObligation "loop:load-base-low" (base.toNat < 2 ^ 54)
  returnLow : CallerContract "loop:return-canonical" (returnPC.toNat < 2 ^ 54)
  destObject : CallerContract "loop:memset:destination-object" (SpanMap.NoWrap (destSpan d n))
  code : DeploymentObligation "loop:code-geometry" (CodeGeometry mapping base)
  codeWrite : DeploymentObligation "loop:code-write-separated" (CodeWriteSeparated mapping base d n)
  data : DeploymentObligation "loop:memset:data-geometry" (∀ i, i < n → ∃ pa : BitVec 56,
    mapping (d + BitVec.ofNat 64 i) = some pa.toNat ∧ MemM1.MemReadIF.NotMMIO pa ∧
    ¬ (rowsFootprint spec.imageRows).byte pa.toNat)
  injective : DeploymentObligation "loop:memset:injective" (SpanMap.UnionInjective mapping [destSpan d n])
  separated : DeploymentObligation "loop:image-table-separated"
    (ImageTableSeparated codeScope base mapping (rowsFootprint spec.imageRows).byte)
  args : CallerContract "loop:memset:args"
    (e.regs.gpr[0] = d ∧ e.regs.gpr[1] = fill ∧ e.regs.gpr[2].toNat = n ∧ e.regs.gpr[30] = returnPC)
  nodup : DeploymentObligation "E34" ((spec.logicalRows.map (·.logical)).Nodup)

def MemsetRows.context {domain : QueryDomain} {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {base d fill returnPC : BitVec 64} {n : Nat} {e : NativeState}
    (r : MemsetRows spec mapping base d fill returnPC n e) (config : AttributeConfig) (rows : List PermissionRow) :
    SetNative.Context where
  domain := domain
  spec := spec
  config := config
  rows := rows
  mapping := mapping
  base := base
  d := d
  fill := fill
  returnPC := returnPC
  n := n
  page := r.page.holds
  low := r.low.holds
  returnLow := r.returnLow.holds
  destObject := r.destObject.holds
  code := r.code.holds
  codeWrite := r.codeWrite.holds
  data := r.data.holds
  injective := r.injective.holds
  separated := r.separated.holds

abbrev memsetConsumer {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base d : BitVec 64) (n : Nat) : ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  SpanMap.consumerMap [destSpan d n] (Image.codeVAs base Generated.imageStart Generated.imageWords)
    mapping (rowsFootprint spec.imageRows).byte

/-- **memset C1**: from the canonical source and the actual entry, the reviewed memset runs exactly
setSteps n steps to stateAt e (setSteps n), which satisfies Post (return, x0 = d, ∀ i < n, byte(d+i) = fill low byte,
frame outside the destination footprint, callee-saved registers kept). No invariant, step fact or run is assumed. -/
theorem memsetFromSource (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base d fill returnPC : BitVec 64) (n : Nat)
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : NativeState) (ag : AgreesAt cfg e.regs) (sspec : SourceSpec rho caller spec)
    (timers : TimersQuiet e.regs (Schedule.setSteps n))
    (rws : MemsetRows spec mapping base d fill returnPC n e)
    (res : Route7Entry.EntryResidual spec rows mapping (memsetConsumer spec mapping base d n) codeScope image base
      (SetNative.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e)
    (statusRows : DeploymentObligation "loop:memset:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e (e.choiceOcc.getD 1354 0) n)) :
    Uget.Chain.modelRun real (Schedule.setSteps n) e =
        .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real e (Schedule.setSteps n)) ∧
      SetNative.Post (rws.context (sourceAttributes rho caller) rows) e
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e (Schedule.setSteps n)) := by
  have env : EnvS (rws.context (sourceAttributes rho caller) rows) (sourceCatalogue rho caller) e 0 e :=
    Route7Entry.invG_at_entry spec rows mapping (memsetConsumer spec mapping base d n) codeScope image base
      (SetNative.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e (Schedule.setSteps n) n
      (setPast n) cfg ag sspec timers res ⟨statusRows.holds⟩
  obtain ⟨fin, run, post, _, _⟩ := run_s real (rws.context (sourceAttributes rho caller) rows) (sourceCatalogue rho caller)
    rws.nodup.holds e rws.args.holds env
  have final := CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (Schedule.setSteps n) e fin run
  rw [final]
  exact ⟨run, post⟩

/-- Fetched-PC evidence root for memset (same premises as the C1): every state of the exact run is at a reviewed
memset word (0x1c8 + 4j, j < 7) or at returnPC after the final RET. -/
theorem memset_fetch_covered_src (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base d fill returnPC : BitVec 64) (n : Nat)
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : NativeState) (ag : AgreesAt cfg e.regs) (sspec : SourceSpec rho caller spec)
    (timers : TimersQuiet e.regs (Schedule.setSteps n))
    (rws : MemsetRows spec mapping base d fill returnPC n e)
    (res : Route7Entry.EntryResidual spec rows mapping (memsetConsumer spec mapping base d n) codeScope image base
      (SetNative.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e)
    (statusRows : DeploymentObligation "loop:memset:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e (e.choiceOcc.getD 1354 0) n)) :
    ∀ k, k ≤ Schedule.setSteps n → ∃ z, Uget.Chain.modelRun real k e = .ok () z ∧
      PcOkS (rws.context (sourceAttributes rho caller) rows) z := by
  have env : EnvS (rws.context (sourceAttributes rho caller) rows) (sourceCatalogue rho caller) e 0 e :=
    Route7Entry.invG_at_entry spec rows mapping (memsetConsumer spec mapping base d n) codeScope image base
      (SetNative.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e (Schedule.setSteps n) n
      (setPast n) cfg ag sspec timers res ⟨statusRows.holds⟩
  obtain ⟨_, _, _, cov, _⟩ := run_s real (rws.context (sourceAttributes rho caller) rows) (sourceCatalogue rho caller)
    rws.nodup.holds e rws.args.holds env
  exact cov

end Route7Root
#print axioms Route7Root.memsetFromSource
#print axioms Route7Root.memset_fetch_covered_src
