-- Route 7 / memmove C1 roots (loops): card rows (NO disjointness), the memmove Context, the entry invariant from
-- Route7Entry.invG_at_entry (capacity 2n, movePast, moveSteps of the public path), the run from run_m.
import Route7Move.Run
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
open ArmCertLoop ArmCertLoop.ContractDraft Route7Move CertiFFI.Claim

/-- memmove card rows: memcpy's minus disjointness (the spans may overlap). -/
structure MemmoveRows {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base d s returnPC : BitVec 64) (n : Nat) (e : NativeState) : Prop where
  page : DeploymentObligation "loop:load-base-page" (base.toNat % 4096 = 0)
  low : DeploymentObligation "loop:load-base-low" (base.toNat < 2 ^ 54)
  returnLow : CallerContract "loop:return-canonical" (returnPC.toNat < 2 ^ 54)
  sourceObject : CallerContract "loop:memmove:source-object" (SpanMap.NoWrap (sourceSpan s n))
  destObject : CallerContract "loop:memmove:destination-object" (SpanMap.NoWrap (destSpan d n))
  code : DeploymentObligation "loop:code-geometry" (CodeGeometry mapping base)
  codeWrite : DeploymentObligation "loop:code-write-separated" (CodeWriteSeparated mapping base d n)
  data : DeploymentObligation "loop:data-geometry" (DataGeometry mapping d s n (rowsFootprint spec.imageRows).byte)
  injective : DeploymentObligation "loop:union-injective" (SpanMap.UnionInjective mapping (spans d s n))
  separated : DeploymentObligation "loop:image-table-separated"
    (ImageTableSeparated codeScope base mapping (rowsFootprint spec.imageRows).byte)
  args : CallerContract "loop:memmove:args" (ContractDraft.Args d s returnPC n e)
  present : CallerContract "loop:memmove:source-present" (ContractDraft.SourcePresent mapping s n e)
  nodup : DeploymentObligation "E34" ((spec.logicalRows.map (·.logical)).Nodup)

def MemmoveRows.context {domain : QueryDomain} {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {base d s returnPC : BitVec 64} {n : Nat} {e : NativeState}
    (r : MemmoveRows spec mapping base d s returnPC n e) (config : AttributeConfig) (rows : List PermissionRow) :
    Route7Move.Context where
  domain := domain
  spec := spec
  config := config
  rows := rows
  mapping := mapping
  base := base
  d := d
  s := s
  returnPC := returnPC
  n := n
  page := r.page.holds
  low := r.low.holds
  returnLow := r.returnLow.holds
  sourceObject := r.sourceObject.holds
  destObject := r.destObject.holds
  code := r.code.holds
  codeWrite := r.codeWrite.holds
  data := r.data.holds
  injective := r.injective.holds
  separated := r.separated.holds

abbrev memmoveConsumer {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base d s : BitVec 64) (n : Nat) : ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  SpanMap.consumerMap (spans d s n) (Image.codeVAs base Generated.imageStart Generated.imageWords)
    mapping (rowsFootprint spec.imageRows).byte

/-- **memmove C1**: from the canonical source and the actual entry, the reviewed memmove runs exactly
moveSteps (movePath d s n) n steps to stateAt e (that count), which satisfies MovePost: ∀ i < n, byte(d+i) at the end
= byte(s+i) at ENTRY, even when the spans overlap; frame / registers as in the card. No disjointness premise. -/
theorem memmoveFromSource (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base d s returnPC : BitVec 64) (n : Nat)
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : NativeState) (ag : AgreesAt cfg e.regs) (sspec : SourceSpec rho caller spec)
    (timers : TimersQuiet e.regs (Schedule.moveSteps (movePath d s n) n))
    (rws : MemmoveRows spec mapping base d s returnPC n e)
    (res : Route7Entry.EntryResidual spec rows mapping (memmoveConsumer spec mapping base d s n) codeScope image base
      (Route7Move.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e)
    (statusRows : DeploymentObligation "loop:memmove:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e (e.choiceOcc.getD 1354 0) (2 * n))) :
    Uget.Chain.modelRun real (Schedule.moveSteps (movePath d s n) n) e =
        .ok () (CertiFFI.Prog.Generic.ModelRunView.stateAt real e (Schedule.moveSteps (movePath d s n) n)) ∧
      MovePost mapping d s returnPC n e
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e (Schedule.moveSteps (movePath d s n) n)) := by
  have env : EnvM (rws.context (sourceAttributes rho caller) rows) (sourceCatalogue rho caller) e 0 e :=
    Route7Entry.invG_at_entry spec rows mapping (memmoveConsumer spec mapping base d s n) codeScope image base
      (Route7Move.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e
      (Schedule.moveSteps (movePath d s n) n) (2 * n) (movePast (movePath d s n) n) cfg ag sspec timers res
      ⟨statusRows.holds⟩
  obtain ⟨fin, run, post, _, _⟩ := run_m real (rws.context (sourceAttributes rho caller) rows) (sourceCatalogue rho caller)
    rws.nodup.holds e rws.args.holds rws.present.holds env
  have final := CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (Schedule.moveSteps (movePath d s n) n) e fin run
  rw [final]
  exact ⟨run, post⟩

/-- Fetched-PC evidence root for memmove (same premises as the C1): every state of the exact run, on whichever public
path (empty / same / forward / backward), is at a reviewed memmove word (0x1e4 + 4j, j < 21) or at returnPC. -/
theorem memmove_fetch_covered_src (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base d s returnPC : BitVec 64) (n : Nat)
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : NativeState) (ag : AgreesAt cfg e.regs) (sspec : SourceSpec rho caller spec)
    (timers : TimersQuiet e.regs (Schedule.moveSteps (movePath d s n) n))
    (rws : MemmoveRows spec mapping base d s returnPC n e)
    (res : Route7Entry.EntryResidual spec rows mapping (memmoveConsumer spec mapping base d s n) codeScope image base
      (Route7Move.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e)
    (statusRows : DeploymentObligation "loop:memmove:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e (e.choiceOcc.getD 1354 0) (2 * n))) :
    ∀ k, k ≤ Schedule.moveSteps (movePath d s n) n → ∃ z, Uget.Chain.modelRun real k e = .ok () z ∧
      PcOkM (rws.context (sourceAttributes rho caller) rows) z := by
  have env : EnvM (rws.context (sourceAttributes rho caller) rows) (sourceCatalogue rho caller) e 0 e :=
    Route7Entry.invG_at_entry spec rows mapping (memmoveConsumer spec mapping base d s n) codeScope image base
      (Route7Move.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e
      (Schedule.moveSteps (movePath d s n) n) (2 * n) (movePast (movePath d s n) n) cfg ag sspec timers res
      ⟨statusRows.holds⟩
  obtain ⟨_, _, _, cov, _⟩ := run_m real (rws.context (sourceAttributes rho caller) rows) (sourceCatalogue rho caller)
    rws.nodup.holds e rws.args.holds rws.present.holds env
  exact cov

end Route7Root
#print axioms Route7Root.memmoveFromSource
#print axioms Route7Root.memmove_fetch_covered_src
