-- Route 7 / memmove CT0 root (loops): two runs from two admitted callers with the same public data (base, d, s,
-- n, returnPC; hence the same public path) and possibly different (secret) source bytes have equal ordered event
-- records over the exact run, on every path (empty / same / forward / backward). Model-trace equality, not a
-- hardware-timing claim (claim notes N2/N3). No disjointness premise.
import Route7Root.Move
import Route7Trace.Move
import Route7CT.Covered
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ReleaseProfile.MachineSource ReleaseProfile.GB10
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Route7Root
open ArmCertLoop ArmCertLoop.ContractDraft Route7Move CertiFFI.Claim

/-- The memmove environment at the actual entry from the source-bound C1 premises (as in memmoveFromSource). -/
theorem memmove_env_at_entry {domain : QueryDomain} (spec : TopologyImageSpec domain) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base d s returnPC : BitVec 64) (n : Nat)
    (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho) (cfg : Configuration rho caller)
    (e : NativeState) (ag : AgreesAt cfg e.regs) (sspec : SourceSpec rho caller spec)
    (timers : TimersQuiet e.regs (Schedule.moveSteps (movePath d s n) n))
    (rws : MemmoveRows spec mapping base d s returnPC n e)
    (res : Route7Entry.EntryResidual spec rows mapping (memmoveConsumer spec mapping base d s n) codeScope image base
      (Route7Move.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e)
    (statusRows : DeploymentObligation "loop:memmove:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e (e.choiceOcc.getD 1354 0) (2 * n))) :
    EnvM (rws.context (sourceAttributes rho caller) rows) (sourceCatalogue rho caller) e 0 e :=
  Route7Entry.invG_at_entry spec rows mapping (memmoveConsumer spec mapping base d s n) codeScope image base
    (Route7Move.offset (rws.context (sourceAttributes rho caller) rows)) rho caller e
    (Schedule.moveSteps (movePath d s n) n) (2 * n) (movePast (movePath d s n) n) cfg ag sspec timers res
    ⟨statusRows.holds⟩

/-- **memmove CT0**: paired source-bound runs with equal public (base, d, s, n, returnPC) have equal
 ordered event records over the exact moveSteps (movePath d s n) n run, whatever the (secret) source bytes. -/
theorem memmoveCT0FromSource (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base d s returnPC : BitVec 64) (n : Nat)
    (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
    (cfg1 : Configuration rho callers.first) (cfg2 : Configuration rho callers.second)
    (e1 e2 : NativeState) (ag1 : AgreesAt cfg1 e1.regs) (ag2 : AgreesAt cfg2 e2.regs)
    (sspec1 : SourceSpec rho callers.first spec) (sspec2 : SourceSpec rho callers.second spec)
    (timers1 : TimersQuiet e1.regs (Schedule.moveSteps (movePath d s n) n))
    (timers2 : TimersQuiet e2.regs (Schedule.moveSteps (movePath d s n) n))
    (rws1 : MemmoveRows spec mapping base d s returnPC n e1) (rws2 : MemmoveRows spec mapping base d s returnPC n e2)
    (res1 : Route7Entry.EntryResidual spec rows mapping (memmoveConsumer spec mapping base d s n) codeScope image base
      (Route7Move.offset (rws1.context (sourceAttributes rho callers.first) rows)) rho callers.first e1)
    (res2 : Route7Entry.EntryResidual spec rows mapping (memmoveConsumer spec mapping base d s n) codeScope image base
      (Route7Move.offset (rws2.context (sourceAttributes rho callers.second) rows)) rho callers.second e2)
    (statusRows1 : DeploymentObligation "loop:memmove:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e1 (e1.choiceOcc.getD 1354 0) (2 * n)))
    (statusRows2 : DeploymentObligation "loop:memmove:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e2 (e2.choiceOcc.getD 1354 0) (2 * n))) :
    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.moveSteps (movePath d s n) n))
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.moveSteps (movePath d s n) n)) ∧
    (∀ j, j < (Schedule.moveSteps (movePath d s n) n) → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta) ∧
    (∀ j, j < (Schedule.moveSteps (movePath d s n) n) → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta) := by
  obtain ⟨f1, r1, post1, _, t1⟩ := run_m real (rws1.context (sourceAttributes rho callers.first) rows)
    (sourceCatalogue rho callers.first) rws1.nodup.holds e1 rws1.args.holds rws1.present.holds
    (memmove_env_at_entry spec rows mapping base d s returnPC n rho callers.first cfg1 e1 ag1 sspec1 timers1 rws1 res1
      statusRows1)
  obtain ⟨f2, r2, post2, _, t2⟩ := run_m real (rws2.context (sourceAttributes rho callers.second) rows)
    (sourceCatalogue rho callers.second) rws2.nodup.holds e2 rws2.args.holds rws2.present.holds
    (memmove_env_at_entry spec rows mapping base d s returnPC n rho callers.second cfg2 e2 ag2 sspec2 timers2 rws2 res2
      statusRows2)
  refine ⟨Route7Trace.ct_of_traced real spec mapping (recsOfM (rws1.context (sourceAttributes rho callers.first) rows))
    (pcOfM (rws1.context (sourceAttributes rho callers.first) rows)) (Schedule.moveSteps (movePath d s n) n)
    e1 e2 f1 f2 t1 t2 r1 r2 (post1.1.trans post2.1.symm) (res1.v1_pc.holds.trans res2.v1_pc.holds.symm),
    Route7Trace.traced_covered real spec mapping (recsOfM (rws1.context (sourceAttributes rho callers.first) rows)) _ (Schedule.moveSteps (movePath d s n) n) e1 t1 (Route7Move.recs_some_m _),
    Route7Trace.traced_covered real spec mapping (recsOfM (rws2.context (sourceAttributes rho callers.second) rows)) _ (Schedule.moveSteps (movePath d s n) n) e2 t2 (Route7Move.recs_some_m _)⟩

end Route7Root
#print axioms Route7Root.memmoveCT0FromSource
