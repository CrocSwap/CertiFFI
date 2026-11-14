-- Route 7 / memcpy CT0 root (loops): two runs from two admitted callers of the same completion, with the same
-- public data (base, d, s, n, returnPC; the copied bytes are secret), have equal ordered V2 event records (PC / address
-- / width / kind, no data values) over the exact run: PhasedCT.TimingRec,. Model-trace equality, not a
-- hardware-timing claim (claim notes N2/N3: no DIT; single core, no concurrent writer).
import Route7Root.C1
import Route7CT.Covered
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ReleaseProfile.MachineSource ReleaseProfile.GB10
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Route7Root
open ArmCertLoop ArmCertLoop.CopyNative ArmCertLoop.ContractDraft Route7Copy CertiFFI.Claim

/-- **memcpy CT0**: paired runs with equal public (base, d, s, n, returnPC) from the canonical source
have equal ordered event records, every step of both runs appending an OrderedEventV2.Covered delta, over the exact copySteps n run. Each run carries its own source-bound C1
premises (agreement, SourceSpec, card rows, entry residual, tag-status rows); no run, invariant or trace is assumed. -/
theorem memcpyCT0FromSource (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base d s returnPC : BitVec 64) (n : Nat)
    (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
    (cfg1 : Configuration rho callers.first) (cfg2 : Configuration rho callers.second)
    (e1 e2 : NativeState) (ag1 : AgreesAt cfg1 e1.regs) (ag2 : AgreesAt cfg2 e2.regs)
    (sspec1 : SourceSpec rho callers.first spec) (sspec2 : SourceSpec rho callers.second spec)
    (timers1 : TimersQuiet e1.regs (Schedule.copySteps n)) (timers2 : TimersQuiet e2.regs (Schedule.copySteps n))
    (rws1 : MemcpyRows spec mapping base d s returnPC n e1) (rws2 : MemcpyRows spec mapping base d s returnPC n e2)
    (res1 : Route7Entry.EntryResidual spec rows mapping (memcpyConsumer spec mapping base d s n) codeScope image base
      (offset base returnPC n) rho callers.first e1)
    (res2 : Route7Entry.EntryResidual spec rows mapping (memcpyConsumer spec mapping base d s n) codeScope image base
      (offset base returnPC n) rho callers.second e2)
    (statusRows1 : DeploymentObligation "loop:memcpy:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e1 (e1.choiceOcc.getD 1354 0) (2 * n)))
    (statusRows2 : DeploymentObligation "loop:memcpy:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e2 (e2.choiceOcc.getD 1354 0) (2 * n))) :
    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.copySteps n))
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.copySteps n)) ∧
    (∀ j, j < (Schedule.copySteps n) → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta) ∧
    (∀ j, j < (Schedule.copySteps n) → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta) := by
  obtain ⟨f1, r1, post1, _, t1⟩ := memcpy_of_env real rws1 (sourceAttributes rho callers.first) rows
    (sourceCatalogue rho callers.first)
    (memcpy_env_at_entry spec rows mapping base d s returnPC n rho callers.first cfg1 e1 ag1 sspec1 timers1 rws1 res1
      statusRows1)
  obtain ⟨f2, r2, post2, _, t2⟩ := memcpy_of_env real rws2 (sourceAttributes rho callers.second) rows
    (sourceCatalogue rho callers.second)
    (memcpy_env_at_entry spec rows mapping base d s returnPC n rho callers.second cfg2 e2 ag2 sspec2 timers2 rws2 res2
      statusRows2)
  refine ⟨Route7Trace.ct_of_traced real spec mapping (recsOf (rws1.context (sourceAttributes rho callers.first) rows))
    (pcOf (rws1.context (sourceAttributes rho callers.first) rows)) (Schedule.copySteps n) e1 e2 f1 f2 t1 t2 r1 r2
    (post1.1.trans post2.1.symm) (res1.v1_pc.holds.trans res2.v1_pc.holds.symm),
    Route7Trace.traced_covered real spec mapping (recsOf (rws1.context (sourceAttributes rho callers.first) rows)) _ (Schedule.copySteps n) e1 t1 (Route7Copy.recs_some _),
    Route7Trace.traced_covered real spec mapping (recsOf (rws2.context (sourceAttributes rho callers.second) rows)) _ (Schedule.copySteps n) e2 t2 (Route7Copy.recs_some _)⟩

end Route7Root
#print axioms Route7Root.memcpyCT0FromSource
