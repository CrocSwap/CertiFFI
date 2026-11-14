-- CT2 composed root for route-7 memmove: memmoveCT0FromSource's binders verbatim; conclusion =
-- CT0's conclusion ∧ the CT2.R0 held part at the same N; run facts from the CT2 run copy (Route7Move.CT2.run_m).
import CT2Route7.MemmoveR0
import Route7Root.CT0Move
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ReleaseProfile.MachineSource ReleaseProfile.GB10
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
open ArmCertLoop ArmCertLoop.ContractDraft Route7Move CertiFFI.Claim

namespace Route7Move.CT2

/-- memmove_r0's conclusion with the path made explicit (the root instantiates it at movePath d s n). -/
def R0Concl (p : Schedule.MovePath) (e1 e2 f1 f2 : ArmBridge.Draft.NativeState) : Prop :=
    f1.regs.gpr[0] = f2.regs.gpr[0] ∧ f1.regs.gpr[1] = f2.regs.gpr[1] ∧ f1.regs.gpr[2] = f2.regs.gpr[2] ∧
    (p = .forward ∨ p = .backward → f1.regs.gpr[3] = f2.regs.gpr[3]) ∧
    (p = .backward → f1.regs.gpr[4] = f2.regs.gpr[4]) ∧
    ((p = .empty ∨ p = .same) → f1.regs.gpr = e1.regs.gpr ∧ f2.regs.gpr = e2.regs.gpr) ∧
    (p = .forward → ∀ r : Fin 31, 5 ≤ r.val →
      f1.regs.gpr[r.val] = e1.regs.gpr[r.val] ∧ f2.regs.gpr[r.val] = e2.regs.gpr[r.val]) ∧
    (p = .backward → ∀ r : Fin 31, 6 ≤ r.val →
      f1.regs.gpr[r.val] = e1.regs.gpr[r.val] ∧ f2.regs.gpr[r.val] = e2.regs.gpr[r.val]) ∧
    f1.regs.SP_EL0 = e1.regs.SP_EL0 ∧ f2.regs.SP_EL0 = e2.regs.SP_EL0

end Route7Move.CT2

namespace Route7Root
open ArmCertLoop ArmCertLoop.ContractDraft Route7Move CertiFFI.Claim

/-- **memmove CT2.R0 (release root).** CT0's binders and relation (shared public base, d, s, n, returnPC); conclusion =
CT0's conclusion ∧ the per-path CT2.R0 held part at CT0's return step. Findings (not claimed): forward x4, backward x5
(last copied byte). -/
theorem memmoveCT2R0FromSource (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
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
    (    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.moveSteps (movePath d s n) n))
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.moveSteps (movePath d s n) n)) ∧
    (∀ j, j < (Schedule.moveSteps (movePath d s n) n) → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta) ∧
    (∀ j, j < (Schedule.moveSteps (movePath d s n) n) → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta)) ∧
    Route7Move.CT2.R0Concl (movePath d s n) e1 e2 (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.moveSteps (movePath d s n) n)) (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.moveSteps (movePath d s n) n)) := by
  obtain ⟨f1, r1, p1, _, _⟩ := Route7Move.CT2.run_m real (rws1.context (sourceAttributes rho callers.first) rows)
    (sourceCatalogue rho callers.first) rws1.nodup.holds e1 rws1.args.holds rws1.present.holds
    (memmove_env_at_entry spec rows mapping base d s returnPC n rho callers.first cfg1 e1 ag1 sspec1 timers1 rws1 res1
      statusRows1)
  obtain ⟨f2, r2, p2, _, _⟩ := Route7Move.CT2.run_m real (rws2.context (sourceAttributes rho callers.second) rows)
    (sourceCatalogue rho callers.second) rws2.nodup.holds e2 rws2.args.holds rws2.present.holds
    (memmove_env_at_entry spec rows mapping base d s returnPC n rho callers.second cfg2 e2 ag2 sspec2 timers2 rws2 res2
      statusRows2)
  refine ⟨memmoveCT0FromSource real spec rows mapping base d s returnPC n rho callers cfg1 cfg2 e1 e2 ag1 ag2 sspec1
    sspec2 timers1 timers2 rws1 rws2 res1 res2 statusRows1 statusRows2, ?_⟩
  have s1 := CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (Schedule.moveSteps (movePath d s n) n) e1 f1 r1
  have s2 := CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (Schedule.moveSteps (movePath d s n) n) e2 f2 r2
  rw [s1, s2]
  exact Route7Move.CT2.memmove_r0 (rws1.context (sourceAttributes rho callers.first) rows)
    (rws2.context (sourceAttributes rho callers.second) rows) rfl rfl rfl e1 e2 f1 f2
    rws1.args.holds rws2.args.holds p1 p2

end Route7Root
#print axioms Route7Root.memmoveCT2R0FromSource
