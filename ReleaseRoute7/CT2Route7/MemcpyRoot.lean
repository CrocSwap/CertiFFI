-- CT2 composed root for route-7 memcpy: memcpyCT0FromSource's binders verbatim; conclusion =
-- CT0's conclusion ∧ the CT2.R0 held part at the same N; run facts from the CT2 run copy (Route7Copy.CT2.run_r).
import CT2Route7.CopyRun
import Route7Root.CT0
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ReleaseProfile.MachineSource ReleaseProfile.GB10
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
open ArmCertLoop ArmCertLoop.CopyNative ArmCertLoop.ContractDraft Route7Copy CertiFFI.Claim

namespace Route7Copy.CT2
open ArmBridge.Draft
/-- memcpy CT2.R0 held part at return (public d, s, n shared). Finding (n > 0, not claimed): x4 = last copied byte. -/
def R0Concl (n : Nat) (e1 e2 f1 f2 : NativeState) : Prop :=
  f1.regs.gpr[0] = f2.regs.gpr[0] ∧ f1.regs.gpr[1] = f2.regs.gpr[1] ∧ f1.regs.gpr[2] = f2.regs.gpr[2] ∧
  (0 < n → f1.regs.gpr[3] = f2.regs.gpr[3]) ∧
  (n = 0 → (f1.regs.gpr[3] = e1.regs.gpr[3] ∧ f1.regs.gpr[4] = e1.regs.gpr[4]) ∧
           (f2.regs.gpr[3] = e2.regs.gpr[3] ∧ f2.regs.gpr[4] = e2.regs.gpr[4])) ∧
  (∀ r : Fin 31, 5 ≤ r.val → f1.regs.gpr[r.val] = e1.regs.gpr[r.val] ∧ f2.regs.gpr[r.val] = e2.regs.gpr[r.val]) ∧
  f1.regs.SP_EL0 = e1.regs.SP_EL0 ∧ f2.regs.SP_EL0 = e2.regs.SP_EL0

theorem r0_of_posts (c1 c2 : Context) (hd : c1.d = c2.d) (hs : c1.s = c2.s) (hn : c1.n = c2.n)
    (e1 e2 f1 f2 : NativeState)
    (p1 : ArmCertLoop.ContractDraft.CopyPost c1.mapping c1.d c1.s c1.returnPC c1.n e1 f1 ∧ ExtraR c1 e1 f1)
    (p2 : ArmCertLoop.ContractDraft.CopyPost c2.mapping c2.d c2.s c2.returnPC c2.n e2 f2 ∧ ExtraR c2 e2 f2) :
    R0Concl c1.n e1 e2 f1 f2 := by
  obtain ⟨⟨_, x0a, _, _, _, spa, _⟩, x1a, x2a, x3a, z_a, ka⟩ := p1
  obtain ⟨⟨_, x0b, _, _, _, spb, _⟩, x1b, x2b, x3b, z_b, kb⟩ := p2
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ⟨ka r hr, kb r hr⟩, spa, spb⟩
  · change f1.regs.gpr[0] = c1.d at x0a; change f2.regs.gpr[0] = c2.d at x0b
    rw [x0a, x0b, hd]
  · rw [x1a, x1b, hs, hn]
  · exact BitVec.eq_of_toNat_eq (by rw [x2a, x2b])
  · intro pos; rw [x3a pos, x3b (by omega), hd, hn]
  · intro z; exact ⟨z_a z, z_b (by omega)⟩
end Route7Copy.CT2

namespace Route7Root
open ArmCertLoop ArmCertLoop.CopyNative ArmCertLoop.ContractDraft Route7Copy CertiFFI.Claim

/-- **memcpy CT2.R0 (release root).** CT0's binders and relation; conclusion = CT0's conclusion ∧ the CT2.R0 held part
at CT0's return step. Finding (not claimed, n > 0): x4 = last copied byte. -/
theorem memcpyCT2R0FromSource (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
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
    (    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.copySteps n))
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.copySteps n)) ∧
    (∀ j, j < (Schedule.copySteps n) → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta) ∧
    (∀ j, j < (Schedule.copySteps n) → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta)) ∧
    Route7Copy.CT2.R0Concl n e1 e2 (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.copySteps n)) (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.copySteps n)) := by
  obtain ⟨f1, r1, p1, _, _⟩ := Route7Copy.CT2.run_r real (rws1.context (sourceAttributes rho callers.first) rows)
    (sourceCatalogue rho callers.first) rws1.nodup.holds e1 rws1.args.holds rws1.present.holds
    (memcpy_env_at_entry spec rows mapping base d s returnPC n rho callers.first cfg1 e1 ag1 sspec1 timers1 rws1 res1
      statusRows1)
  obtain ⟨f2, r2, p2, _, _⟩ := Route7Copy.CT2.run_r real (rws2.context (sourceAttributes rho callers.second) rows)
    (sourceCatalogue rho callers.second) rws2.nodup.holds e2 rws2.args.holds rws2.present.holds
    (memcpy_env_at_entry spec rows mapping base d s returnPC n rho callers.second cfg2 e2 ag2 sspec2 timers2 rws2 res2
      statusRows2)
  refine ⟨memcpyCT0FromSource real spec rows mapping base d s returnPC n rho callers cfg1 cfg2 e1 e2 ag1 ag2 sspec1
    sspec2 timers1 timers2 rws1 rws2 res1 res2 statusRows1 statusRows2, ?_⟩
  have s1 := CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (Schedule.copySteps n) e1 f1 r1
  have s2 := CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (Schedule.copySteps n) e2 f2 r2
  rw [s1, s2]
  exact Route7Copy.CT2.r0_of_posts (rws1.context (sourceAttributes rho callers.first) rows)
    (rws2.context (sourceAttributes rho callers.second) rows) rfl rfl rfl e1 e2 f1 f2 p1 p2

end Route7Root
#print axioms Route7Root.memcpyCT2R0FromSource
