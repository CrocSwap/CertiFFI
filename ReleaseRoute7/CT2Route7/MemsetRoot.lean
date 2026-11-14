-- CT2 composed root for route-7 memset: memsetCT0FromSource's binders verbatim; conclusion =
-- CT0's conclusion ∧ the CT2.R0 (HELD) statement at the same N; run facts from the CT2 run copy (Route7Set.CT2.run_s).
import CT2Route7.SetRunR
import Route7Root.CT0Set
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ReleaseProfile.MachineSource ReleaseProfile.GB10
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
open ArmCertLoop ArmCertLoop.SetNative ArmCertLoop.ContractDraft Route7Set CertiFFI.Claim

namespace Route7Set.CT2
open ArmBridge.Draft
/-- memset CT2.R0 (HELD): public x0, x2, x3 (n>0) equal across runs; per run x1 = the caller's own secret fill (named,
G4), x3 unchanged when n = 0, x4..x30 and sp unchanged (caller-owned / callee-saved). Every GPR is covered. -/
def R0Concl (mapping : BitVec 64 → Option Nat) (d : BitVec 64) (n : Nat) (e1 e2 f1 f2 : NativeState) : Prop :=
  f1.regs.gpr[0] = f2.regs.gpr[0] ∧ f1.regs.gpr[2] = f2.regs.gpr[2] ∧ (0 < n → f1.regs.gpr[3] = f2.regs.gpr[3]) ∧
  (f1.regs.gpr[1] = e1.regs.gpr[1] ∧ f2.regs.gpr[1] = e2.regs.gpr[1]) ∧
  (n = 0 → f1.regs.gpr[3] = e1.regs.gpr[3] ∧ f2.regs.gpr[3] = e2.regs.gpr[3]) ∧
  (∀ r : Fin 31, 4 ≤ r.val → f1.regs.gpr[r.val] = e1.regs.gpr[r.val] ∧ f2.regs.gpr[r.val] = e2.regs.gpr[r.val]) ∧
  f1.regs.SP_EL0 = e1.regs.SP_EL0 ∧ f2.regs.SP_EL0 = e2.regs.SP_EL0 ∧
  -- R1: NZCV returned unchanged per run (the caller's own flags; named, never public)
  (HeapV2StepCerts.Flags.nzcv f1.regs = HeapV2StepCerts.Flags.nzcv e1.regs ∧
   HeapV2StepCerts.Flags.nzcv f2.regs = HeapV2StepCerts.Flags.nzcv e2.regs) ∧
  -- R2: every byte outside the declared output (the destination) is returned unchanged, per run
  (∀ pa, ¬ ArmCertLoop.ContractDraft.DestinationPA mapping d n pa → f1.mem[pa]? = e1.mem[pa]?) ∧
  (∀ pa, ¬ ArmCertLoop.ContractDraft.DestinationPA mapping d n pa → f2.mem[pa]? = e2.mem[pa]?) ∧
  -- R3: the vector register file (_Z, hence V0-V31) and FPSR returned unchanged, per run
  (f1.regs._Z = e1.regs._Z ∧ ArmFull.Register.FPSR.get f1.regs = ArmFull.Register.FPSR.get e1.regs) ∧
  (f2.regs._Z = e2.regs._Z ∧ ArmFull.Register.FPSR.get f2.regs = ArmFull.Register.FPSR.get e2.regs)

theorem r0_of_posts (c1 c2 : Context) (hd : c1.d = c2.d) (hn : c1.n = c2.n) (e1 e2 f1 f2 : NativeState)
    (a1 : Args c1 e1) (a2 : Args c2 e2)
    (hm : c1.mapping = c2.mapping)
    (p1 : Post c1 e1 f1 ∧ ExtraS c1 e1 f1) (p2 : Post c2 e2 f2 ∧ ExtraS c2 e2 f2) :
    R0Concl c1.mapping c1.d c1.n e1 e2 f1 f2 := by
  obtain ⟨⟨_, x0a, _, fra, ka, spa, za, _, fsa⟩, x1a, x2a, x3a, z_a, nza⟩ := p1
  obtain ⟨⟨_, x0b, _, frb, kb, spb, zb, _, fsb⟩, x1b, x2b, x3b, z_b, nzb⟩ := p2
  exact ⟨by rw [x0a, x0b, hd], BitVec.eq_of_toNat_eq (by rw [x2a, x2b]),
    fun pos => by rw [x3a pos, x3b (by omega), hd, hn], ⟨x1a.trans a1.2.1.symm, x1b.trans a2.2.1.symm⟩,
    fun z => ⟨z_a z, z_b (by omega)⟩, fun r hr => ⟨ka r hr, kb r hr⟩, spa, spb, ⟨nza, nzb⟩, fra,
    by rw [hm, hd, hn]; exact frb, ⟨za, fsa⟩, ⟨zb, fsb⟩⟩
end Route7Set.CT2

namespace Route7Root
open ArmCertLoop ArmCertLoop.SetNative ArmCertLoop.ContractDraft Route7Set CertiFFI.Claim

/-- **memset CT2.R3 (R0+R1+R2+R3) (release root): HELD.** CT0's binders and relation; conclusion = CT0's conclusion ∧ the CT2.R0
statement at CT0's return step (every GPR either equal across the runs or named: x1 = caller's own secret fill). -/
theorem memsetCT2R0FromSource (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base d fill1 fill2 returnPC : BitVec 64) (n : Nat)
    (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
    (cfg1 : Configuration rho callers.first) (cfg2 : Configuration rho callers.second)
    (e1 e2 : NativeState) (ag1 : AgreesAt cfg1 e1.regs) (ag2 : AgreesAt cfg2 e2.regs)
    (sspec1 : SourceSpec rho callers.first spec) (sspec2 : SourceSpec rho callers.second spec)
    (timers1 : TimersQuiet e1.regs (Schedule.setSteps n)) (timers2 : TimersQuiet e2.regs (Schedule.setSteps n))
    (rws1 : MemsetRows spec mapping base d fill1 returnPC n e1) (rws2 : MemsetRows spec mapping base d fill2 returnPC n e2)
    (res1 : Route7Entry.EntryResidual spec rows mapping (memsetConsumer spec mapping base d n) codeScope image base
      (SetNative.offset (rws1.context (sourceAttributes rho callers.first) rows)) rho callers.first e1)
    (res2 : Route7Entry.EntryResidual spec rows mapping (memsetConsumer spec mapping base d n) codeScope image base
      (SetNative.offset (rws2.context (sourceAttributes rho callers.second) rows)) rho callers.second e2)
    (statusRows1 : DeploymentObligation "loop:memset:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e1 (e1.choiceOcc.getD 1354 0) n))
    (statusRows2 : DeploymentObligation "loop:memset:tag-status-rows"
      (NativeMteTagCheck.TagStatusRows e2 (e2.choiceOcc.getD 1354 0) n)) :
    (    PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.setSteps n))
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.setSteps n)) ∧
    (∀ j, j < (Schedule.setSteps n) → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta) ∧
    (∀ j, j < (Schedule.setSteps n) → ∃ delta : Array Event,
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (j + 1)).events =
        (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).events ++ delta ∧
      ArmCertCTOrdered.OrderedEventV2.Covered delta)) ∧
    Route7Set.CT2.R0Concl mapping d n e1 e2 (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.setSteps n)) (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.setSteps n)) := by
  obtain ⟨f1, r1, p1, _, _⟩ := Route7Set.CT2.run_s real (rws1.context (sourceAttributes rho callers.first) rows)
    (sourceCatalogue rho callers.first) rws1.nodup.holds e1 rws1.args.holds
    (memset_env_at_entry spec rows mapping base d fill1 returnPC n rho callers.first cfg1 e1 ag1 sspec1 timers1 rws1 res1
      statusRows1)
  obtain ⟨f2, r2, p2, _, _⟩ := Route7Set.CT2.run_s real (rws2.context (sourceAttributes rho callers.second) rows)
    (sourceCatalogue rho callers.second) rws2.nodup.holds e2 rws2.args.holds
    (memset_env_at_entry spec rows mapping base d fill2 returnPC n rho callers.second cfg2 e2 ag2 sspec2 timers2 rws2 res2
      statusRows2)
  refine ⟨memsetCT0FromSource real spec rows mapping base d fill1 fill2 returnPC n rho callers cfg1 cfg2 e1 e2 ag1 ag2
    sspec1 sspec2 timers1 timers2 rws1 rws2 res1 res2 statusRows1 statusRows2, ?_⟩
  have s1 := CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (Schedule.setSteps n) e1 f1 r1
  have s2 := CertiFFI.Prog.Generic.ModelRunView.stateAt_of_run real (Schedule.setSteps n) e2 f2 r2
  rw [s1, s2]
  exact Route7Set.CT2.r0_of_posts (rws1.context (sourceAttributes rho callers.first) rows)
    (rws2.context (sourceAttributes rho callers.second) rows) rfl rfl e1 e2 f1 f2 rws1.args.holds rws2.args.holds rfl p1 p2

end Route7Root
#print axioms Route7Root.memsetCT2R0FromSource
