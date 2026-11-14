-- CT1 v2.1 run-to-return distinct-secret witness for route-7 memset (/ add. 10-11, publish 79ae): the accepted
-- memset_ct1_witness tuple (DIT caller, dit1/dit2) plus rt1 discharged in-world as memset_ct0ret_witness (retA 0x500000 vs
-- Plan.B 0x400000, outside [(456, 484)], decided), with Route7Root.memsetCT1RetFromSource applied.
import CT1Witness.MemsetDit
import CT1Ret.Memset
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace CT1Witness.MemsetDit
open Sail Sail.ConcurrencyInterfaceV1
open ArmFull ArmCertWalk ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.MachineSource ReleaseProfile.GB10
open ArmCertLoop ArmCertLoop.ContractDraft Route7GB10 Route7GB10.Closed CertiFFI.Claim ArmBridge.CruxGenGuarded
open ArmCertLoop.SetNative Route7Set
open CT1Witness.Memset

/-- **memset CT1 v2.1 run-to-return distinct-secret witness**: every binder of `Route7Root.memsetCT1RetFromSource` (incl.
    dit1/dit2 and rt1_1/rt1_2) proved in-world, the secret fills differ (decided), and the CT1Ret conclusion holds. -/
theorem memset_ct1ret_witness (real : Type) [Sail.SailReal real] :
    ∃ (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
      (cfg1 : Configuration rho callers.first) (cfg2 : Configuration rho callers.second)
      (domain : QueryDomain) (spec : TopologyImageSpec domain) (rows : List PermissionRow)
      (mapping : BitVec 64 → Option Nat) (base d f1 f2 returnPC : BitVec 64) (n : Nat) (e1 e2 : ArmBridge.Draft.NativeState)
      (ag1 : AgreesAt cfg1 e1.regs) (ag2 : AgreesAt cfg2 e2.regs)
      (sspec1 : SourceSpec rho callers.first spec) (sspec2 : SourceSpec rho callers.second spec)
      (timers1 : TimersQuiet e1.regs (Schedule.setSteps n)) (timers2 : TimersQuiet e2.regs (Schedule.setSteps n))
      (rws1 : Route7Root.MemsetRows spec mapping base d f1 returnPC n e1)
      (rws2 : Route7Root.MemsetRows spec mapping base d f2 returnPC n e2)
      (res1 : Route7Entry.EntryResidual spec rows mapping (Route7Root.memsetConsumer spec mapping base d n) codeScope image
        base (SetNative.offset (rws1.context (sourceAttributes rho callers.first) rows)) rho callers.first e1)
      (res2 : Route7Entry.EntryResidual spec rows mapping (Route7Root.memsetConsumer spec mapping base d n) codeScope image
        base (SetNative.offset (rws2.context (sourceAttributes rho callers.second) rows)) rho callers.second e2)
      (statusRows1 : DeploymentObligation "loop:memset:tag-status-rows"
        (NativeMteTagCheck.TagStatusRows e1 (e1.choiceOcc.getD 1354 0) n))
      (statusRows2 : DeploymentObligation "loop:memset:tag-status-rows"
        (NativeMteTagCheck.TagStatusRows e2 (e2.choiceOcc.getD 1354 0) n))
      (dit1 : CallerContract "card:ct1-caller-dit" (e1.regs.PSTATE.DIT = 1#1))
      (dit2 : CallerContract "card:ct1-caller-dit" (e2.regs.PSTATE.DIT = 1#1))
      (rt1_1 : CallerContract "card:ct0-return-outside-code" (¬ CT0Ret.InCode base e1.regs.gpr[30] [(456, 484)]))
      (rt1_2 : CallerContract "card:ct0-return-outside-code" (¬ CT0Ret.InCode base e2.regs.gpr[30] [(456, 484)])),
      f1 ≠ f2 ∧
      (((PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record e1 e2
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
    (∀ j, j ≤ Schedule.setSteps n → (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).regs.PSTATE.DIT = 1#1) ∧
    (∀ j, j ≤ Schedule.setSteps n → (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).regs.PSTATE.DIT = 1#1) ∧
    (∀ k, k ≤ Schedule.setSteps n → ∃ z, Uget.Chain.modelRun real k e1 = .ok () z ∧ PcOkS (rws1.context (sourceAttributes rho callers.first) rows) z) ∧
    (∀ k, k ≤ Schedule.setSteps n → ∃ z, Uget.Chain.modelRun real k e2 = .ok () z ∧ PcOkS (rws2.context (sourceAttributes rho callers.second) rows) z) ∧
    (∀ k, k < Schedule.setSteps n → ∃ w ∈ CT1.Route7Word.code 9 7, (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 k).regs._PC = base + BitVec.ofNat 64 w.1 ∧
      CT1.Route7Word.WordAt mapping (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 k) base w.1 w.2) ∧
    (∀ k, k < Schedule.setSteps n → ∃ w ∈ CT1.Route7Word.code 9 7, (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 k).regs._PC = base + BitVec.ofNat 64 w.1 ∧
      CT1.Route7Word.WordAt mapping (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 k) base w.1 w.2) ∧
    CT1.Tables.Route7.memsetWords = ((ArmCertLoop.Generated.imageWords.drop ((ArmCertLoop.Generated.armcert_memset_entry - ArmCertLoop.Generated.imageStart) / 4)).take 7).map BitVec.toNat ∧
    (CT1.Route7Word.code 9 7).map (·.2) = CT1.Tables.Route7.memsetWords ∧
    CT1.Words.windowListed CT1.Tables.Route7.table CT1.Tables.Route7.memsetWords = true ∧
    CT1.Words.noSveSme CT1.Tables.Route7.memsetWords = true) ∧
    (∀ k, k < Schedule.setSteps n → CT0Ret.InCode base (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 k).regs._PC [(456, 484)]) ∧
    (∀ k, k < Schedule.setSteps n → CT0Ret.InCode base (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 k).regs._PC [(456, 484)]) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (Schedule.setSteps n)).regs._PC = e1.regs.gpr[30] ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (Schedule.setSteps n)).regs._PC = e2.regs.gpr[30] ∧
    ¬ CT0Ret.InCode base e1.regs.gpr[30] [(456, 484)] ∧
    ¬ CT0Ret.InCode base e2.regs.gpr[30] [(456, 484)]) := by
  obtain ⟨⟨rho⟩, callerOf, -, -⟩ := sourceDomainWitness
  obtain ⟨c0⟩ := callerOf rho
  let c : AdmissibleCaller rho := ditCallerOf c0
  let callers : AdmissibleCTCallers rho := AdmissibleCTCallers.ofCallers c c
  obtain ⟨spec, sspec, hl, hlr, hir⟩ := sourceSpec_of_tables rho c tables oracle
    (Plan.payload (gprsOf fill1) Generated.armcert_memset_entry 0#88).data
    (E rho c (gprsOf fill1) Generated.armcert_memset_entry 0#88) rfl
  have hir' : spec.imageRows = World.imageRows := hir
  have hlr' : spec.logicalRows = World.logicalRows := hlr
  have hlay' : spec.layout = World.layout := hl
  have rws1 := rows_at rho c fill1 spec hir' hlr'
  have rws2 := rows_at rho c fill2 spec hir' hlr'
  have t1 := model_timersQuiet worldSemantics rho c (Plan.payload (gprsOf fill1) Generated.armcert_memset_entry 0#88)
    (Plan.timers_disabled _ _ _) (Schedule.setSteps 1)
  have t2 := model_timersQuiet worldSemantics rho c (Plan.payload (gprsOf fill2) Generated.armcert_memset_entry 0#88)
    (Plan.timers_disabled _ _ _) (Schedule.setSteps 1)
  have ag1 := makeModelEntry_agrees worldSemantics rho c (Plan.payload (gprsOf fill1) Generated.armcert_memset_entry 0#88)
  have ag2 := makeModelEntry_agrees worldSemantics rho c (Plan.payload (gprsOf fill2) Generated.armcert_memset_entry 0#88)
  have res1 := residual_at rho c fill1 spec sspec hlr' hir' hlay' (fun _ h => h) rws1
  have res2 := residual_at rho c fill2 spec sspec hlr' hir' hlay' (fun _ h => h) rws2
  have st1 : DeploymentObligation "loop:memset:tag-status-rows" _ := ⟨status_rows rho c fill1 1⟩
  have st2 : DeploymentObligation "loop:memset:tag-status-rows" _ := ⟨status_rows rho c fill2 1⟩
  have d1 : CallerContract "card:ct1-caller-dit"
      ((E rho c (gprsOf fill1) Generated.armcert_memset_entry 0#88).regs.PSTATE.DIT = 1#1) := ⟨rfl⟩
  have d2 : CallerContract "card:ct1-caller-dit"
      ((E rho c (gprsOf fill2) Generated.armcert_memset_entry 0#88).regs.PSTATE.DIT = 1#1) := ⟨rfl⟩
  have rtOut : ¬ CT0Ret.InCode Plan.B retA [(456, 484)] := by unfold CT0Ret.InCode; decide
  have rt1A : CallerContract "card:ct0-return-outside-code" (¬ CT0Ret.InCode Plan.B (E rho c (gprsOf fill1) Generated.armcert_memset_entry 0#88).regs.gpr[30] [(456, 484)]) :=
    ⟨by first
      | (rw [rws1.args.holds.2.2.2]; exact rtOut)
      | (show ¬ CT0Ret.InCode Plan.B (HeapV2StepCerts.RegBind.regVal (E rho c (gprsOf fill1) Generated.armcert_memset_entry 0#88) (HeapV2StepCerts.RegBind.Reg.x 30)) [(456, 484)]
         rw [rws1.args.holds.2.2.2]; exact rtOut)⟩
  have rt1B : CallerContract "card:ct0-return-outside-code" (¬ CT0Ret.InCode Plan.B (E rho c (gprsOf fill2) Generated.armcert_memset_entry 0#88).regs.gpr[30] [(456, 484)]) :=
    ⟨by first
      | (rw [rws2.args.holds.2.2.2]; exact rtOut)
      | (show ¬ CT0Ret.InCode Plan.B (HeapV2StepCerts.RegBind.regVal (E rho c (gprsOf fill2) Generated.armcert_memset_entry 0#88) (HeapV2StepCerts.RegBind.Reg.x 30)) [(456, 484)]
         rw [rws2.args.holds.2.2.2]; exact rtOut)⟩
  refine ⟨rho, callers, Configuration.ofSource rho c, Configuration.ofSource rho c, _, spec, World.permissionRows,
    World.mapping, Plan.B, dA, fill1, fill2, retA, 1, _, _, ag1, ag2, sspec, sspec, t1, t2, rws1, rws2, res1, res2,
    st1, st2, d1, d2, rt1A, rt1B, by decide, ?_⟩
  exact Route7Root.memsetCT1RetFromSource real spec World.permissionRows World.mapping Plan.B dA fill1 fill2 retA 1 rho
    callers _ _ _ _ ag1 ag2 sspec sspec t1 t2 rws1 rws2 res1 res2 st1 st2 d1 d2 rt1A rt1B

end CT1Witness.MemsetDit
#print axioms CT1Witness.MemsetDit.memset_ct1ret_witness
