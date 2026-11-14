-- CT1 v2.1 run-to-return distinct-secret witness for secp c00 (/ add. 10-11, publish 79ae): the SAME tuple as
-- secp_c00_ct1_witness / secp_c00_ct0ret_witness (low + rt1 proved in-world there), with secpCT1RetFromSource_c00 applied.
import CT1Witness.SecpC00Ret
import CT1Ret.Secp.C00
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace CT1Witness.SecpC00
open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.SecpShimRuntime

/-- **secp c00 CT1 v2.1 run-to-return distinct-secret witness**: every binder of `secpCT1RetFromSource_c00` (incl. low,
    rt1_1, rt1_2) proved in-world, x1 limb 0 = 0 vs 1, and the full CT1Ret conclusion. -/
theorem secp_c00_ct1ret_witness (real : Type) [Sail.SailReal real] :
    ∃ (sem : ModelSemantics) (o : OracleChoice) (t : TranslateSpan.CheckedTopology.Tables)
      (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
      (pins : ArmCert.Translate.Model.HeapV2E17.Pins)
      (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
      (cfg1 : Configuration rho callers.first) (cfg2 : Configuration rho callers.second)
      (e1 e2 : ArmBridge.Draft.NativeState) (ag1 : AgreesAt cfg1 e1.regs) (ag2 : AgreesAt cfg2 e2.regs)
      (res1 : SecpResidual_c00 sem o t rows mapping base pins rho callers.first e1)
      (res2 : SecpResidual_c00 sem o t rows mapping base pins rho callers.second e2)
      (same : CertiFFI.Claim.CallerContract "card:secp-ct-same-except-operands" (SecpCt.SameExceptOperands false e1 e2))
      (low : CertiFFI.Claim.DeploymentObligation "card:ct0-image-base-low" (base.toNat < 2 ^ 54))
      (rt1_1 : CertiFFI.Claim.CallerContract "card:ct0-return-outside-code" (¬ CT0Ret.InCode base e1.regs.gpr[30] [(8092, 8136), (5688, 5784)]))
      (rt1_2 : CertiFFI.Claim.CallerContract "card:ct0-return-outside-code" (¬ CT0Ret.InCode base e2.regs.gpr[30] [(8092, 8136), (5688, 5784)])),
      e1.mem[2153779200]? = some 0#8 ∧ e2.mem[2153779200]? = some 1#8 ∧ (0#8 : BitVec 8) ≠ 1#8 ∧
      (PipeLean_D234_SecpAdd_c00.Default.inputs mapping e1).getD 32 0 = 0#64 ∧
      (PipeLean_D234_SecpAdd_c00.Default.inputs mapping e2).getD 32 0 = 1#64 ∧
      ((((ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 0)
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 0) (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 35)
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 35) ∧
    (∀ j, j < 35 → ∃ delta : Array Sail.ConcurrencyInterfaceV1.Event, (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (j + 1)).events =
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).events ++ delta ∧ ArmCertCTOrdered.OrderedEventV2.Covered delta) ∧
    (∀ j, j < 35 → ∃ delta : Array Sail.ConcurrencyInterfaceV1.Event, (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (j + 1)).events =
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).events ++ delta ∧ ArmCertCTOrdered.OrderedEventV2.Covered delta)) ∧
    (∀ j, 5 ≤ j → j ≤ 33 → (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).regs.PSTATE.DIT = 1#1) ∧
    (∀ j, 5 ≤ j → j ≤ 33 → (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).regs.PSTATE.DIT = 1#1)) ∧
    (∀ k, k < 35 → ∃ w, w ∈ (DitShim243.Deployment.extend PipeLean_D234_SecpAdd_c00.EntryBinding.plan 8092 (67108257#26)).code ∧
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 k).regs._PC = base + BitVec.ofNat 64 w.fst ∧ _root_.CT1.SecpWordCommon.WordAt mapping (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 k) base w.fst w.snd) ∧
    (∀ k, k < 35 → ∃ w, w ∈ (DitShim243.Deployment.extend PipeLean_D234_SecpAdd_c00.EntryBinding.plan 8092 (67108257#26)).code ∧
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 k).regs._PC = base + BitVec.ofNat 64 w.fst ∧ _root_.CT1.SecpWordCommon.WordAt mapping (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 k) base w.fst w.snd) ∧
    _root_.CT1.Words.windowListed _root_.CT1.Tables.Secp.table (PipeLean_D234_SecpAdd_c00.EntryBinding.plan.code.map (·.2)) = true ∧
    _root_.CT1.Words.noSveSme ((DitShim243.Deployment.extend PipeLean_D234_SecpAdd_c00.EntryBinding.plan 8092 (67108257#26)).code.map (·.2)) = true ∧
    (DitShim243.Deployment.shimCode 8092 (67108257#26)).map (·.2) = _root_.CT1.SecpShim.template 2550136225 ∧
    _root_.CT1.Words.windowOrShim _root_.CT1.Tables.Secp.table (_root_.CT1.SecpShim.template 2550136225) ((DitShim243.Deployment.extend PipeLean_D234_SecpAdd_c00.EntryBinding.plan 8092 (67108257#26)).code.map (·.2)) = true ∧
    ((CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 35).regs.PSTATE.DIT = e1.regs.PSTATE.DIT ∧ (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 35).regs.SP_EL0 = e1.regs.SP_EL0 ∧
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 35).regs.gpr[30] = e1.regs.gpr[30]) ∧
    ((CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 35).regs.PSTATE.DIT = e2.regs.PSTATE.DIT ∧ (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 35).regs.SP_EL0 = e2.regs.SP_EL0 ∧
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 35).regs.gpr[30] = e2.regs.gpr[30])) ∧
    (∀ k, k < 35 → CT0Ret.InCode base (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 k).regs._PC [(8092, 8136), (5688, 5784)]) ∧
    (∀ k, k < 35 → CT0Ret.InCode base (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 k).regs._PC [(8092, 8136), (5688, 5784)]) ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 35).regs._PC = e1.regs.gpr[30] ∧
    (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 35).regs._PC = e2.regs.gpr[30] ∧
    ¬ CT0Ret.InCode base e1.regs.gpr[30] [(8092, 8136), (5688, 5784)] ∧
    ¬ CT0Ret.InCode base e2.regs.gpr[30] [(8092, 8136), (5688, 5784)]) := by
  obtain ⟨⟨rho⟩, callerOf, -, -⟩ := sourceDomainWitness
  obtain ⟨c⟩ := callerOf rho
  let callers : AdmissibleCTCallers rho := AdmissibleCTCallers.ofCallers c c
  have t1 := model_timersQuiet worldSemantics rho c (XlateSecp.World.payload XlateSecp.ShimC00.card_shim_c00 0#88)
    (fun _ _ => by show (0#64 : BitVec 64).getLsbD 0 = false; decide) (PipeLean_D234_SecpAdd_c00.EntryBinding.plan.code.length + 11)
  have t2 := model_timersQuiet worldSemantics rho c (XlateSecpAlt.World.payload XlateSecp.ShimC00.card_shim_c00 0#88)
    (fun _ _ => by show (0#64 : BitVec 64).getLsbD 0 = false; decide) (PipeLean_D234_SecpAdd_c00.EntryBinding.plan.code.length + 11)
  have r1 := C2C00.residual rho c XlateSecp.Raw.oracle 0#88 t1
  have r2 := C2C00Alt.residual rho c XlateSecp.Raw.oracle 0#88 t2
  have ag1 := makeModelEntry_agrees worldSemantics rho c (XlateSecp.World.payload XlateSecp.ShimC00.card_shim_c00 0#88)
  have ag2 := makeModelEntry_agrees worldSemantics rho c (XlateSecpAlt.World.payload XlateSecp.ShimC00.card_shim_c00 0#88)
  have same : CertiFFI.Claim.CallerContract "card:secp-ct-same-except-operands"
      (SecpCt.SameExceptOperands false
        (makeModelEntry worldSemantics rho c (XlateSecp.World.payload XlateSecp.ShimC00.card_shim_c00 0#88))
        (makeModelEntry worldSemantics rho c (XlateSecpAlt.World.payload XlateSecp.ShimC00.card_shim_c00 0#88))) :=
    ⟨same_of_data worldSemantics rho c _ _ (data_eq 0#88)⟩
  have low : CertiFFI.Claim.DeploymentObligation "card:ct0-image-base-low" (XlateSecp.World.base.toNat < 2 ^ 54) :=
    ⟨base_low⟩
  have rt1a : CertiFFI.Claim.CallerContract "card:ct0-return-outside-code"
      (¬ CT0Ret.InCode XlateSecp.World.base
        (makeModelEntry worldSemantics rho c (XlateSecp.World.payload XlateSecp.ShimC00.card_shim_c00 0#88)).regs.gpr[30]
        [(8092, 8136), (5688, 5784)]) := ⟨by rw [lr1]; exact lr_outside⟩
  have rt1b : CertiFFI.Claim.CallerContract "card:ct0-return-outside-code"
      (¬ CT0Ret.InCode XlateSecp.World.base
        (makeModelEntry worldSemantics rho c (XlateSecpAlt.World.payload XlateSecp.ShimC00.card_shim_c00 0#88)).regs.gpr[30]
        [(8092, 8136), (5688, 5784)]) := ⟨by rw [lr2]; exact lr_outside⟩
  have ret := secpCT1RetFromSource_c00 real worldSemantics XlateSecp.Raw.oracle XlateSecp.World.tables
    XlateSecp.World.permissionRows XlateSecp.World.mapping XlateSecp.World.base XlateSecp.Shim.shimPins rho callers
    (Configuration.ofSource rho c) (Configuration.ofSource rho c) _ _ ag1 ag2 r1 r2 same low rt1a rt1b
  exact ⟨_, _, _, _, _, _, _, rho, callers, _, _, _, _, ag1, ag2, r1, r2, same, low, rt1a, rt1b, byte1 rho c, byte2 rho c,
    by decide, in1 rho c, in2 rho c, ret⟩

end CT1Witness.SecpC00
#print axioms CT1Witness.SecpC00.secp_c00_ct1ret_witness
