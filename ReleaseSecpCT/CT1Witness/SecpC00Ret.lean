-- CT0 v2.1 run-to-return distinct-secret witness: the return-stated root
-- secpCT0RetFromSource_c00 applied to the SAME distinct-secret tuple as secp_c00_witness / secp_c00_ct1_witness, with its
-- extra premises proved in-world: low (World.base < 2^54, decided) and rt1 (the world caller LR 0x400000 lies outside
-- RANGES = [shim certiffi_bignum_add_p256k1_dit, body bignum_add_p256k1], decided on the constant).
import CT1Witness.SecpC00CT1
import CT0Ret.Secp.C00
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace CT1Witness.SecpC00
open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.SecpShimRuntime

/-- The world caller LR (x30) of the shim card data. -/
theorem data_lr : (XlateSecp.World.data XlateSecp.ShimC00.card_shim_c00).gpr[30] = 0x400000#64 := by decide

theorem lr1 (rho : AdmissibleSourceCompletion) (c : AdmissibleCaller rho) :
    (makeModelEntry worldSemantics rho c (XlateSecp.World.payload XlateSecp.ShimC00.card_shim_c00 0#88)).regs.gpr[30] =
      0x400000#64 := by
  show (XlateSecp.World.data XlateSecp.ShimC00.card_shim_c00).gpr[30] = _
  exact data_lr

theorem lr2 (rho : AdmissibleSourceCompletion) (c : AdmissibleCaller rho) :
    (makeModelEntry worldSemantics rho c (XlateSecpAlt.World.payload XlateSecp.ShimC00.card_shim_c00 0#88)).regs.gpr[30] =
      0x400000#64 := by
  show (XlateSecp.World.data XlateSecp.ShimC00.card_shim_c00).gpr[30] = _
  rw [card_eq]; exact data_lr

theorem base_low : XlateSecp.World.base.toNat < 2 ^ 54 := by decide

theorem lr_outside : ¬ CT0Ret.InCode XlateSecp.World.base 0x400000#64 [(8092, 8136), (5688, 5784)] := by
  unfold CT0Ret.InCode; decide

/-- **secp c00 CT0 v2.1 run-to-return distinct-secret witness**: an ∃ over EVERY binder of `secpCT0RetFromSource_c00`
    (the 20 CT0 binders + low + rt1_1 + rt1_2), each premise proved in-world, x1 limb 0 = 0 vs 1 (PA 0x80601000 / input
    slot 32, decided), and the Ret root's full conclusion for this pair. -/
theorem secp_c00_ct0ret_witness (real : Type) [Sail.SailReal real] :
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
      ((    ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 0)
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 0) (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 35)
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 35) ∧
    (∀ j, j < 35 → ∃ delta : Array Sail.ConcurrencyInterfaceV1.Event, (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (j + 1)).events =
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).events ++ delta ∧ ArmCertCTOrdered.OrderedEventV2.Covered delta) ∧
    (∀ j, j < 35 → ∃ delta : Array Sail.ConcurrencyInterfaceV1.Event, (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (j + 1)).events =
      (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).events ++ delta ∧ ArmCertCTOrdered.OrderedEventV2.Covered delta)) ∧
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
  have ret := secpCT0RetFromSource_c00 real worldSemantics XlateSecp.Raw.oracle XlateSecp.World.tables
    XlateSecp.World.permissionRows XlateSecp.World.mapping XlateSecp.World.base XlateSecp.Shim.shimPins rho callers
    (Configuration.ofSource rho c) (Configuration.ofSource rho c) _ _ ag1 ag2 r1 r2 same low rt1a rt1b
  exact ⟨_, _, _, _, _, _, _, rho, callers, _, _, _, _, ag1, ag2, r1, r2, same, low, rt1a, rt1b, byte1 rho c, byte2 rho c,
    by decide, in1 rho c, in2 rho c, ret⟩

end CT1Witness.SecpC00
#print axioms CT1Witness.SecpC00.secp_c00_ct0ret_witness
