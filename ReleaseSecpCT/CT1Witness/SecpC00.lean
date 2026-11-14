-- CT1 M4: distinct-secret non-vacuity witness for secp c00 CT0-DIT.
-- e1 = World entry (all operand bytes 0); e2 = XlateSecpAlt.World entry (operand byte 0x80601000:= 1, x1 limb 0
-- = 1 < p). Same completion, caller pair, semantics, oracle, tables, rows, mapping, base, pins and registers; every
-- Lean premise of secpCT0DitFromSource_c00 is proved in-world; the secret operand byte differs (decided).
import PipeLean_D234_SecpAdd_c00.CtSource
import SecpShimC2C00Alt
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace CT1Witness.SecpC00
open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.SecpShimRuntime

theorem byte1 (rho : AdmissibleSourceCompletion) (c : AdmissibleCaller rho) :
    (makeModelEntry worldSemantics rho c (XlateSecp.World.payload XlateSecp.ShimC00.card_shim_c00 0#88)).mem[2153779200]? = some 0#8 :=
  XlateSecp.World.entry_realizes worldSemantics rho c _ 0#88 (2153779200, 0#8) (by
    unfold XlateSecp.World.plan
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    unfold XlateSecp.World.dataPlan
    exact List.mem_flatMap.mpr ⟨(0x80601000, 32), by simp [XlateSecp.World.dataRanges],
      List.mem_map.mpr ⟨0, by simp, rfl⟩⟩)

theorem byte2 (rho : AdmissibleSourceCompletion) (c : AdmissibleCaller rho) :
    (makeModelEntry worldSemantics rho c (XlateSecpAlt.World.payload XlateSecp.ShimC00.card_shim_c00 0#88)).mem[2153779200]? = some 1#8 :=
  XlateSecpAlt.World.entry_realizes worldSemantics rho c _ 0#88 (2153779200, 1#8) (by
    unfold XlateSecpAlt.World.plan
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    unfold XlateSecpAlt.World.dataPlan
    exact List.mem_flatMap.mpr ⟨(0x80601000, 32), by simp [XlateSecp.World.dataRanges],
      List.mem_map.mpr ⟨0, by simp, by simp [XlateSecpAlt.World.dataByte]⟩⟩)

/-- Generic: two model entries from the same source completion and caller whose payload `data` parts agree are equal in
    every GPR. Stated over abstract payloads so the kernel never compares payload memories. -/
theorem same_of_data (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (c : AdmissibleCaller rho)
    (p1 p2 : ModelPayload) (h : p1.data = p2.data) :
    SecpCt.SameExceptOperands false (makeModelEntry sem rho c p1) (makeModelEntry sem rho c p2) :=
  ⟨fun i _ => by simp only [makeModelEntry, h]⟩

theorem card_eq : XlateSecp.ShimC00.card_shim_c00 = XlateSecp.ShimC00.card_shim_c00 := rfl

/-- The default and alt payloads share their `data` part (they differ only in memory). -/
theorem data_eq (pc : BitVec 88) :
    (XlateSecp.World.payload XlateSecp.ShimC00.card_shim_c00 pc).data =
      (XlateSecpAlt.World.payload XlateSecp.ShimC00.card_shim_c00 pc).data := by
  simp only [XlateSecp.World.payload, XlateSecpAlt.World.payload, card_eq]

theorem regions_cons : ∃ rest, PipeLean_D234_SecpAdd_c00.EntryBinding.plan.regions =
    (({ pin := 0, off := Int.ofNat 0, words := 4 } : ArmCertValue.Region), 32) ::
    (({ pin := 1, off := Int.ofNat 0, words := 4 } : ArmCertValue.Region), 32) :: rest := ⟨_, rfl⟩

theorem nb : ArmCertValue.totalL PipeLean_D234_SecpAdd_c00.EntryBinding.plan.regions = 96 := by decide

theorem va0 : XlateSecp.World.mapping (Sail.BitVec.addInt
    (if h : (PipeLean_D234_SecpAdd_c00.EntryBinding.plan.normalize { pin := 1, off := Int.ofNat 0, words := 4 }).pin < 31
      then (XlateSecp.World.data XlateSecp.ShimC00.card_shim_c00).gpr[(PipeLean_D234_SecpAdd_c00.EntryBinding.plan.normalize { pin := 1, off := Int.ofNat 0, words := 4 }).pin]
      else 0)
    ((PipeLean_D234_SecpAdd_c00.EntryBinding.plan.normalize { pin := 1, off := Int.ofNat 0, words := 4 }).off + ((0 : Nat) : Int)))
    = some 2153779200 := by decide

/-- Root operand vocabulary: input slot 32 (x1 operand region, byte 0 = limb 0 low byte) of any entry with the shim card GPRs is the
    byte at PA 0x80601000. -/
theorem input32 (e : ArmBridge.Draft.NativeState)
    (hg : e.regs.gpr = (XlateSecp.World.data XlateSecp.ShimC00.card_shim_c00).gpr) :
    (PipeLean_D234_SecpAdd_c00.Default.inputs XlateSecp.World.mapping e).getD 32 0 =
      ((e.mem[2153779200]?).getD 0).setWidth 64 := by
  obtain ⟨rest, hr⟩ := regions_cons
  simp only [PipeLean_D234_SecpAdd_c00.Default.inputs, TranslateSpan.SecpCurrentEntry.inputs, ArmCertValue.mkInputsL]
  rw [ArmCertValue.mkInputsG_getD _ _ _ _ (by rw [nb]; omega)]
  simp only [ArmCertValue.inputValG, nb, show (32 : Nat) < 96 by decide, ite_true]
  congr 1
  rw [hr]
  simp only [ArmCertValue.Physical.Entry.snapshot, show ¬ (32 : Nat) < 32 by decide, ite_false, Nat.sub_self,
    show (0 : Nat) < 32 by decide, ite_true,
    ArmCertValue.Physical.regionByte, TranslateSpan.SecpRawDeployment.view, TranslateSpan.SecpRawDeployment.regionVA,
    TranslateSpan.SecpRawDeployment.entryGPR, hg]
  rw [va0]
  rfl

theorem in1 (rho : AdmissibleSourceCompletion) (c : AdmissibleCaller rho) :
    (PipeLean_D234_SecpAdd_c00.Default.inputs XlateSecp.World.mapping
      (makeModelEntry worldSemantics rho c (XlateSecp.World.payload XlateSecp.ShimC00.card_shim_c00 0#88))).getD 32 0 = 0#64 := by
  rw [input32 _ rfl, byte1 rho c]; rfl

theorem in2 (rho : AdmissibleSourceCompletion) (c : AdmissibleCaller rho) :
    (PipeLean_D234_SecpAdd_c00.Default.inputs XlateSecp.World.mapping
      (makeModelEntry worldSemantics rho c (XlateSecpAlt.World.payload XlateSecp.ShimC00.card_shim_c00 0#88))).getD 32 0 = 1#64 := by
  rw [input32 _ rfl, byte2 rho c]; rfl

/-- **secp c00 CT0-DIT distinct-secret witness**: an ∃ over all 20 binders of `secpCT0DitFromSource_c00`, every
 premise proved in C2 world / WorldAlt, the entries equal in every GPR (SameExceptOperands), the operand byte at
    PA 0x80601000 (x1 limb 0) 0 vs 1 (decided), also in the root operand vocabulary: input slot 32 (x1 region byte 0) = 0 vs 1, and the CT0-DIT conclusion for this pair. -/
theorem secp_c00_witness (real : Type) [Sail.SailReal real] :
    ∃ (sem : ModelSemantics) (o : OracleChoice) (t : TranslateSpan.CheckedTopology.Tables)
      (rows : List ArmCert.Translate.Model.PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
      (pins : ArmCert.Translate.Model.HeapV2E17.Pins)
      (rho : AdmissibleSourceCompletion) (callers : AdmissibleCTCallers rho)
      (cfg1 : Configuration rho callers.first) (cfg2 : Configuration rho callers.second)
      (e1 e2 : ArmBridge.Draft.NativeState) (ag1 : AgreesAt cfg1 e1.regs) (ag2 : AgreesAt cfg2 e2.regs)
      (res1 : SecpResidual_c00 sem o t rows mapping base pins rho callers.first e1)
      (res2 : SecpResidual_c00 sem o t rows mapping base pins rho callers.second e2)
      (same : CertiFFI.Claim.CallerContract "card:secp-ct-same-except-operands" (SecpCt.SameExceptOperands false e1 e2)),
      e1.mem[2153779200]? = some 0#8 ∧ e2.mem[2153779200]? = some 1#8 ∧ (0#8 : BitVec 8) ≠ 1#8 ∧
      (PipeLean_D234_SecpAdd_c00.Default.inputs mapping e1).getD 32 0 = 0#64 ∧
      (PipeLean_D234_SecpAdd_c00.Default.inputs mapping e2).getD 32 0 = 1#64 ∧
      (((ArmBridge.CruxGenGuarded.PhasedCT.TimingRec ArmCertCTOrdered.OrderedEventV2.record
          (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 0) (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 0)
          (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 35) (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 35)) ∧
        (∀ j, j < 35 → ∃ delta : Array Sail.ConcurrencyInterfaceV1.Event, (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 (j + 1)).events =
          (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).events ++ delta ∧ ArmCertCTOrdered.OrderedEventV2.Covered delta) ∧
        (∀ j, j < 35 → ∃ delta : Array Sail.ConcurrencyInterfaceV1.Event, (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 (j + 1)).events =
          (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).events ++ delta ∧ ArmCertCTOrdered.OrderedEventV2.Covered delta)) ∧
        (∀ j, 5 ≤ j → j ≤ 33 → (CertiFFI.Prog.Generic.ModelRunView.stateAt real e1 j).regs.PSTATE.DIT = 1#1) ∧
        (∀ j, 5 ≤ j → j ≤ 33 → (CertiFFI.Prog.Generic.ModelRunView.stateAt real e2 j).regs.PSTATE.DIT = 1#1)) := by
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
  have ct := secpCT0DitFromSource_c00 real worldSemantics XlateSecp.Raw.oracle XlateSecp.World.tables
    XlateSecp.World.permissionRows XlateSecp.World.mapping XlateSecp.World.base XlateSecp.Shim.shimPins rho callers
    (Configuration.ofSource rho c) (Configuration.ofSource rho c) _ _ ag1 ag2 r1 r2 same
  exact ⟨_, _, _, _, _, _, _, rho, callers, _, _, _, _, ag1, ag2, r1, r2, same, byte1 rho c, byte2 rho c, by decide, in1 rho c, in2 rho c, ct⟩

end CT1Witness.SecpC00
#print axioms CT1Witness.SecpC00.secp_c00_witness
