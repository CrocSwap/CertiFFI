import ReleaseProfile.GB10.HeapTrapInst
import ReleaseProfile.GB10.HeapTrapClosed
import ReleaseProfile.GB10.HeapC2Variant

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-! Heap Initial5 (TrapPath 10) positive C2 at the trap world `HeapTrapWorld.world 5`.
Tables: `HeapTrapTables` (normal + VA page 0). Translate statics: `Heap.TrapInst`, closed: `HeapTrapClosed`;
images/no-update: `Variant.images_tw`/`a211_tw` with the trap tables' finite checks. -/

namespace ReleaseProfile.GB10.Heap.Trap.T5

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Normal
open ReleaseProfile.GB10.Heap.TrapInst (Wt Et)

abbrev t : HeapTrapWorld.T := 5

variable (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)

theorem images (pcount : BitVec 88) {specCaller : AdmissibleCaller rho}
    {spec : ArmCert.Translate.Model.TopologyImageSpec (fun q => ∃ q0 ∈ HeapTrapTables.queries, ArmCertWalk.SamePage q0.va q.va)}
    (sspec : SourceSpec rho specCaller spec) (hir : spec.imageRows = HeapTrapTables.tables.imageRows) :
    ArmCert.Translate.Model.CurrentImagesAt spec (sourceAttributes rho caller) (Wt t).rows
        (ArmBridge.CruxGenGuarded.beforeFetchState (Et rho caller t pcount)) ∧
      ArmCertWalk.RawImageAt spec.imageRows (ArmBridge.CruxGenGuarded.beforeFetchState (Et rho caller t pcount)).mem :=
  Variant.images_tw rho caller pcount (Wt t) HeapTrapTables.tables rfl
    (by unfold ArmCert.Translate.Model.PermissionRowsDeclared; decide) (by decide) (by decide)
    (fun b => by cases b <;> decide) (by decide)
    (fun c h1 h2 h3 h4 h5 => by
      simp only [checkPermissionImageNoOverlay, permissionParamsView, Variant.imageParamsLit,
        ArmCertWalk.descriptorPermissionView, S1LogicalReference.leafPermissions,
        S1LogicalReference.classicPermissions, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]
      decide)
    sspec hir

theorem a121 (pcount : BitVec 88) : CertiFFI.Claim.DeploymentObligation "card:default-initial/v1/pc"
    ((Et rho caller t pcount).regs._PC = (Wt t).base + (Wt t).offS 0) := by
  refine ⟨?_⟩
  show (HeapTrapWorld.data t)._PC = HeapWorldData.base + HeapV2Card.Instance.offS 0
  rw [HeapV2Card.Instance.rc_offPre 0 (by decide)]
  decide

theorem a257 (pcount : BitVec 88) : CertiFFI.Claim.CallerContract "comp:caller:shim-caller-contract"
    ((Et rho caller t pcount).regs.SP_EL0 = BitVec.ofNat 64 (Wt t).pins.sp + BitVec.ofInt 64 16) := by
  refine ⟨?_⟩
  show (HeapTrapWorld.data t).SP_EL0 = BitVec.ofNat 64 (HeapTrapWorld.pins t).sp + BitVec.ofInt 64 16
  decide

theorem a267 (pcount : BitVec 88) : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers"
    (HeapV2StepCerts.RegBind.regVal (Et rho caller t pcount) (HeapV2StepCerts.RegBind.Reg.x 0) =
      BitVec.ofInt 64 ↑(Wt t).pins.x0) := by
  refine ⟨?_⟩
  simp only [HeapV2StepCerts.RegBind.regVal]
  show (HeapTrapWorld.data t).gpr[((0 : Fin 31) : Nat)] = BitVec.ofInt 64 ↑(HeapTrapWorld.pins t).x0
  decide

theorem a268 (pcount : BitVec 88) : CertiFFI.Claim.CallerContract "comp:caller:caller-buffers"
    (HeapV2StepCerts.RegBind.regVal (Et rho caller t pcount) (HeapV2StepCerts.RegBind.Reg.x 1) =
      BitVec.ofInt 64 ↑(Wt t).pins.x1) := by
  refine ⟨?_⟩
  simp only [HeapV2StepCerts.RegBind.regVal]
  show (HeapTrapWorld.data t).gpr[((1 : Fin 31) : Nat)] = BitVec.ofInt 64 ↑(HeapTrapWorld.pins t).x1
  decide

theorem a276 (pcount : BitVec 88) : CertiFFI.Claim.CallerContract "card:path-selector"
    (HeapV2StepCerts.ValBind.TrapPath 10 (Wt t).pins (HeapV2StepCerts.E17General.qOf (Et rho caller t pcount))) := by
  refine ⟨?_⟩
  simp only [HeapV2StepCerts.ValBind.TrapPath]
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · show 32 ≤ (HeapV2StepCerts.RegBind.regVal (Et rho caller t pcount) (.x 2)).toNat
    simp only [HeapV2StepCerts.RegBind.regVal]
    show 32 ≤ (HeapTrapWorld.data t).gpr[((2 : Fin 31) : Nat)].toNat
    decide
  · show HeapV2StepCerts.RegBind.regVal (Et rho caller t pcount) (.x 3) ≠ 32#64
    simp only [HeapV2StepCerts.RegBind.regVal]
    show (HeapTrapWorld.data t).gpr[((3 : Fin 31) : Nat)] ≠ 32#64
    decide

end ReleaseProfile.GB10.Heap.Trap.T5

