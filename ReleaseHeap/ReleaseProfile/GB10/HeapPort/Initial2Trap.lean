import ReleaseProfile.GB10.HeapPort.Initial2C2
import ReleaseProfile.GB10.HeapTrapInst
import ReleaseProfile.GB10.HeapTrapClosed
import ReleaseProfile.GB10.HeapC2Variant

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-! Heap Initial2 (TrapPath 4) positive C2 at the trap world `HeapTrapWorld.world 2`.
Tables: `HeapTrapTables` (normal + VA page 0). Translate statics: `Heap.TrapInst`, closed: `HeapTrapClosed`;
images/no-update: `Variant.images_tw`/`a211_tw` with the trap tables' finite checks. -/

namespace ReleaseProfile.GB10.Heap.Trap.T2

open ReleaseProfile.MachineSource ReleaseProfile.GB10 ReleaseProfile.GB10.Heap ReleaseProfile.GB10.Heap.Normal
open ReleaseProfile.GB10.Heap.TrapInst (Wt Et)

abbrev t : HeapTrapWorld.T := 2

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
    (HeapV2StepCerts.ValBind.TrapPath 4 (Wt t).pins (HeapV2StepCerts.E17General.qOf (Et rho caller t pcount))) := by
  refine ⟨?_⟩
  simp only [HeapV2StepCerts.ValBind.TrapPath]
  decide

#check "CURRENT_DECL GB10.Heap.Trap.T2.initial2_c2"
theorem initial2_c2 : Initial2C2 rho caller :=
  initial2_c2_reduce rho caller worldSemantics (worldPayload (Wt t)) (fun _ => rfl) HeapTrapTables.tables
    HeapWorldData.oracle (Wt t).rows (Wt t).mapping (Wt t).pins (Wt t).scope (Wt t).image (Wt t).loadBase
    (Wt t).base (Wt t).offS (Wt t).budget (Wt t).tablePlan (fun _ => timers_disabled)
    (fun pcount spec sspec hlay hlr hir timers =>
      have imgs := images rho caller pcount sspec hir
      {
        timers := timers,
        a16 := a16, a17 := a17, a18 := a18, a19 := a19,
        a20 := TrapInst.a20 t,
        a55 := ⟨imgs.1.covered⟩,
        a56 := ⟨imgs.1.topology⟩,
        a57 := ⟨imgs.1.attributes⟩,
        a58 := ⟨imgs.1.writeback⟩,
        a59 := ⟨imgs.1.permissions⟩,
        a121 := a121 rho caller pcount,
        a122 := HeapTrapClosed.a122 rho caller t pcount sspec hlay hlr hir,
        a123 := TrapInst.a123 rho caller t pcount,
        a210 := ⟨imgs.2⟩,
        a211 := Variant.a211_tw rho caller pcount (Wt t) HeapTrapTables.tables (fun wr => by cases wr <;> decide) sspec hir,
        a243 := ⟨world_tagStatusRows rho caller (Wt t) pcount 1⟩,
        a244 := TrapInst.a245 t hir,
        a245 := a245, a246 := a246,
        a256 := TrapInst.a257 rho caller t pcount,
        a257 := a257 rho caller pcount,
        a258 := TrapInst.a259 t hir,
        a259 := a259,
        a261 := ⟨ReleaseProfile.GB10.CodeStaticR.ofFull (TrapInst.a262 t hir).holds⟩,
        a262 := TrapInst.a263all t,
        a263 := TrapInst.a264 t,
        a264 := TrapInst.a265 t,
        a265 := Normal.a261,
        a266 := TrapInst.a267 rho caller t pcount,
        a267 := a267 rho caller pcount,
        a268 := a268 rho caller pcount,
        a269 := TrapInst.a270 rho caller t pcount,
        a270 := TrapInst.a271 t,
        a271 := TrapInst.a272 t,
        a272 := TrapInst.a273 t,
        a273 := TrapInst.a274 t hir,
        a274 := TrapInst.a275 t hir,
        a275 := TrapInst.a276 hlr,
        a276 := a276 rho caller pcount
      })

end ReleaseProfile.GB10.Heap.Trap.T2

#print axioms ReleaseProfile.GB10.Heap.Trap.T2.initial2_c2
