-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import DefaultHeapDitStep
import DefaultHeapBranchRowsCall
import DefaultHeapClassRows07
import DefaultHeapClassRows08
import DefaultHeapMemDitRows05
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ReleaseProfile.DefaultHeapRun
open ReleaseProfile
open ReleaseProfile.DefaultHeapResidue (controls)
attribute [local instance 10] Classical.propDecidable


#check "CURRENT_DECL heap dit_segment_11"
theorem dit_segment_11 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 330 ≤ k → k < 357 → ∀ x, RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  intro k lo hi x inv
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_330 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_330] using dp.rowsRoom 330 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_330] using dp.rowsNext 330 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.branch real spec config rows mapping _ codeScope (HeapV2.image base) base
      dp.static.separated base HeapV2Compose.offsetOf budget pins 331 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
      (EntryBodyRet.W 30#5) 94 (by decide) (by decide) x inv.1.body (DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide) (by rw [RtSaved2.link_target (by decide) inv.1.lr]; exact (low_of _ (by decide) dp.low)) _ (RtSaved2.link_target (by decide) inv.1.lr)) dp.nodup
      (DefaultHeapCode.memFetch spec config rows mapping base budget 331 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x2c8 0xd65f03c0
        (by decide) (by decide) _ (by decide) x inv.1.body.core)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 332 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_332 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 332 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x5c 0xd2800000
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 332 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x5c 0xd2800000
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 333 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_333 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 333 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x60 0xd2800001
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 333 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x60 0xd2800001
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 334 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_334 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 334 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x64 0xd2800002
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 334 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x64 0xd2800002
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 335 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_335 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 335 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x68 0xd2800003
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 335 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x68 0xd2800003
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 336 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_336 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 336 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x6c 0xd2800004
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 336 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x6c 0xd2800004
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 337 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_337 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 337 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x70 0xd2800005
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 337 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x70 0xd2800005
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 338 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_338 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 338 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x74 0xd2800006
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 338 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x74 0xd2800006
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 339 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_339 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 339 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x78 0xd2800007
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 339 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x78 0xd2800007
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 340 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_340 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 340 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x7c 0xd2800008
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 340 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x7c 0xd2800008
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 341 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_341 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 341 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x80 0xd2800009
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 341 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x80 0xd2800009
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 342 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_342 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 342 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x84 0xd280000a
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 342 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x84 0xd280000a
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 343 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_343 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 343 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x88 0xd280000b
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 343 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x88 0xd280000b
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 344 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_344 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 344 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x8c 0xd280000c
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 344 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x8c 0xd280000c
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 345 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_345 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 345 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x90 0xd280000d
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 345 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x90 0xd280000d
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 346 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_346 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 346 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x94 0xd280000e
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 346 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x94 0xd280000e
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 347 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_347 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 347 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x98 0xd280000f
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 347 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x98 0xd280000f
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 348 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_348 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 348 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x9c 0xd2800010
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 348 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x9c 0xd2800010
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 349 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.tailW_349 real x)
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 349 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0xa0 0xd2800011
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 349 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0xa0 0xd2800011
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 350 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (DefaultHeapClassStep.fromWN (HeapV2StepCerts.TailWE.tailWN_350 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 350 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0xa4 0xf240083f
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 350 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0xa4 0xf240083f
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_351 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_351] using dp.rowsRoom 351 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_351] using dp.rowsNext 351 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_352 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_352] using dp.rowsRoom 352 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_352] using dp.rowsNext 352 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_353 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_353] using dp.rowsRoom 353 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_353] using dp.rowsNext 353 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_354 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_354] using dp.rowsRoom 354 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_354] using dp.rowsNext 354 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    obtain ⟨fin, run, _, _, dit⟩ :=
      DefaultHeapMemDitRows.step_355 real spec config rows mapping base budget pins
        (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic dp.pinAligned dp.codeD
        dp.nodup (by omega) dp.page (by simpa only [DefaultHeapBudget.cost_at_355] using dp.rowsRoom 355 (by decide)) (by simpa only [DefaultHeapBudget.cost_at_355] using dp.rowsNext 355 (by decide)) x inv.1.body
    exact ⟨fin, run, dit⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 356 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (DefaultHeapClassStep.fromWF (HeapV2StepCerts.TailWE.tailWF_356 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 356 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0xbc 0x910103ff
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 356 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0xbc 0x910103ff
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  omega
#print axioms dit_segment_11
end ReleaseProfile.DefaultHeapRun
