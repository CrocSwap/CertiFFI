-- Current-profile heap body with exact ordered records.
import DefaultHeapBody
import DefaultHeapDitStep
import DefaultHeapClassRows04
import DefaultHeapClassRows05
import DefaultHeapClassRows06
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


#check "CURRENT_DECL heap dit_segment_09"
theorem dit_segment_09 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 270 ≤ k → k < 300 → ∀ x, RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  intro k lo hi x inv
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 270 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_270 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 270 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1d4 0x9b057c67
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 270 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1d4 0x9b057c67
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 271 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_271 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 271 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1d8 0x9bc57c66
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 271 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1d8 0x9bc57c66
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 272 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_272 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 272 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1dc 0x9a1f00c6
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 272 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1dc 0x9a1f00c6
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 273 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_273 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 273 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1e0 0xab07018c
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 273 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1e0 0xab07018c
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 274 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_274 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 274 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1e4 0xba0601ad
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 274 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1e4 0xba0601ad
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 275 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_275 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 275 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1e8 0x9a1f01ce
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 275 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1e8 0x9a1f01ce
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 276 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_276 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 276 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1ec 0xab090129
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 276 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1ec 0xab090129
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 277 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_277 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 277 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1f0 0xba0a014a
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 277 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1f0 0xba0a014a
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 278 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_278 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 278 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1f4 0xba0b016b
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 278 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1f4 0xba0b016b
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 279 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_279 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 279 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1f8 0xba0c018c
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 279 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1f8 0xba0c018c
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 280 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_280 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 280 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1fc 0xba0d01ad
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 280 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x1fc 0xba0d01ad
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 281 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_281 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 281 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x200 0xba0e01ce
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 281 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x200 0xba0e01ce
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 282 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_282 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 282 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x204 0x9a9f37e6
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 282 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x204 0x9a9f37e6
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 283 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_283 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 283 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x208 0x9bc27c47
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 283 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x208 0x9bc27c47
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 284 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_284 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 284 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x20c 0x9b027c48
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 284 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x20c 0x9b027c48
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 285 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_285 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 285 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x210 0xab070129
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 285 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x210 0xab070129
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 286 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_286 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 286 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x214 0x9b037c67
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 286 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x214 0x9b037c67
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 287 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_287 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 287 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x218 0xba07014a
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 287 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x218 0xba07014a
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 288 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_288 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 288 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x21c 0x9bc37c67
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 288 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x21c 0x9bc37c67
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 289 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_289 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 289 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x220 0xba07016b
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 289 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x220 0xba07016b
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 290 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_290 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 290 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x224 0x9b047c87
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 290 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x224 0x9b047c87
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 291 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_291 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 291 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x228 0xba07018c
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 291 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x228 0xba07018c
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 292 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_292 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 292 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x22c 0x9bc47c87
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 292 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x22c 0x9bc47c87
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 293 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_293 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 293 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x230 0xba0701ad
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 293 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x230 0xba0701ad
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 294 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_294 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 294 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x234 0x9b057ca7
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 294 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x234 0x9b057ca7
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 295 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_295 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 295 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x238 0xba0701ce
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 295 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x238 0xba0701ce
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 296 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_296 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 296 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x23c 0x9bc57ca7
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 296 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x23c 0x9bc57ca7
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 297 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_297 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 297 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x240 0x9a0700c6
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 297 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x240 0x9a0700c6
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 298 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_298 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 298 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x244 0xd2807a23
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 298 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x244 0xd2807a23
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  ·
    exact DefaultHeapDitStep.scalar real spec config rows mapping _ codeScope (HeapV2.image base) base
          dp.static.separated base HeapV2Compose.offsetOf budget pins 299 catalogue entry capacity drawsBefore (by omega) (by decide) dp.page (by decide)
          _ _ _ x inv.1.body (HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_299 real x))
          (DefaultHeapCode.memNextPlaced spec config rows mapping base budget 299 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x248 0xb2600063
            (by decide) (by decide) (by decide) x inv.1.body.core) dp.nodup
          (DefaultHeapCode.memFetch spec config rows mapping base budget 299 pins (rowsFootprint spec.imageRows).byte catalogue dp.static 0x248 0xb2600063
            (by decide) (by decide) _ (by decide) x inv.1.body.core) (by decide)
  omega
#print axioms dit_segment_09
end ReleaseProfile.DefaultHeapRun
