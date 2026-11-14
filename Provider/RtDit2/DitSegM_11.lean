import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.StepsV2_05
import RtDit2.StepBaseM
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace RtDit.StepsM
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.StepsM.ditSegM_11"
  (← IO.getStderr).flush

theorem ditSegM_11 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 330 ≤ k → k < 357 → RtDit.DitStepM real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 330 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 330 pins (rowsFootprint spec.imageRows).byte dp.static 0x2c4 0xa9012c0a
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp8.selected (10#5) (0#5) (11#5) (2#7)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Stp8 real spec config rows mapping dp.dataStatic dp.pinAligned (MemSteps.step_330).1 rfl (2#7) (0#5) (10#5) (11#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_330).2.1 (MemSteps.step_330).2.2.2.1 ⟨(MemSteps.step_330).2.2.2.2.1, (MemSteps.step_330).2.2.2.2.2.1⟩ (MemSteps.step_330).2.2.2.2.2.2 rfl rfl (MemSteps.step_330).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 331 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 331 pins (rowsFootprint spec.imageRows).byte dp.static 0x2c8 0xd65f03c0
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      _ (RtDit.dit_retM real 30#5 (by decide) (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch _
        (by rw [RtSaved2.link_target (by decide) inv.lr]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 332 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_332 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_332 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 333 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_333 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_333 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 334 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_334 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_334 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 335 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_335 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_335 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 336 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_336 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_336 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 337 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_337 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_337 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 338 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_338 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_338 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 339 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_339 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_339 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 340 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_340 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_340 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 341 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_341 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_341 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 342 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_342 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_342 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 343 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_343 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_343 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 344 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_344 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_344 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 345 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_345 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_345 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 346 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_346 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_346 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 347 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_347 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_347 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 348 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_348 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_348 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 349 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_349 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_349 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 350 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_350 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_350 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 351 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 351 pins (rowsFootprint spec.imageRows).byte dp.static 0xa8 0xa9000be1
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (0#7)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Stp real spec config rows mapping dp.dataStatic dp.pinAligned (MemSteps.step_351).1 rfl (0#7) (1#5) (2#5) (by decide) (by decide) (by decide +kernel) (MemSteps.step_351).2.1 (MemSteps.step_351).2.2.2.1 (MemSteps.step_351).2.2.2.2 rfl rfl (MemSteps.step_351).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 352 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 352 pins (rowsFootprint spec.imageRows).byte dp.static 0xac 0xa9010be1
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (2#7)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Stp real spec config rows mapping dp.dataStatic dp.pinAligned (MemSteps.step_352).1 rfl (2#7) (1#5) (2#5) (by decide) (by decide) (by decide +kernel) (MemSteps.step_352).2.1 (MemSteps.step_352).2.2.2.1 (MemSteps.step_352).2.2.2.2 rfl rfl (MemSteps.step_352).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 353 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 353 pins (rowsFootprint spec.imageRows).byte dp.static 0xb0 0xa9020be1
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (4#7)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Stp real spec config rows mapping dp.dataStatic dp.pinAligned (MemSteps.step_353).1 rfl (4#7) (1#5) (2#5) (by decide) (by decide) (by decide +kernel) (MemSteps.step_353).2.1 (MemSteps.step_353).2.2.2.1 (MemSteps.step_353).2.2.2.2 rfl rfl (MemSteps.step_353).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 354 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 354 pins (rowsFootprint spec.imageRows).byte dp.static 0xb4 0xa9437bf3
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldp.selected (19#5) (30#5) (6#7)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Ldp real spec config rows mapping dp.dataStatic dp.pinAligned (MemSteps.step_354).1 rfl (6#7) (19#5) (30#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_354).2.1 (MemSteps.step_354).2.2.2.1 (MemSteps.step_354).2.2.2.2 rfl rfl (MemSteps.step_354).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 355 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 355 pins (rowsFootprint spec.imageRows).byte dp.static 0xb8 0xa9030be1
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp.selected (1#5) (2#5) (6#7)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Stp real spec config rows mapping dp.dataStatic dp.pinAligned (MemSteps.step_355).1 rfl (6#7) (1#5) (2#5) (by decide) (by decide) (by decide +kernel) (MemSteps.step_355).2.1 (MemSteps.step_355).2.2.2.1 (MemSteps.step_355).2.2.2.2 rfl rfl (MemSteps.step_355).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 356 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_356 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_356 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  exact absurd hi (by omega)

#print axioms ditSegM_11
end RtDit.StepsM
