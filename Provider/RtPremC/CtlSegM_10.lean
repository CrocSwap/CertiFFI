import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.StepsV2_04
import HeapV2StepCerts.StepsV2_05
import RtPremC.CtlM
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace RtPremC.StepsM
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.StepsM.ctlSegM_10"
  (← IO.getStderr).flush

theorem ctlSegM_10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 300 ≤ k → k < 330 → RtPremC.CtlStepM real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 300 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_300 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_300 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 301 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_301 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_301 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 302 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_302 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_302 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 303 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_303 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_303 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 304 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_304 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_304 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 305 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_305 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_305 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 306 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_306 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_306 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 307 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_307 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_307 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 308 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_308 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_308 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 309 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_309 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_309 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 310 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_310 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_310 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 311 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_311 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_311 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 312 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_312 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_312 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 313 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_313 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_313 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 314 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_314 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_314 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 315 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_315 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_315 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 316 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_316 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_316 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 317 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_317 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_317 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 318 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_318 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_318 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 319 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_319 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_319 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 320 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_320 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_320 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 321 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_321 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_321 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 322 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_322 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_322 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 323 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_323 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_323 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 324 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_324 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_324 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 325 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_325 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_325 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 326 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_326 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_326 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 327 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_327 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_327 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 328 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_328 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_328 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 329 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 329 pins (rowsFootprint spec.imageRows).byte dp.static 0x2c0 0xa9002408
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp8.selected (8#5) (0#5) (9#5) (0#7)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Stp8 real spec config rows mapping dp.dataStatic dp.pinAligned (MemSteps.step_329).1 rfl (0#7) (0#5) (8#5) (9#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_329).2.1 (MemSteps.step_329).2.2.2.1 ⟨(MemSteps.step_329).2.2.2.2.1, (MemSteps.step_329).2.2.2.2.2.1⟩ (MemSteps.step_329).2.2.2.2.2.2 rfl rfl (MemSteps.step_329).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  exact absurd hi (by omega)

#print axioms ctlSegM_10
end RtPremC.StepsM
