import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.StepsV2_02
import HeapV2StepCerts.StepsV2_03
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
  IO.eprintln "CURRENT_DECL RtDit.StepsM.ctlSegM_08"
  (← IO.getStderr).flush

theorem ctlSegM_08 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 240 ≤ k → k < 270 → RtPremC.CtlStepM real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 240 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 240 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_240).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_240).2.1 (MemSteps.step_240).2.2.2 rfl rfl (MemSteps.step_240).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 241 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_241 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_241 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 242 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 242 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 243 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 243 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_243).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_243).2.1 (MemSteps.step_243).2.2.2 rfl rfl (MemSteps.step_243).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 244 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_244 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_244 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 245 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 245 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 246 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 246 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_246).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_246).2.1 (MemSteps.step_246).2.2.2 rfl rfl (MemSteps.step_246).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 247 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_247 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_247 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 248 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 248 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 249 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 249 pins (rowsFootprint spec.imageRows).byte dp.static 0x18c 0xd65f03c0
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_retM real 30#5 (by decide) (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [RtSaved2.link_target (by decide) inv.lr]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 250 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_250 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_250 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 251 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_251 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_251 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf 252 + sign_extend (78#26 ++ 0#2) 64 = HeapV2Compose.offsetOf (252 + 1) := by decide +kernel
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 252 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 252 pins (rowsFootprint spec.imageRows).byte dp.static 0x58 0x9400004e
        (by decide +kernel) (by decide +kernel) _ (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_blM real 78#26 (controls_of_v4 inv)
        (by rw [NativeEntryCallerRegisters.bl_target, inv.v3.v2.v1.pc, BitVec.add_assoc, land]; exact low_of _ (by decide +kernel) dp.low) (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 253 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 253 pins (rowsFootprint spec.imageRows).byte dp.static 0x190 0xa9400c22
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldp8.selected (2#5) (1#5) (3#5) (0#7)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldp8 real spec config rows mapping dp.dataStatic dp.pinAligned (MemSteps.step_253).1 rfl (0#7) (1#5) (2#5) (3#5) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_253).2.1 (MemSteps.step_253).2.2.2.1 ⟨(MemSteps.step_253).2.2.2.2.1, (MemSteps.step_253).2.2.2.2.2.1⟩ (MemSteps.step_253).2.2.2.2.2.2 rfl rfl (MemSteps.step_253).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 254 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_254 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_254 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 255 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_255 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_255 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 256 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 256 pins (rowsFootprint spec.imageRows).byte dp.static 0x19c 0xa9411424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldp8.selected (4#5) (1#5) (5#5) (2#7)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldp8 real spec config rows mapping dp.dataStatic dp.pinAligned (MemSteps.step_256).1 rfl (2#7) (1#5) (4#5) (5#5) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_256).2.1 (MemSteps.step_256).2.2.2.1 ⟨(MemSteps.step_256).2.2.2.2.1, (MemSteps.step_256).2.2.2.2.2.1⟩ (MemSteps.step_256).2.2.2.2.2.2 rfl rfl (MemSteps.step_256).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 257 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_257 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_257 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 258 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_258 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_258 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 259 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_259 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_259 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 260 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_260 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_260 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 261 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_261 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_261 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 262 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_262 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_262 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 263 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_263 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_263 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 264 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_264 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_264 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 265 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_265 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_265 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 266 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_266 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_266 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 267 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_267 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_267 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 268 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_268 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_268 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 269 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_269 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_269 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  exact absurd hi (by omega)

#print axioms ctlSegM_08
end RtPremC.StepsM
