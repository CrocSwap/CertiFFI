import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.StepsV2_02
import RtDit.StepBase
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace RtDit.Steps
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false

run_cmd do
  IO.eprintln "CURRENT_DECL RtDit.Steps.ditSeg_07"
  (← IO.getStderr).flush

theorem ditSeg_07 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 210 ≤ k → k < 240 → RtDit.DitStep real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 210 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 210 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_210).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_210).2.1 (MemSteps.step_210).2.2.2 rfl rfl (MemSteps.step_210).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 211 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_211 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_211 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 212 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 212 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 213 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 213 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_213).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_213).2.1 (MemSteps.step_213).2.2.2 rfl rfl (MemSteps.step_213).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 214 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_214 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_214 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 215 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 215 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 216 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 216 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_216).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_216).2.1 (MemSteps.step_216).2.2.2 rfl rfl (MemSteps.step_216).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 217 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_217 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_217 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 218 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 218 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 219 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 219 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_219).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_219).2.1 (MemSteps.step_219).2.2.2 rfl rfl (MemSteps.step_219).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 220 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_220 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_220 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 221 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 221 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 222 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 222 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_222).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_222).2.1 (MemSteps.step_222).2.2.2 rfl rfl (MemSteps.step_222).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 223 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_223 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_223 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 224 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 224 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 225 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 225 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_225).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_225).2.1 (MemSteps.step_225).2.2.2 rfl rfl (MemSteps.step_225).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 226 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_226 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_226 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 227 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 227 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 228 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 228 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_228).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_228).2.1 (MemSteps.step_228).2.2.2 rfl rfl (MemSteps.step_228).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 229 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_229 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_229 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 230 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 230 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 231 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 231 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_231).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_231).2.1 (MemSteps.step_231).2.2.2 rfl rfl (MemSteps.step_231).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 232 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_232 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_232 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 233 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 233 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 234 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 234 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_234).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_234).2.1 (MemSteps.step_234).2.2.2 rfl rfl (MemSteps.step_234).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 235 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_235 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_235 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 236 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 236 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 237 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 237 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_237).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_237).2.1 (MemSteps.step_237).2.2.2 rfl rfl (MemSteps.step_237).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 238 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_238 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_238 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 239 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 239 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  exact absurd hi (by omega)

#print axioms ditSeg_07
end RtDit.Steps
