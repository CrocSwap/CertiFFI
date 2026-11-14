import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.StepsV2_01
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
  IO.eprintln "CURRENT_DECL RtDit.Steps.ditSeg_06"
  (← IO.getStderr).flush

theorem ditSeg_06 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 180 ≤ k → k < 210 → RtDit.DitStep real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 180 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 180 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_180).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_180).2.1 (MemSteps.step_180).2.2.2 rfl rfl (MemSteps.step_180).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 181 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_181 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_181 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 182 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 182 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 183 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 183 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_183).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_183).2.1 (MemSteps.step_183).2.2.2 rfl rfl (MemSteps.step_183).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 184 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_184 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_184 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 185 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 185 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 186 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 186 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_186).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_186).2.1 (MemSteps.step_186).2.2.2 rfl rfl (MemSteps.step_186).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 187 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_187 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_187 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 188 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 188 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 189 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 189 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_189).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_189).2.1 (MemSteps.step_189).2.2.2 rfl rfl (MemSteps.step_189).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 190 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_190 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_190 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 191 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 191 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 192 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 192 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_192).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_192).2.1 (MemSteps.step_192).2.2.2 rfl rfl (MemSteps.step_192).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 193 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_193 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_193 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 194 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 194 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 195 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 195 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_195).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_195).2.1 (MemSteps.step_195).2.2.2 rfl rfl (MemSteps.step_195).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 196 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_196 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_196 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 197 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 197 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 198 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 198 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_198).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_198).2.1 (MemSteps.step_198).2.2.2 rfl rfl (MemSteps.step_198).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 199 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_199 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_199 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 200 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 200 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 201 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 201 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_201).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_201).2.1 (MemSteps.step_201).2.2.2 rfl rfl (MemSteps.step_201).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 202 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_202 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_202 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 203 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 203 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 204 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 204 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_204).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_204).2.1 (MemSteps.step_204).2.2.2 rfl rfl (MemSteps.step_204).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 205 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_205 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_205 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 206 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 206 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 207 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 207 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_207).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_207).2.1 (MemSteps.step_207).2.2.2 rfl rfl (MemSteps.step_207).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 208 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_208 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_208 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 209 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 209 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  exact absurd hi (by omega)

#print axioms ditSeg_06
end RtDit.Steps
