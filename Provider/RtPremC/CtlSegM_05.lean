import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.StepsV2_01
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
  IO.eprintln "CURRENT_DECL RtDit.StepsM.ctlSegM_05"
  (← IO.getStderr).flush

theorem ctlSegM_05 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 150 ≤ k → k < 180 → RtPremC.CtlStepM real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf 150 + sign_extend (75#26 ++ 0#2) 64 = HeapV2Compose.offsetOf (150 + 1) := by decide +kernel
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 150 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 150 pins (rowsFootprint spec.imageRows).byte dp.static 0x4c 0x9400004b
        (by decide +kernel) (by decide +kernel) _ (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_blM real 75#26 (controls_of_v4 inv)
        (by rw [NativeEntryCallerRegisters.bl_target, inv.v3.v2.v1.pc, BitVec.add_assoc, land]; exact low_of _ (by decide +kernel) dp.low) (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 151 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 151 pins (rowsFootprint spec.imageRows).byte dp.static 0x178 0xb40000a2
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_cbzM real 2#5 5#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 152 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_152 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_152 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 153 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 153 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_153).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_153).2.1 (MemSteps.step_153).2.2.2 rfl rfl (MemSteps.step_153).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 154 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_154 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_154 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 155 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 155 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 156 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 156 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_156).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_156).2.1 (MemSteps.step_156).2.2.2 rfl rfl (MemSteps.step_156).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 157 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_157 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_157 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 158 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 158 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 159 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 159 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_159).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_159).2.1 (MemSteps.step_159).2.2.2 rfl rfl (MemSteps.step_159).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 160 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_160 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_160 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 161 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 161 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 162 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 162 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_162).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_162).2.1 (MemSteps.step_162).2.2.2 rfl rfl (MemSteps.step_162).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 163 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_163 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_163 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 164 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 164 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 165 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 165 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_165).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_165).2.1 (MemSteps.step_165).2.2.2 rfl rfl (MemSteps.step_165).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 166 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_166 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_166 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 167 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 167 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 168 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 168 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_168).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_168).2.1 (MemSteps.step_168).2.2.2 rfl rfl (MemSteps.step_168).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 169 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_169 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_169 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 170 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 170 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 171 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 171 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_171).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_171).2.1 (MemSteps.step_171).2.2.2 rfl rfl (MemSteps.step_171).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 172 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_172 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_172 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 173 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 173 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 174 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 174 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_174).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_174).2.1 (MemSteps.step_174).2.2.2 rfl rfl (MemSteps.step_174).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 175 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_175 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_175 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 176 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 176 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 177 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 177 pins (rowsFootprint spec.imageRows).byte dp.static 0x180 0x38001461
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (1#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_177).1 rfl (1#9) (3#5) (1#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_177).2.1 (MemSteps.step_177).2.2.2 rfl rfl (MemSteps.step_177).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 178 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_178 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_178 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 179 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 179 pins (rowsFootprint spec.imageRows).byte dp.static 0x188 0x54ffffc1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524286#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  exact absurd hi (by omega)

#print axioms ctlSegM_05
end RtPremC.StepsM
