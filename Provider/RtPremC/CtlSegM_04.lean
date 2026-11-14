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
  IO.eprintln "CURRENT_DECL RtDit.StepsM.ctlSegM_04"
  (← IO.getStderr).flush

theorem ctlSegM_04 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 120 ≤ k → k < 150 → RtPremC.CtlStepM real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 120 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_120 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_120 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 121 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 121 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 122 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 122 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_122).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_122).2.1 (MemSteps.step_122).2.2.2 rfl rfl (MemSteps.step_122).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 123 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 123 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_123).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_123).2.1 (MemSteps.step_123).2.2.2 rfl rfl (MemSteps.step_123).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 124 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_124 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_124 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 125 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 125 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 126 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 126 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_126).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_126).2.1 (MemSteps.step_126).2.2.2 rfl rfl (MemSteps.step_126).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 127 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 127 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_127).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_127).2.1 (MemSteps.step_127).2.2.2 rfl rfl (MemSteps.step_127).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 128 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_128 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_128 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 129 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 129 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 130 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 130 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_130).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_130).2.1 (MemSteps.step_130).2.2.2 rfl rfl (MemSteps.step_130).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 131 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 131 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_131).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_131).2.1 (MemSteps.step_131).2.2.2 rfl rfl (MemSteps.step_131).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 132 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_132 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_132 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 133 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 133 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 134 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 134 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_134).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_134).2.1 (MemSteps.step_134).2.2.2 rfl rfl (MemSteps.step_134).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 135 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 135 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_135).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_135).2.1 (MemSteps.step_135).2.2.2 rfl rfl (MemSteps.step_135).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 136 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_136 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_136 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 137 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 137 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 138 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 138 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_138).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_138).2.1 (MemSteps.step_138).2.2.2 rfl rfl (MemSteps.step_138).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 139 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 139 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_139).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_139).2.1 (MemSteps.step_139).2.2.2 rfl rfl (MemSteps.step_139).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 140 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_140 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_140 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 141 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 141 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 142 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 142 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_142).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_142).2.1 (MemSteps.step_142).2.2.2 rfl rfl (MemSteps.step_142).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 143 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 143 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_143).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_143).2.1 (MemSteps.step_143).2.2.2 rfl rfl (MemSteps.step_143).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 144 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_144 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_144 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 145 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 145 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 146 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 146 pins (rowsFootprint spec.imageRows).byte dp.static 0x140 0xd65f03c0
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_retM real 30#5 (by decide) (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [RtSaved2.link_target (by decide) inv.lr]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 147 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_147 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_147 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 148 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_148 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_148 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 149 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_149 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_149 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  exact absurd hi (by omega)

#print axioms ctlSegM_04
end RtPremC.StepsM
