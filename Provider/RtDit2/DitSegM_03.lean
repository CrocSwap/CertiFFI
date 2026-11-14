import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.StepsV2_00
import HeapV2StepCerts.StepsV2_01
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
  IO.eprintln "CURRENT_DECL RtDit.StepsM.ditSegM_03"
  (← IO.getStderr).flush

theorem ditSegM_03 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 90 ≤ k → k < 120 → RtDit.DitStepM real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 90 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 90 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_90).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_90).2.1 (MemSteps.step_90).2.2.2 rfl rfl (MemSteps.step_90).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 91 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 91 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_91).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_91).2.1 (MemSteps.step_91).2.2.2 rfl rfl (MemSteps.step_91).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 92 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_92 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_92 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 93 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 93 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      _ (RtDit.dit_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch _
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 94 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 94 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_94).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_94).2.1 (MemSteps.step_94).2.2.2 rfl rfl (MemSteps.step_94).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 95 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 95 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_95).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_95).2.1 (MemSteps.step_95).2.2.2 rfl rfl (MemSteps.step_95).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 96 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_96 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_96 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 97 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 97 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      _ (RtDit.dit_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch _
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 98 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 98 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_98).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_98).2.1 (MemSteps.step_98).2.2.2 rfl rfl (MemSteps.step_98).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 99 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 99 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_99).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_99).2.1 (MemSteps.step_99).2.2.2 rfl rfl (MemSteps.step_99).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 100 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_100 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_100 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 101 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 101 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      _ (RtDit.dit_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch _
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 102 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 102 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_102).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_102).2.1 (MemSteps.step_102).2.2.2 rfl rfl (MemSteps.step_102).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 103 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 103 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_103).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_103).2.1 (MemSteps.step_103).2.2.2 rfl rfl (MemSteps.step_103).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 104 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_104 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_104 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 105 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 105 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      _ (RtDit.dit_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch _
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 106 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 106 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_106).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_106).2.1 (MemSteps.step_106).2.2.2 rfl rfl (MemSteps.step_106).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 107 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 107 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_107).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_107).2.1 (MemSteps.step_107).2.2.2 rfl rfl (MemSteps.step_107).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 108 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_108 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_108 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 109 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 109 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      _ (RtDit.dit_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch _
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 110 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 110 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_110).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_110).2.1 (MemSteps.step_110).2.2.2 rfl rfl (MemSteps.step_110).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 111 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 111 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_111).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_111).2.1 (MemSteps.step_111).2.2.2 rfl rfl (MemSteps.step_111).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 112 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_112 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_112 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 113 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 113 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      _ (RtDit.dit_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch _
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 114 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 114 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_114).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_114).2.1 (MemSteps.step_114).2.2.2 rfl rfl (MemSteps.step_114).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 115 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 115 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_115).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_115).2.1 (MemSteps.step_115).2.2.2 rfl rfl (MemSteps.step_115).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 116 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_116 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      _ (RtDit.dit_classM real ((HeapV2StepCerts.cert2_116 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl _)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 117 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 117 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      _ (RtDit.dit_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch _
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 118 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 118 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_118).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_118).2.1 (MemSteps.step_118).2.2.2 rfl rfl (MemSteps.step_118).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 119 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 119 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      _ (RtDit.dit_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_119).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_119).2.1 (MemSteps.step_119).2.2.2 rfl rfl (MemSteps.step_119).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  exact absurd hi (by omega)

#print axioms ditSegM_03
end RtDit.StepsM
