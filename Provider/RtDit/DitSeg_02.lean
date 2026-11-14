import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.StepsV2_00
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
  IO.eprintln "CURRENT_DECL RtDit.Steps.ditSeg_02"
  (← IO.getStderr).flush

theorem ditSeg_02 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 60 ≤ k → k < 90 → RtDit.DitStep real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 60 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_60 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_60 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 61 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 61 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 62 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 62 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_62).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_62).2.1 (MemSteps.step_62).2.2.2 rfl rfl (MemSteps.step_62).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 63 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 63 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_63).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_63).2.1 (MemSteps.step_63).2.2.2 rfl rfl (MemSteps.step_63).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 64 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_64 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_64 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 65 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 65 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 66 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 66 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_66).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_66).2.1 (MemSteps.step_66).2.2.2 rfl rfl (MemSteps.step_66).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 67 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 67 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_67).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_67).2.1 (MemSteps.step_67).2.2.2 rfl rfl (MemSteps.step_67).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 68 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_68 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_68 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 69 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 69 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 70 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 70 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_70).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_70).2.1 (MemSteps.step_70).2.2.2 rfl rfl (MemSteps.step_70).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 71 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 71 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_71).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_71).2.1 (MemSteps.step_71).2.2.2 rfl rfl (MemSteps.step_71).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 72 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_72 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_72 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 73 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 73 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 74 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 74 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_74).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_74).2.1 (MemSteps.step_74).2.2.2 rfl rfl (MemSteps.step_74).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 75 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 75 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_75).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_75).2.1 (MemSteps.step_75).2.2.2 rfl rfl (MemSteps.step_75).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 76 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_76 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_76 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 77 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 77 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 78 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 78 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_78).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_78).2.1 (MemSteps.step_78).2.2.2 rfl rfl (MemSteps.step_78).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 79 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 79 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_79).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_79).2.1 (MemSteps.step_79).2.2.2 rfl rfl (MemSteps.step_79).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 80 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_80 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_80 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 81 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 81 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 82 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 82 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_82).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_82).2.1 (MemSteps.step_82).2.2.2 rfl rfl (MemSteps.step_82).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 83 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 83 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_83).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_83).2.1 (MemSteps.step_83).2.2.2 rfl rfl (MemSteps.step_83).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 84 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_84 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_84 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 85 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 85 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 86 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 86 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_86).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_86).2.1 (MemSteps.step_86).2.2.2 rfl rfl (MemSteps.step_86).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 87 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 87 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_87).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_87).2.1 (MemSteps.step_87).2.2.2 rfl rfl (MemSteps.step_87).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 88 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_88 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_88 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 89 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 89 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  exact absurd hi (by omega)

#print axioms ditSeg_02
end RtDit.Steps
