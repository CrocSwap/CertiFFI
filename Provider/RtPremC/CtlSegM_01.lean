import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.StepsV2_00
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
  IO.eprintln "CURRENT_DECL RtDit.StepsM.ctlSegM_01"
  (← IO.getStderr).flush

theorem ctlSegM_01 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 30 ≤ k → k < 60 → RtPremC.CtlStepM real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 30 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 30 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_30).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_30).2.1 (MemSteps.step_30).2.2.2 rfl rfl (MemSteps.step_30).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 31 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 31 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_31).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_31).2.1 (MemSteps.step_31).2.2.2 rfl rfl (MemSteps.step_31).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 32 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_32 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_32 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 33 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 33 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 34 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 34 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_34).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_34).2.1 (MemSteps.step_34).2.2.2 rfl rfl (MemSteps.step_34).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 35 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 35 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_35).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_35).2.1 (MemSteps.step_35).2.2.2 rfl rfl (MemSteps.step_35).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 36 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_36 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_36 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 37 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 37 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 38 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 38 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_38).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_38).2.1 (MemSteps.step_38).2.2.2 rfl rfl (MemSteps.step_38).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 39 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 39 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_39).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_39).2.1 (MemSteps.step_39).2.2.2 rfl rfl (MemSteps.step_39).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 40 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_40 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_40 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 41 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 41 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 42 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 42 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_42).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_42).2.1 (MemSteps.step_42).2.2.2 rfl rfl (MemSteps.step_42).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 43 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 43 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_43).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_43).2.1 (MemSteps.step_43).2.2.2 rfl rfl (MemSteps.step_43).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 44 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_44 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_44 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 45 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 45 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 46 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 46 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_46).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_46).2.1 (MemSteps.step_46).2.2.2 rfl rfl (MemSteps.step_46).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 47 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 47 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_47).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_47).2.1 (MemSteps.step_47).2.2.2 rfl rfl (MemSteps.step_47).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 48 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_48 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_48 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 49 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 49 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 50 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 50 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_50).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_50).2.1 (MemSteps.step_50).2.2.2 rfl rfl (MemSteps.step_50).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 51 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 51 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_51).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_51).2.1 (MemSteps.step_51).2.2.2 rfl rfl (MemSteps.step_51).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 52 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_52 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_52 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 53 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 53 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 54 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 54 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_54).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_54).2.1 (MemSteps.step_54).2.2.2 rfl rfl (MemSteps.step_54).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 55 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 55 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_55).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_55).2.1 (MemSteps.step_55).2.2.2 rfl rfl (MemSteps.step_55).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 56 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_56 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_classM real ((HeapV2StepCerts.cert2_56 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl (fun _ => True))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 57 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 57 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_bcondM real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch (fun _ => True)
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 58 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 58 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_58).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_58).2.1 (MemSteps.step_58).2.2.2 rfl rfl (MemSteps.step_58).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtPremC.ctl_atM real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 59 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 59 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (fun _ => True) (RtPremC.ctl_memM real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_59).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_59).2.1 (MemSteps.step_59).2.2.2 rfl rfl (MemSteps.step_59).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  exact absurd hi (by omega)

#print axioms ctlSegM_01
end RtPremC.StepsM
