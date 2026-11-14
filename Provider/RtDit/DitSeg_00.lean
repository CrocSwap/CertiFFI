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
  IO.eprintln "CURRENT_DECL RtDit.Steps.ditSeg_00"
  (← IO.getStderr).flush

theorem ditSeg_00 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 0 ≤ k → k < 30 → RtDit.DitStep real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 0 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 0 pins (rowsFootprint spec.imageRows).byte dp.static 0x0 0xb4001660
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_cbz real 0#5 179#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 1 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 1 pins (rowsFootprint spec.imageRows).byte dp.static 0x4 0xb4001641
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_cbz real 1#5 178#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 2 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_2 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_2 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 3 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 3 pins (rowsFootprint spec.imageRows).byte dp.static 0xc 0x54001601
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 176#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 4 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_4 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_4 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 5 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 5 pins (rowsFootprint spec.imageRows).byte dp.static 0x14 0x540015c1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 174#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 6 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_6 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_6 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 7 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 7 pins (rowsFootprint spec.imageRows).byte dp.static 0x1c 0x54001583
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 3#4 172#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 8 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_8 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_8 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 9 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 9 pins (rowsFootprint spec.imageRows).byte dp.static 0x24 0x54001541
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 170#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 10 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_10 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_10 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 11 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 11 pins (rowsFootprint spec.imageRows).byte dp.static 0x2c 0xa9037bf3
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Stp.selected (19#5) (30#5) (6#7)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Stp real spec config rows mapping dp.dataStatic dp.pinAligned (MemSteps.step_11).1 rfl (6#7) (19#5) (30#5) (by decide) (by decide) (by decide +kernel) (MemSteps.step_11).2.1 (MemSteps.step_11).2.2.2.1 (MemSteps.step_11).2.2.2.2 rfl rfl (MemSteps.step_11).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 12 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_12 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_12 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 13 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_13 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_13 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 14 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_14 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_14 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf 15 + sign_extend (59#26 ++ 0#2) 64 = HeapV2Compose.offsetOf (15 + 1) := by decide +kernel
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 15 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 15 pins (rowsFootprint spec.imageRows).byte dp.static 0x3c 0x9400003b
        (by decide +kernel) (by decide +kernel) _ (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_bl real 59#26 (controls_of_v4 inv)
        (by rw [NativeEntryCallerRegisters.bl_target, inv.v3.v2.v1.pc, BitVec.add_assoc, land]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 16 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 16 pins (rowsFootprint spec.imageRows).byte dp.static 0x128 0xb40000c2
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_cbz real 2#5 6#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 17 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_17 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_17 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 18 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 18 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_18).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_18).2.1 (MemSteps.step_18).2.2.2 rfl rfl (MemSteps.step_18).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 19 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 19 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_19).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_19).2.1 (MemSteps.step_19).2.2.2 rfl rfl (MemSteps.step_19).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 20 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_20 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_20 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 21 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 21 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 22 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 22 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_22).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_22).2.1 (MemSteps.step_22).2.2.2 rfl rfl (MemSteps.step_22).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 23 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 23 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_23).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_23).2.1 (MemSteps.step_23).2.2.2 rfl rfl (MemSteps.step_23).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 24 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_24 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_24 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 25 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 25 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 26 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 26 pins (rowsFootprint spec.imageRows).byte dp.static 0x130 0x38401424
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Ldrb.selected (4#5) (1#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Ldrb real spec config rows mapping dp.dataStatic (MemSteps.step_26).1 rfl (1#9) (1#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_26).2.1 (MemSteps.step_26).2.2.2 rfl rfl (MemSteps.step_26).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 27 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 27 pins (rowsFootprint spec.imageRows).byte dp.static 0x134 0x38001464
      (by decide +kernel) (by decide +kernel) (NativeEntryBodyDispatch.Strb.selected (4#5) (3#5) (1#9)) (by decide +kernel) x inv.v3.v2)
      (RtDit.dit_mem real (MemNext.memV_Strb real spec config rows mapping dp.dataStatic (MemSteps.step_27).1 rfl (1#9) (3#5) (4#5) (by decide) (by decide) (by decide) (by decide +kernel) (MemSteps.step_27).2.1 (MemSteps.step_27).2.2.2 rfl rfl (MemSteps.step_27).2.2.1 x) rfl inv.v3.raw inv.v3.noUpd inv.v3.regBind inv.v3.present inv.v3.post2
        inv.v3.mode inv.v3.debug inv.v3.feat inv.v3.dcache)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 28 (by omega) dp.page (by decide +kernel) _ x inv.v3
      ((HeapV2StepCerts.cert2_28 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).fetch x inv.v3.v2)
      (RtDit.dit_class real ((HeapV2StepCerts.cert2_28 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static).tail x inv.v3.v2) rfl)
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    exact RtDit.dit_at real spec config rows mapping _ _ _ _ base HeapV2Compose.offsetOf budget pins 29 (by omega) dp.page (by decide +kernel) _ x inv.v3
      (MemNext.memFetch spec config rows mapping base budget 29 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c 0x54ffffa1
        (by decide +kernel) (by decide +kernel) _ (by decide) x inv.v3.v2)
      (RtDit.dit_bcond real 1#4 524285#19 (by decide) inv.v3.v2.v1.pins inv.v3.v2.branch
        (by rw [inv.v3.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low))
  exact absurd hi (by omega)

#print axioms ditSeg_00
end RtDit.Steps
