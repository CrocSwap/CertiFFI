import Bridge.CruxGenGuarded.ChainInvV4At
import Bridge.CruxGenGuarded.EvSteps.EvBase
import HeapV2StepCerts.MemStepsV4E_00
import HeapV2StepCerts.MemStepsV4E_01
import HeapV2StepCerts.StepsV2_00
import HeapV2StepCerts.TailWStepsEC0
import HeapV2StepCerts.TailWStepsEC1
import HeapV2StepCerts.ValBindDec
import RtB6.RichZ
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace ArmBridge.CruxGenGuarded.EvSteps
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

run_cmd do
  IO.eprintln "CURRENT_DECL EvSteps.evSeg_01"
  (← IO.getStderr).flush

theorem evSeg_01 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 30 ≤ k → k < 60 → EvStep real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_30 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_31 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_32 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 32 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_32 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (33 + 1) = if true then HeapV2Compose.offsetOf 33 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 33 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 33 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_33 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 33 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_34 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_35 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_36 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 36 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_36 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (37 + 1) = if true then HeapV2Compose.offsetOf 37 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 37 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 37 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_37 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 37 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_38 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_39 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_40 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 40 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_40 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (41 + 1) = if true then HeapV2Compose.offsetOf 41 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 41 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 41 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_41 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 41 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_42 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_43 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_44 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 44 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_44 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (45 + 1) = if true then HeapV2Compose.offsetOf 45 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 45 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 45 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_45 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 45 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_46 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_47 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_48 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 48 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_48 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (49 + 1) = if true then HeapV2Compose.offsetOf 49 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 49 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 49 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_49 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 49 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_50 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_51 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_52 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 52 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_52 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (53 + 1) = if true then HeapV2Compose.offsetOf 53 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 53 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 53 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_53 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 53 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_54 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_55 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_56 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 56 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_56 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (57 + 1) = if true then HeapV2Compose.offsetOf 57 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 57 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 57 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_57 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 57 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_58 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_59 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  exact absurd hi (by omega)

#print axioms evSeg_01
end ArmBridge.CruxGenGuarded.EvSteps
