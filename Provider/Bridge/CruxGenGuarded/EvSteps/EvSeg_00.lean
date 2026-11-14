import Bridge.CruxGenGuarded.ChainInvV4At
import Bridge.CruxGenGuarded.EvSteps.EvBase
import HeapV2StepCerts.MemStepsV4E_00
import HeapV2StepCerts.RegValStepsE00
import HeapV2StepCerts.StepsV2_00
import HeapV2StepCerts.TailWStepsEC0
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
  IO.eprintln "CURRENT_DECL EvSteps.evSeg_00"
  (← IO.getStderr).flush

theorem evSeg_00 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 0 ≤ k → k < 30 → EvStep real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (0 + 1) = if false then HeapV2Compose.offsetOf 0 + sign_extend (179#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 0 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_cbz_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 0 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 0#5 179#19 false (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_0 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 0 pins (rowsFootprint spec.imageRows).byte dp.static 0x0
        0xb4001660 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (1 + 1) = if false then HeapV2Compose.offsetOf 1 + sign_extend (178#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 1 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_cbz_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 1 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#5 178#19 false (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_1 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 1 pins (rowsFootprint spec.imageRows).byte dp.static 0x4
        0xb4001641 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_2 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 2 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_2 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (3 + 1) = if false then HeapV2Compose.offsetOf 3 + sign_extend (176#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 3 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 3 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 176#19 false (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_3 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 3 pins (rowsFootprint spec.imageRows).byte dp.static 0xc
        0x54001601 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_4 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 4 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_4 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (5 + 1) = if false then HeapV2Compose.offsetOf 5 + sign_extend (174#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 5 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 5 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 174#19 false (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_5 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 5 pins (rowsFootprint spec.imageRows).byte dp.static 0x14
        0x540015c1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_6 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 6 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_6 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (7 + 1) = if false then HeapV2Compose.offsetOf 7 + sign_extend (172#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 7 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 7 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 3#4 172#19 false (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_7 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 7 pins (rowsFootprint spec.imageRows).byte dp.static 0x1c
        0x54001583 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_8 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 8 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_8 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (9 + 1) = if false then HeapV2Compose.offsetOf 9 + sign_extend (170#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 9 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 9 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 170#19 false (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_9 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 9 pins (rowsFootprint spec.imageRows).byte dp.static 0x24
        0x54001541 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_10 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 10 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_10 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_11 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_12 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 12 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_12 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_13 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 13 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_13 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_14 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 14 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_14 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.RichZ.richBl_15_atE real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte
      dp.static (by omega) dp.page (low_of _ (by decide +kernel) dp.low) dp.nodup x inv.v3 (controls_of_v4 inv)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (16 + 1) = if false then HeapV2Compose.offsetOf 16 + sign_extend (6#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 16 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_cbz_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 16 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 2#5 6#19 false (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_16 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 16 pins (rowsFootprint spec.imageRows).byte dp.static 0x128
        0xb40000c2 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_17 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 17 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_17 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_18 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_19 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_20 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 20 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_20 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (21 + 1) = if true then HeapV2Compose.offsetOf 21 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 21 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 21 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_21 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 21 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_22 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_23 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_24 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 24 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_24 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (25 + 1) = if true then HeapV2Compose.offsetOf 25 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 25 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 25 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_25 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 25 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_26 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_27 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_28 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 28 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_28 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (29 + 1) = if true then HeapV2Compose.offsetOf 29 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 29 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 29 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_29 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 29 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  exact absurd hi (by omega)

#print axioms evSeg_00
end ArmBridge.CruxGenGuarded.EvSteps
