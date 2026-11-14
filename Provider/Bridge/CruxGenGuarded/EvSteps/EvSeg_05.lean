import Bridge.CruxGenGuarded.ChainInvV4At
import Bridge.CruxGenGuarded.EvSteps.EvBase
import HeapV2StepCerts.MemStepsV4E_03
import HeapV2StepCerts.RegValStepsE01
import HeapV2StepCerts.StepsV2_01
import HeapV2StepCerts.TailWStepsEC4
import HeapV2StepCerts.TailWStepsEC5
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
  IO.eprintln "CURRENT_DECL EvSteps.evSeg_05"
  (← IO.getStderr).flush

theorem evSeg_05 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 150 ≤ k → k < 180 → EvStep real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.RichZ.richBl_150_atE real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte
      dp.static (by omega) dp.page (low_of _ (by decide +kernel) dp.low) dp.nodup x inv.v3 (controls_of_v4 inv)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (151 + 1) = if false then HeapV2Compose.offsetOf 151 + sign_extend (5#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 151 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_cbz_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 151 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 2#5 5#19 false (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_151 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 151 pins (rowsFootprint spec.imageRows).byte dp.static 0x178
        0xb40000a2 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_152 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 152 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_152 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_153 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_154 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 154 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_154 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (155 + 1) = if true then HeapV2Compose.offsetOf 155 + sign_extend (524286#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 155 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 155 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524286#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_155 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 155 pins (rowsFootprint spec.imageRows).byte dp.static 0x188
        0x54ffffc1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_156 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_157 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 157 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_157 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (158 + 1) = if true then HeapV2Compose.offsetOf 158 + sign_extend (524286#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 158 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 158 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524286#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_158 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 158 pins (rowsFootprint spec.imageRows).byte dp.static 0x188
        0x54ffffc1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_159 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_160 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 160 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_160 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (161 + 1) = if true then HeapV2Compose.offsetOf 161 + sign_extend (524286#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 161 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 161 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524286#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_161 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 161 pins (rowsFootprint spec.imageRows).byte dp.static 0x188
        0x54ffffc1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_162 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_163 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 163 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_163 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (164 + 1) = if true then HeapV2Compose.offsetOf 164 + sign_extend (524286#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 164 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 164 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524286#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_164 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 164 pins (rowsFootprint spec.imageRows).byte dp.static 0x188
        0x54ffffc1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_165 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_166 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 166 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_166 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (167 + 1) = if true then HeapV2Compose.offsetOf 167 + sign_extend (524286#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 167 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 167 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524286#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_167 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 167 pins (rowsFootprint spec.imageRows).byte dp.static 0x188
        0x54ffffc1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_168 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_169 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 169 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_169 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (170 + 1) = if true then HeapV2Compose.offsetOf 170 + sign_extend (524286#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 170 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 170 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524286#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_170 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 170 pins (rowsFootprint spec.imageRows).byte dp.static 0x188
        0x54ffffc1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_171 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_172 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 172 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_172 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (173 + 1) = if true then HeapV2Compose.offsetOf 173 + sign_extend (524286#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 173 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 173 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524286#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_173 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 173 pins (rowsFootprint spec.imageRows).byte dp.static 0x188
        0x54ffffc1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_174 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_175 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 175 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_175 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (176 + 1) = if true then HeapV2Compose.offsetOf 176 + sign_extend (524286#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 176 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 176 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524286#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_176 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 176 pins (rowsFootprint spec.imageRows).byte dp.static 0x188
        0x54ffffc1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_177 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_178 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 178 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_178 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (179 + 1) = if true then HeapV2Compose.offsetOf 179 + sign_extend (524286#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 179 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 179 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524286#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_179 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 179 pins (rowsFootprint spec.imageRows).byte dp.static 0x188
        0x54ffffc1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  exact absurd hi (by omega)

#print axioms evSeg_05
end ArmBridge.CruxGenGuarded.EvSteps
