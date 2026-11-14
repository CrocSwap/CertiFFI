import Bridge.CruxGenGuarded.ChainInvV4At
import Bridge.CruxGenGuarded.EvSteps.EvBase
import HeapV2StepCerts.MemStepsV4E_02
import HeapV2StepCerts.MemStepsV4E_03
import HeapV2StepCerts.RegValStepsE01
import HeapV2StepCerts.StepsV2_01
import HeapV2StepCerts.TailWStepsEC3
import HeapV2StepCerts.TailWStepsEC4
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
  IO.eprintln "CURRENT_DECL EvSteps.evSeg_04"
  (← IO.getStderr).flush

theorem evSeg_04 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 120 ≤ k → k < 150 → EvStep real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_120 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 120 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_120 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (121 + 1) = if true then HeapV2Compose.offsetOf 121 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 121 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 121 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_121 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 121 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_122 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_123 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_124 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 124 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_124 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (125 + 1) = if true then HeapV2Compose.offsetOf 125 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 125 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 125 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_125 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 125 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_126 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_127 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_128 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 128 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_128 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (129 + 1) = if true then HeapV2Compose.offsetOf 129 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 129 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 129 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_129 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 129 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_130 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_131 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_132 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 132 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_132 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (133 + 1) = if true then HeapV2Compose.offsetOf 133 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 133 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 133 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_133 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 133 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_134 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_135 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_136 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 136 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_136 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (137 + 1) = if true then HeapV2Compose.offsetOf 137 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 137 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 137 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_137 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 137 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_138 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_139 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_140 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 140 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_140 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (141 + 1) = if true then HeapV2Compose.offsetOf 141 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 141 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 141 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 true (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_141 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 141 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_142 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_143 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_144 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 144 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_144 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    have land : HeapV2Compose.offsetOf (145 + 1) = if false then HeapV2Compose.offsetOf 145 + sign_extend (524285#19 ++ 0#2) 64
        else HeapV2Compose.offsetOf 145 + 4#64 := by decide +kernel
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_bcond_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 145 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 1#4 524285#19 false (by decide) x inv.v3
      (HeapV2StepCerts.ValBind.dec_145 dp.np inv.v3.regBind inv.valBind)
      (fun y iy => by rw [iy.v2.v1.pc, BitVec.add_assoc]; exact low_of _ (by decide +kernel) dp.low)
      (fun y iy => by rw [iy.v2.v1.pc, land]; simp [BitVec.add_assoc])
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 145 pins (rowsFootprint spec.imageRows).byte dp.static 0x13c
        0x54ffffa1 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_ret_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 146 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 30#5 (by decide) (by decide) x inv.v3
      (by rw [RtSaved2.link_target (by decide) inv.lr]; exact low_of _ (by decide +kernel) dp.low)
      (RtSaved2.link_target (by decide) inv.lr)
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 146 pins (rowsFootprint spec.imageRows).byte dp.static 0x140
        0xd65f03c0 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_147 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 147 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_147 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_148 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 148 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_148 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_149 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 149 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_149 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  exact absurd hi (by omega)

#print axioms evSeg_04
end ArmBridge.CruxGenGuarded.EvSteps
