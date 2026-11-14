import Bridge.CruxGenGuarded.ChainInvV4At
import Bridge.CruxGenGuarded.EvSteps.EvBase
import HeapV2StepCerts.MemStepsV4E_05
import HeapV2StepCerts.RegValStepsE05
import HeapV2StepCerts.StepsV2_05
import HeapV2StepCerts.TailWStepsEC8
import HeapV2StepCerts.TailWStepsEC9
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
  IO.eprintln "CURRENT_DECL EvSteps.evSeg_11"
  (← IO.getStderr).flush

theorem evSeg_11 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 330 ≤ k → k < 357 → EvStep real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_330 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := RtB6.RichZ.rich_branch_ret_atE real spec config rows mapping _ HeapV2StepCerts.codeScope
      (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget pins 331 (by omega) (by decide) dp.page
      (by decide +kernel) (by decide +kernel) (by decide +kernel) dp.nodup 30#5 (by decide) (by decide) x inv.v3
      (by rw [RtSaved2.link_target (by decide) inv.lr]; exact low_of _ (by decide +kernel) dp.low)
      (RtSaved2.link_target (by decide) inv.lr)
      (fun y iy => HeapV2StepCerts.MemNext.memFetch spec config rows mapping base budget 331 pins (rowsFootprint spec.imageRows).byte dp.static 0x2c8
        0xd65f03c0 (by decide +kernel) (by decide +kernel) _ (by decide) y iy.v2)
    exact ⟨fin, run, r.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_332 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 332 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_332 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_333 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 333 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_333 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_334 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 334 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_334 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_335 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 335 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_335 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_336 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 336 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_336 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_337 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 337 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_337 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_338 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 338 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_338 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_339 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 339 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_339 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_340 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 340 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_340 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_341 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 341 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_341 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_342 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 342 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_342 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_343 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 343 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_343 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_344 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 344 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_344 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_345 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 345 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_345 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_346 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 346 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_346 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_347 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 347 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_347 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_348 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 348 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_348 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_349 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 349 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_349 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_350 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 350 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.tailW_350 real y) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_351 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_352 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_353 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_354 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_355 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_356 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 356 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_356 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  exact absurd hi (by omega)

#print axioms evSeg_11
end ArmBridge.CruxGenGuarded.EvSteps
