import Bridge.CruxGenGuarded.ChainInvV4At
import Bridge.CruxGenGuarded.EvSteps.EvBase
import HeapV2StepCerts.MemStepsV4E_04
import HeapV2StepCerts.RegValStepsE04
import HeapV2StepCerts.RegValStepsE05
import HeapV2StepCerts.StepsV2_04
import HeapV2StepCerts.StepsV2_05
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
  IO.eprintln "CURRENT_DECL EvSteps.evSeg_10"
  (← IO.getStderr).flush

theorem evSeg_10 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 300 ≤ k → k < 330 → EvStep real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_300 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 300 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_300 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_301 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 301 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_301 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_302 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 302 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_302 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_303 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 303 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_303 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_304 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 304 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_304 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_305 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 305 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_305 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_306 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 306 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_306 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_307 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 307 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_307 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_308 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 308 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_308 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_309 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 309 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_309 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_310 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 310 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_310 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_311 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 311 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_311 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_312 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 312 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_312 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_313 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 313 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_313 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_314 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 314 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_314 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_315 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 315 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_315 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_316 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 316 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_316 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_317 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 317 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_317 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_318 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 318 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_318 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_319 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 319 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_319 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_320 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 320 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_320 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_321 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 321 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_321 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_322 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 322 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_322 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_323 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 323 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_323 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_324 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 324 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_324 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_325 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 325 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_325 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_326 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 326 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_326 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_327 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 327 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_327 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_328 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 328 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_328 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    obtain ⟨fin, run, _, r⟩ := HeapV2StepCerts.memStep4E_329 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
      dp.dataStatic dp.pinAligned dp.codeD dp.nodup (by omega) dp.page x inv.v3
    exact ⟨fin, run, r.2.2.2.2.2.2.1⟩
  exact absurd hi (by omega)

#print axioms evSeg_10
end ArmBridge.CruxGenGuarded.EvSteps
