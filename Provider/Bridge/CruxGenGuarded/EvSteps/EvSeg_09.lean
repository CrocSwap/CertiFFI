import Bridge.CruxGenGuarded.ChainInvV4At
import Bridge.CruxGenGuarded.EvSteps.EvBase
import HeapV2StepCerts.RegValStepsE03
import HeapV2StepCerts.RegValStepsE04
import HeapV2StepCerts.StepsV2_03
import HeapV2StepCerts.StepsV2_04
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
  IO.eprintln "CURRENT_DECL EvSteps.evSeg_09"
  (← IO.getStderr).flush

theorem evSeg_09 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget) (hb : 357 ≤ budget) :
    ∀ k, 270 ≤ k → k < 300 → EvStep real spec config rows mapping base pins entry budget k := by
  intro k lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_270 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 270 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_270 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_271 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 271 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_271 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_272 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 272 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_272 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_273 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 273 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_273 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_274 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 274 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_274 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_275 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 275 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_275 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_276 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 276 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_276 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_277 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 277 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_277 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_278 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 278 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_278 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_279 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 279 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_279 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_280 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 280 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_280 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_281 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 281 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_281 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_282 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 282 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_282 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_283 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 283 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_283 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_284 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 284 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_284 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_285 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 285 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_285 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_286 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 286 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_286 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_287 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 287 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_287 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_288 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 288 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_288 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_289 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 289 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_289 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_290 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 290 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_290 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_291 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 291 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_291 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_292 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 292 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_292 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_293 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 293 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_293 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_294 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 294 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_294 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_295 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 295 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_295 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_296 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 296 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_296 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_297 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 297 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_297 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_298 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 298 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_298 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  rcases Nat.eq_or_lt_of_le lo with rfl | lo
  · intro x inv
    let c := HeapV2StepCerts.cert2_299 real spec config rows mapping base budget pins (rowsFootprint spec.imageRows).byte dp.static
    exact ev_class real spec config rows mapping _ HeapV2StepCerts.codeScope (HeapV2.image base) base dp.static.separated base
      HeapV2Compose.offsetOf budget pins 299 (by omega) dp.page (by decide +kernel) dp.nodup c.word c.writes c.see c.next
      (fun y _ => HeapV2StepCerts.TailWE.ClassTailWAt.ofV (by decide +kernel) (HeapV2StepCerts.RegValE.tailV_299 real y)) (fun y h => c.placedNext y h.v2) (fun y h => c.fetch y h.v2) x inv.v3
  exact absurd hi (by omega)

#print axioms evSeg_09
end ArmBridge.CruxGenGuarded.EvSteps
