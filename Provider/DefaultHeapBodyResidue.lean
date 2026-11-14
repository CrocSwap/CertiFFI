-- SIMD, scrub and flag conclusions from the actual default heap run.
import DefaultHeapBody
import DefaultHeapNcv
import DefaultHeapClassRows08
import DefaultHeapMemRows05
import HeapV2StepCerts.ScrubBind

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open HeapV2StepCerts CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf)
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024
set_option Elab.async false

namespace ReleaseProfile.DefaultHeapRun

theorem body_z (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (pins : HeapV2E17.Pins)
    (entry : NativeState) (budget : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore)
    (hb : 357 ≤ budget) :
    ∀ k, k ≤ 357 → (stateAt real entry k).regs._Z = entry.regs._Z := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore
      dp hb k (by omega)
    obtain ⟨fin, run, _, z, _⟩ := steps real spec config rows mapping base pins entry budget catalogue
      capacity drawsBefore dp hb k (by omega) _ inv
    rw [EvSteps.stateAt_succ_of run]
    exact z.trans (ih (by omega))

theorem body_scrub (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (pins : HeapV2E17.Pins)
    (entry : NativeState) (budget : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore)
    (hb : 357 ≤ budget) :
    ∀ i : Fin 18, RegBind.regVal (stateAt real entry 357) (.x (Fin.castLE (by decide) i)) = 0#64 := by
  have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore
    dp hb 357 (by decide)
  exact ValBind.scrub_at_357 inv.1.valBind

theorem body_flags350 (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (pins : HeapV2E17.Pins)
    (entry : NativeState) (budget : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore)
    (hb : 357 ≤ budget) :
    Flags.nzcv (stateAt real entry 351).regs = (0#1, 1#1, 0#1, 0#1) := by
  have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore
    dp hb 350 (by decide)
  obtain ⟨fin, run, _, veff, hn, hc, hv⟩ := DefaultHeapNcv.z_classN real spec config rows mapping _
    codeScope (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget 350 catalogue
    (by omega) dp.page (by decide) dp.nodup _ _ _ (fun y => y.regs._PC + 4#64)
    (fun y _ => TailWE.tailWN_350 real y)
    (fun y h => DefaultHeapCode.memNextPlaced spec config rows mapping base budget 350 pins
      (rowsFootprint spec.imageRows).byte catalogue dp.static 0xa4 0xf240083f
      (by decide) (by decide) (by decide) y h)
    (fun y h => DefaultHeapCode.memFetch spec config rows mapping base budget 350 pins
      (rowsFootprint spec.imageRows).byte catalogue dp.static 0xa4 0xf240083f
      (by decide) (by decide) _ (by decide) y h) _ inv.1.body.core
  have hz := ValBind.zbind_350 inv.1.valBind veff
  rw [EvSteps.stateAt_succ_of run]
  exact Prod.ext hn (Prod.ext (hz (by decide) (by decide)) (Prod.ext hc hv))

#print axioms body_z
#print axioms body_scrub
#print axioms body_flags350
theorem body_memory_flags (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, 351 ≤ k → k ≤ 355 →
      Flags.nzcv (stateAt real entry (k + 1)).regs = Flags.nzcv (stateAt real entry k).regs := by
  intro k lo hi
  rcases (show k = 351 ∨ k = 352 ∨ k = 353 ∨ k = 354 ∨ k = 355 by omega) with rfl | rfl | rfl | rfl | rfl
  · have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb 351 (by decide)
    obtain ⟨fin, run, _, effect⟩ := DefaultHeapMemRows.step_351 real spec config rows mapping base budget pins
      (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic
      dp.pinAligned dp.codeD dp.nodup (by omega) dp.page
      (by simpa only [DefaultHeapBudget.cost_at_351] using dp.rowsRoom 351 (by decide))
      (by simpa only [DefaultHeapBudget.cost_at_351] using dp.rowsNext 351 (by decide)) _ inv.1.body
    rw [EvSteps.stateAt_succ_of run]
    exact effect.2.2.2.2.2.1
  · have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb 352 (by decide)
    obtain ⟨fin, run, _, effect⟩ := DefaultHeapMemRows.step_352 real spec config rows mapping base budget pins
      (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic
      dp.pinAligned dp.codeD dp.nodup (by omega) dp.page
      (by simpa only [DefaultHeapBudget.cost_at_352] using dp.rowsRoom 352 (by decide))
      (by simpa only [DefaultHeapBudget.cost_at_352] using dp.rowsNext 352 (by decide)) _ inv.1.body
    rw [EvSteps.stateAt_succ_of run]
    exact effect.2.2.2.2.2.1
  · have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb 353 (by decide)
    obtain ⟨fin, run, _, effect⟩ := DefaultHeapMemRows.step_353 real spec config rows mapping base budget pins
      (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic
      dp.pinAligned dp.codeD dp.nodup (by omega) dp.page
      (by simpa only [DefaultHeapBudget.cost_at_353] using dp.rowsRoom 353 (by decide))
      (by simpa only [DefaultHeapBudget.cost_at_353] using dp.rowsNext 353 (by decide)) _ inv.1.body
    rw [EvSteps.stateAt_succ_of run]
    exact effect.2.2.2.2.2.1
  · have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb 354 (by decide)
    obtain ⟨fin, run, _, effect⟩ := DefaultHeapMemRows.step_354 real spec config rows mapping base budget pins
      (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic
      dp.pinAligned dp.codeD dp.nodup (by omega) dp.page
      (by simpa only [DefaultHeapBudget.cost_at_354] using dp.rowsRoom 354 (by decide))
      (by simpa only [DefaultHeapBudget.cost_at_354] using dp.rowsNext 354 (by decide)) _ inv.1.body
    rw [EvSteps.stateAt_succ_of run]
    exact effect.2.2.2.2.2.1
  · have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb 355 (by decide)
    obtain ⟨fin, run, _, effect⟩ := DefaultHeapMemRows.step_355 real spec config rows mapping base budget pins
      (rowsFootprint spec.imageRows).byte catalogue entry capacity drawsBefore dp.static dp.dataStatic
      dp.pinAligned dp.codeD dp.nodup (by omega) dp.page
      (by simpa only [DefaultHeapBudget.cost_at_355] using dp.rowsRoom 355 (by decide))
      (by simpa only [DefaultHeapBudget.cost_at_355] using dp.rowsNext 355 (by decide)) _ inv.1.body
    rw [EvSteps.stateAt_succ_of run]
    exact effect.2.2.2.2.2.1

theorem body_flags356 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    Flags.nzcv (stateAt real entry 357).regs = Flags.nzcv (stateAt real entry 356).regs := by
  have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb 356 (by decide)
  obtain ⟨fin, run, _, _, flags⟩ := DefaultHeapNcv.z_classF real spec config rows mapping _
    codeScope (HeapV2.image base) base dp.static.separated base HeapV2Compose.offsetOf budget 356 catalogue
    (by omega) dp.page (by decide) dp.nodup _ _ _ (fun y => y.regs._PC + 4#64)
    (fun y _ => TailWE.tailWF_356 real y)
    (fun y h => DefaultHeapCode.memNextPlaced spec config rows mapping base budget 356 pins
      (rowsFootprint spec.imageRows).byte catalogue dp.static 0xbc 0x910103ff
      (by decide) (by decide) (by decide) y h)
    (fun y h => DefaultHeapCode.memFetch spec config rows mapping base budget 356 pins
      (rowsFootprint spec.imageRows).byte catalogue dp.static 0xbc 0x910103ff
      (by decide) (by decide) _ (by decide) y h) _ inv.1.body.core
  rw [EvSteps.stateAt_succ_of run]
  exact flags

theorem body_nzcv (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    Flags.nzcv (stateAt real entry 357).regs = (0#1, 1#1, 0#1, 0#1) := by
  have keep (k : Nat) (lo : 351 ≤ k) (hi : k ≤ 356) :
      Flags.nzcv (stateAt real entry (k + 1)).regs = Flags.nzcv (stateAt real entry k).regs := by
    by_cases last : k = 356
    · subst k
      exact body_flags356 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
    · exact body_memory_flags real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo (by omega)
  have all : ∀ n, n ≤ 6 →
      Flags.nzcv (stateAt real entry (351 + n)).regs = (0#1, 1#1, 0#1, 0#1) := by
    intro n hn
    induction n with
    | zero =>
      exact body_flags350 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb
    | succ n ih =>
      rw [show 351 + (n + 1) = (351 + n) + 1 by omega]
      exact (keep (351 + n) (by omega) (by omega)).trans (ih (by omega))
  exact all 6 (by decide)

#print axioms body_memory_flags
#print axioms body_flags356
#print axioms body_nzcv
end ReleaseProfile.DefaultHeapRun
