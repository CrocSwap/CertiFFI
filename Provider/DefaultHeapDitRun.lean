-- Current-profile heap body with exact ordered records.
import DefaultHeapShimBranch
import DefaultHeapDitSegment00
import DefaultHeapDitSegment01
import DefaultHeapDitSegment02
import DefaultHeapDitSegment03
import DefaultHeapDitSegment04
import DefaultHeapDitSegment05
import DefaultHeapDitSegment06
import DefaultHeapDitSegment07
import DefaultHeapDitSegment08
import DefaultHeapDitSegment09
import DefaultHeapDitSegment10
import DefaultHeapDitSegment11
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded HeapV2StepCerts
open CertiFFI.Prog.Generic.ModelRunView
open HeapV2StepCerts.E17General (qOf low_of)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace ReleaseProfile.DefaultHeapRun


theorem dit_steps (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, k < 357 → ∀ x, RunInv spec config rows mapping base pins entry budget k catalogue capacity drawsBefore x →
      ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  intro k hk
  rcases (show (0 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 90) ∨ (90 ≤ k ∧ k < 120) ∨ (120 ≤ k ∧ k < 150) ∨ (150 ≤ k ∧ k < 180) ∨ (180 ≤ k ∧ k < 210) ∨ (210 ≤ k ∧ k < 240) ∨ (240 ≤ k ∧ k < 270) ∨ (270 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 330) ∨ (330 ≤ k ∧ k < 357) by omega) with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact dit_segment_00 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact dit_segment_01 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact dit_segment_02 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact dit_segment_03 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact dit_segment_04 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact dit_segment_05 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact dit_segment_06 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact dit_segment_07 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact dit_segment_08 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact dit_segment_09 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact dit_segment_10 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi
  · exact dit_segment_11 real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k lo hi

theorem body_dit (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 357 ≤ budget) :
    ∀ k, k ≤ 357 → (stateAt real entry k).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have inv := prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k (by omega)
    obtain ⟨fin, run, dit⟩ := dit_steps real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb k (by omega) _ inv
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
    exact dit.trans (ih (by omega))
#print axioms dit_steps
#print axioms body_dit
theorem ret_dit (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 358 ≤ budget)
    (low : entry.regs.gpr[30].toNat < 2 ^ 55) :
    let x := stateAt real entry 357
    ∃ fin, modelStep real x = .ok () fin ∧
      fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  intro x
  have inv : RunInv spec config rows mapping base pins entry budget 357 catalogue capacity drawsBefore x :=
    prefixes real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp (by omega) 357 (by decide)
  have core := inv.1.body.core
  have lr := RtSaved2.lrSaved_of_chain inv.1.lr
  let w := EntryBodyRet.W 30#5
  have ob := DefaultHeapCode.memFetch spec config rows mapping base budget 357 pins (rowsFootprint spec.imageRows).byte catalogue
    dp.static 0xc0 0xd65f03c0 (by decide) (by decide) w (by decide) x core
  let target := entry.regs.gpr[30]
  have tail := DefaultRuntimeBranch.RichRet.tail_at real x 30#5 (by decide) (by decide)
    (by rw [lr]; exact low) target lr
  have placed : target = base + (target - base) := by rw [BitVec.add_comm, BitVec.sub_add_cancel]
  have hq : HookQuiet ((budget - 358) + 1) x := by
    have e : budget - 358 + 1 = budget - 357 := by omega
    rw [e]; exact core.v1.quiet
  obtain ⟨fin, run, _, _, _, pc, _, _, _, _, _, gpr, sp, mem, _, _, _, _, _, _, _, z, ev, gcs, _, _, dit⟩ :=
    DefaultHeapShimBranch.entry_branch_event real spec config rows mapping w 94 x core.v1.pins target
      (target - base) tail core.v1.gic core.v1.features core.v1.debug (budget - 358) hq base
      (HeapV2Compose.offsetOf 357) core.v1.pc dp.page (by decide) placed core.v1.current
      _ core.closed codeScope (HeapV2.image base) base core.placed dp.static.separated
      core.branch core.raw core.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code dp.nodup
  exact ⟨fin, run, dit⟩


theorem body_dit_return (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (drawsBefore : Nat → Nat)
    (dp : DeploymentPremises spec config rows mapping base pins entry budget catalogue capacity drawsBefore) (hb : 358 ≤ budget)
    (low : entry.regs.gpr[30].toNat < 2 ^ 55) :
    (stateAt real entry 358).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
  obtain ⟨fin, run, dit⟩ := ret_dit real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp hb low
  rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
  exact dit.trans (body_dit real spec config rows mapping base pins entry budget catalogue capacity drawsBefore dp (by omega) 357 (by decide))
#print axioms ret_dit
#print axioms body_dit_return
end ReleaseProfile.DefaultHeapRun
