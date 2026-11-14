-- Actual prologue/body oracle and descriptor transport to the epilogue entry.
import DefaultHeapBodyEntry
import DefaultHeapBody
import DefaultHeapShimControl

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open CertiFFI.Prog.Generic.ModelRunView
open ArmBridge.CruxGenGuarded.Release (shimMap)
open HeapV2StepCerts NativeMteTagCheck
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapShimBody

#check "CURRENT_DECL default shim body transport"
theorem body_transport (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (offS : Nat → BitVec 64) (budget : Nat) (entry : NativeState)
    (catalogue : ControlCatalogue) (capacity : Nat)
    (E : NativeBodyDeploy.BodyEntry spec mapping base pins scope offS entry)
    (pre : DefaultHeapShimPre.ShimPreMG real 357 spec config rows mapping pins scope
      (HeapV2.image base) base base offS budget catalogue capacity entry)
    (room : 365 ≤ budget) (rowRoom : DefaultHeapBudget.capacity + 2 ≤ capacity)
    (low : (base + offS 365).toNat < 2 ^ 55) :
    RtPremC.CtlRel spec entry (stateAt real entry 365) ∧
    ClosedMembershipAt spec config rows mapping (shimMap spec mapping base pins)
      (beforeFetchState (stateAt real entry 365)) ∧
    (∃ used, ChoiceDelta entry (stateAt real entry 365) used ∧ used ≤ DefaultHeapBudget.capacity + 1) ∧
    TagStatusRows (stateAt real entry 365) ((stateAt real entry 365).choiceOcc.getD 1354 0) 1 := by
  have dp := DefaultHeapRun.body_deployment_of_prologue real 357 spec config rows mapping base pins
    scope offS budget (budget - 7) entry catalogue capacity E rfl
    (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) rowRoom) pre
  obtain ⟨bodyControl, bodyTrace⟩ := DefaultHeapRun.body_return_transport real spec config rows mapping
    base pins (stateAt real entry 7) (budget - 7) catalogue DefaultHeapBudget.capacity
    DefaultHeapBudget.prefixDraws dp (Nat.le_sub_of_add_le room)
    (by rw [pre.x30_7]; exact low)
  have index := RtDit.Window.stateAt_add real entry 7 358
  rw [← index] at bodyControl bodyTrace
  obtain ⟨bodyUsed, bodyChoice, bodyBound⟩ := bodyTrace
  obtain ⟨preUsed, preChoice, preBound⟩ := pre.choice7
  have totalChoice := choice_delta_trans preChoice bodyChoice
  have totalBound : preUsed + bodyUsed ≤ DefaultHeapBudget.capacity + 1 := by
    change bodyUsed ≤ DefaultHeapBudget.capacity at bodyBound
    simpa only [Nat.add_comm] using Nat.add_le_add preBound bodyBound
  refine ⟨pre.control7.trans bodyControl, RtPremC.closed_across pre.inv7.closed bodyControl,
    ⟨preUsed + bodyUsed, totalChoice, totalBound⟩, ?_⟩
  have remaining : preUsed + bodyUsed + 1 ≤ capacity :=
    Nat.le_trans (Nat.add_le_add_right totalBound 1) rowRoom
  intro index within
  rw [totalChoice.1, totalChoice.2]
  simpa only [Nat.add_assoc] using pre.statusRows (preUsed + bodyUsed + index)
    (Nat.lt_of_lt_of_le (Nat.add_lt_add_left within _) remaining)

#print axioms body_transport
theorem return_current (real : Type) [Sail.SailReal real] {domain : QueryDomain}
    (spec : TopologyImageSpec domain) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (offS : Nat → BitVec 64) (budget : Nat) (entry : NativeState)
    (catalogue : ControlCatalogue) (capacity : Nat)
    (E : NativeBodyDeploy.BodyEntry spec mapping base pins scope offS entry)
    (pre : DefaultHeapShimPre.ShimPreMG real 357 spec config rows mapping pins scope
      (HeapV2.image base) base base offS budget catalogue capacity entry)
    (room : 365 ≤ budget) (rowRoom : DefaultHeapBudget.capacity + 2 ≤ capacity)
    (low : (base + offS 365).toNat < 2 ^ 55)
    (codeStore : ImageTableSeparated scope base mapping (Residue.StoreBytes pins mapping))
    (slotStore : ∀ a, RtShim2.ShimMem.slotBytes pins mapping a → ¬ Residue.StoreBytes pins mapping a) :
    DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins)
      scope (HeapV2.image base) base base offS budget 365 catalogue (stateAt real entry 365) ∧
    (stateAt real entry 365).regs.SP_EL0 = BitVec.ofNat 64 pins.sp ∧
    RtDit.Shim.SlotHas pins mapping
      (ArmCertMem.StpEval.stpData (stateAt real entry 3) 9#5 30#5) (stateAt real entry 365) := by
  have dp := DefaultHeapRun.body_deployment_of_prologue real 357 spec config rows mapping base pins
    scope offS budget (budget - 7) entry catalogue capacity E rfl
    (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) rowRoom) pre
  have inv := DefaultHeapRun.prefixes real spec config rows mapping base pins (stateAt real entry 7)
    (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp
    (Nat.le_trans (by decide : 357 ≤ 358) (Nat.le_sub_of_add_le room)) 357 (by decide)
  have core := inv.1.body.core
  have lr := RtSaved2.lrSaved_of_chain inv.1.lr
  simp only [show (GPRSummary.key (30#5 : BitVec 5).toNat).val = 30 from by decide] at lr
  have ob := DefaultHeapCode.memFetch spec config rows mapping base (budget - 7) 357 pins
    (rowsFootprint spec.imageRows).byte catalogue dp.static 0xc0 0xd65f03c0
    (by decide) (by decide) (EntryBodyRet.W 30#5) (by decide) _ core
  obtain ⟨fin, run, next, _, _, _, _, _, _, _, _⟩ :=
    DefaultHeapShimControl.shim_ret_between real spec config rows mapping _ codeScope (HeapV2.image base)
      base dp.static.separated base HeapV2Compose.offsetOf (budget - 7) 357 catalogue offS budget 365
      (by omega) (by omega) dp.page (by decide) dp.nodup _ core
      (by rw [lr, pre.x30_7]; exact low) (by rw [lr, pre.x30_7]) ob
  have bodyIndex := RtDit.Window.stateAt_add real entry 7 358
  have sameFin : stateAt real entry 365 = fin := by
    rw [bodyIndex]
    exact EvSteps.stateAt_succ_of run
  rw [← sameFin] at next
  obtain ⟨_, _, _, _, spFrame, memFrame⟩ :=
    DefaultHeapRun.body_abi real spec config rows mapping base pins (stateAt real entry 7)
      (budget - 7) catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws dp
      (Nat.le_sub_of_add_le room) (by rw [pre.x30_7]; exact low)
  rw [← bodyIndex] at spFrame memFrame
  have transport := body_transport real spec config rows mapping base pins scope offS budget entry
    catalogue capacity E pre room rowRoom low
  have placed := placed_class_writes memFrame codeStore pre.inv7.placed
  refine ⟨{
    v1 := next.v1
    closed := transport.2.1
    placed := placed
    branch := next.branch
    raw := next.raw
    noUpd := next.noUpd
    post := next.post
    mode := next.mode
    debug := next.debug
    feat := next.feat
    dcache := next.dcache
    controls := next.controls }, spFrame.trans pre.sp7, ?_⟩
  intro n mapped i within
  exact (memFrame (n + i) (slotStore _ ⟨n, mapped, by omega, by omega⟩)).trans
    ((pre.mem47 (n + i)).trans (pre.slot4 n mapped i within))

#print axioms return_current
end ReleaseProfile.DefaultHeapShimBody
