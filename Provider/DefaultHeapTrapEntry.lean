-- Actual default-profile trap-body entry from the concrete shim prologue.
import DefaultHeapTrapBase
import DefaultHeapBodyEntry
import NativeBodyDeploy.TrapM

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.Release (shimMap)
open HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false

namespace ReleaseProfile.DefaultHeapTrap

theorem closed_all_of_shimMap {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {base : BitVec 64} {pins : HeapV2E17.Pins} {s : ArmCertWalk.State}
    (closed : ClosedMembershipAt spec config rows mapping (shimMap spec mapping base pins) s) :
    ClosedMembershipAt spec config rows mapping
      (HeapV2E17.consumerMapOn (fun _ => True) pins base.toNat mapping
        (rowsFootprint spec.imageRows).byte) s := by
  intro va acc aligned size permitted
  apply TranslateShim.closed_cmap_of_shimMap closed va acc aligned size
  rcases permitted with ⟨entry, member, _, data⟩ | code
  · exact Or.inl ⟨entry, member, data⟩
  · exact Or.inr code

theorem body_deployment {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (S : Nat × Nat × Int × Nat × Bool → Prop) (base : BitVec 64) (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (offS : Nat → BitVec 64) (budget bodyBudget : Nat)
    (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (tableRows : NativeSourceInit.Plan)
    (E : NativeBodyDeploy.TrapEntryM spec mapping
      (HeapV2E17.consumerMapOn S pins base.toNat mapping (rowsFootprint spec.imageRows).byte)
      base pins scope offS entry rows tableRows)
    (restrict : ∀ s : ArmCertWalk.State,
      ClosedMembershipAt spec config rows mapping (shimMap spec mapping base pins) s →
      ClosedMembershipAt spec config rows mapping
        (HeapV2E17.consumerMapOn S pins base.toNat mapping (rowsFootprint spec.imageRows).byte) s)
    (hbudget : budget - 7 = bodyBudget) (x : NativeState)
    (i7 : DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins)
      scope (HeapV2.image base) base base offS budget 7 catalogue x)
    (R : NativeBodyDeploy.RunFacts7 pins mapping entry x) :
    BaseInv spec config rows mapping S base bodyBudget pins (rowsFootprint spec.imageRows).byte
      catalogue x HeapV2Compose.offsetOf 0 x := by
  have memory : NativeInit3.EntryMemOK spec rows mapping base tableRows pins x :=
    { sat := fun row member => by
        rw [R.memPre row.1 (E.planAvoidsSlot row member)]
        exact E.satE row member
      codeMapped := E.codeMapped
      codePresent := E.codePresent
      tables := E.tables
      declared := E.declared
      present := NativeBodyDeploy.present_shim R.memPre R.slotPresent E.presentE }
  refine
    { core :=
        { v1 :=
            { pins := i7.v1.pins
              features := i7.v1.features
              debug := i7.v1.debug
              current := i7.v1.current
              quiet := by rw [Nat.sub_zero, ← hbudget]; exact i7.v1.quiet
              gic := i7.v1.gic
              pc := by rw [i7.v1.pc, E.hoff] }
          closed := restrict _ i7.closed
          placed := NativeInit3.placed_of memory
          branch := i7.branch
          raw := i7.raw
          noUpd := i7.noUpd
          post := i7.post
          mode := i7.mode
          debug := i7.debug
          feat := i7.feat
          dcache := i7.dcache
          controls := i7.controls }
      regBind := RegBind.initial R.sp (R.x0.trans E.x0E) (R.x1.trans E.x1E)
      present := memory.present
      statusRows := ?_
      trace := ⟨0, NativeMteTagCheck.choice_delta_refl x, Nat.le_refl _⟩
      control := RtPremC.CtlRel.refl spec x }
  intro index within
  omega

#print axioms body_deployment
#print axioms closed_all_of_shimMap
end ReleaseProfile.DefaultHeapTrap
