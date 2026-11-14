-- Body deployment from the actual shim entry and deployment-static facts.
import DefaultHeapRunBase
import DefaultHeapShimPre
import NativeBodyDeploy.Inv
import TranslateShim.ClosedCmap

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
open CertiFFI.Prog.Generic.ModelRunView
open ArmBridge.Boundary ArmBridge.CruxCore HeapV2StepCerts RtDit RtDit.Shim
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.ChainInvV3
open ArmBridge.CruxGenGuarded.Release (shimMap)
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapRun

#check "CURRENT_DECL heap body_deployment"
theorem body_deployment {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (scope : Nat → Prop) (offS : Nat → BitVec 64)
    (budget bodyBudget : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (E : NativeBodyDeploy.BodyEntry spec mapping base pins scope offS entry)
    (hbudget : budget - 7 = bodyBudget)
    (x : NativeState)
    (i7 : DefaultCurrent.CurrentInv spec config rows mapping (shimMap spec mapping base pins) scope
      (HeapV2.image base) base base offS budget 7 catalogue x)
    (R : NativeBodyDeploy.RunFacts7 pins mapping entry x)
    (bodyRows : NativeMteTagCheck.TagStatusRows x (x.choiceOcc.getD 1354 0) DefaultHeapBudget.capacity) :
    DeploymentPremises spec config rows mapping base pins x bodyBudget catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws where
  static := E.S.static
  dataStatic := E.S.dataStatic
  pinAligned := E.S.pinAligned
  codeD := E.S.codeD
  sep := E.S.sep
  mapped := E.S.mapped
  page := E.S.page
  low := E.S.low
  agrees := E.S.agrees
  np := by rw [R.q]; exact E.normal
  init :=
    { core :=
        { v1 :=
            { pins := i7.v1.pins
              features := i7.v1.features
              debug := i7.v1.debug
              current := i7.v1.current
              quiet := by rw [Nat.sub_zero, ← hbudget]; exact i7.v1.quiet
              gic := i7.v1.gic
              pc := by rw [i7.v1.pc, E.hoff] }
          closed := TranslateShim.closed_cmap_of_shimMap i7.closed
          placed := fun o ho => i7.placed o (E.hscope o ho)
          branch := i7.branch
          raw := i7.raw
          noUpd := i7.noUpd
          post := i7.post
          mode := i7.mode
          debug := i7.debug
          feat := i7.feat
          dcache := i7.dcache
          controls := i7.controls }
      regBind := HeapV2StepCerts.RegBind.initial R.sp (R.x0.trans E.x0E) (R.x1.trans E.x1E)
      present := NativeBodyDeploy.present_shim R.memPre R.slotPresent E.presentE
      statusRows := bodyRows
      trace := ⟨0, NativeMteTagCheck.choice_delta_refl x, Nat.zero_le _⟩
      control := RtPremC.CtlRel.refl spec x }
  nodup := E.S.nodup
  residue := R.residue
  rowsRoom := DefaultHeapBudget.rows_room
  rowsNext := fun k _ => DefaultHeapBudget.rows_next k

#check "CURRENT_DECL heap prologue_run_facts"
theorem prologue_run_facts (real : Type) [Sail.SailReal real] (L : Nat)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (scope : Nat → Prop)
    (offS : Nat → BitVec 64) (budget : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (globalCapacity : Nat)
    (pre : DefaultHeapShimPre.ShimPreMG real L spec config rows mapping pins scope
      (HeapV2.image base) base base offS budget catalogue globalCapacity entry) :
    NativeBodyDeploy.RunFacts7 pins mapping entry (stateAt real entry 7) where
  memPre := pre.memPre
  slotPresent := by
    intro a ha
    obtain ⟨n, hn, lo, hi⟩ := ha
    have delta : a = n + (a - n) := by omega
    rw [delta, pre.mem47, pre.slot4 n hn (a - n) (by omega)]
    rfl
  sp := by simpa using pre.sp7
  x0 := pre.keepPre ⟨0, by decide⟩ (by decide) (by decide)
  x1 := pre.keepPre ⟨1, by decide⟩ (by decide) (by decide)
  q := by
    unfold qOf
    simp only [HeapV2StepCerts.RegBind.regVal]
    rw [pre.keepPre 2 (by decide) (by decide), pre.keepPre 3 (by decide) (by decide)]
  residue := pre.residue7

#check "CURRENT_DECL heap body_deployment_of_prologue"
theorem body_deployment_of_prologue (real : Type) [Sail.SailReal real] (L : Nat)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (scope : Nat → Prop) (offS : Nat → BitVec 64)
    (budget bodyBudget : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (globalCapacity : Nat)
    (E : NativeBodyDeploy.BodyEntry spec mapping base pins scope offS entry)
    (hbudget : budget - 7 = bodyBudget)
    (rowRoom : DefaultHeapBudget.capacity + 1 ≤ globalCapacity)
    (pre : DefaultHeapShimPre.ShimPreMG real L spec config rows mapping pins scope
      (HeapV2.image base) base base offS budget catalogue globalCapacity entry) :
    DeploymentPremises spec config rows mapping base pins (stateAt real entry 7) bodyBudget catalogue DefaultHeapBudget.capacity DefaultHeapBudget.prefixDraws := by
  obtain ⟨used, prefixChoice, bound⟩ := pre.choice7
  have bodyRows : NativeMteTagCheck.TagStatusRows (stateAt real entry 7)
      ((stateAt real entry 7).choiceOcc.getD 1354 0) DefaultHeapBudget.capacity := by
    intro index within
    rw [prefixChoice.1, prefixChoice.2]
    simpa only [Nat.add_assoc] using pre.statusRows (used + index) (by omega)
  exact body_deployment spec config rows mapping base pins scope offS budget bodyBudget entry catalogue E hbudget
    _ pre.inv7 (prologue_run_facts real L spec config rows mapping base pins scope offS budget entry catalogue globalCapacity pre) bodyRows

#check "CURRENT_DECL heap prologue_saved_dit"
theorem prologue_saved_dit (real : Type) [Sail.SailReal real] (L : Nat)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (scope : Nat → Prop)
    (offS : Nat → BitVec 64) (budget : Nat) (entry : NativeState) (catalogue : NativeMteTagCheck.ControlCatalogue) (globalCapacity : Nat)
    (pre : DefaultHeapShimPre.ShimPreMG real L spec config rows mapping pins scope
      (HeapV2.image base) base base offS budget catalogue globalCapacity entry)
    (room : 3 ≤ budget) (page : base.toNat % 4096 = 0)
    (aligned : ∀ j, (offS j).toNat % 4 = 0)
    (ob0 : FetchObligations spec config rows mapping NativeEntryDispatch.BtiC.word entry)
    {w1 : BitVec 32} {writes1 : NativeEntry.Effects.Writes} {K1 : Int}
    {us1 : List (HeapV2StepCerts.RegBind.Reg × HeapV2StepCerts.RegBind.Upd)}
    (tail1 : HeapV2StepCerts.RegValE.ClassTailVAt real w1 writes1 K1 (stateAt real entry 1)
      ((stateAt real entry 1).regs._PC + 4#64) us1)
    (hw1 : writes1.dit = false)
    (ob1 : FetchObligations spec config rows mapping w1 (stateAt real entry 1))
    (prof2 : NativeEntryAdapters.MrsDit.Profile (stateAt real entry 2))
    (ob2 : FetchObligations spec config rows mapping (NativeEntryDispatch.MrsDit.word 9#5) (stateAt real entry 2)) :
    (stateAt real entry 3).regs.gpr[9].extractLsb 24 24 = entry.regs.PSTATE.DIT := by
  have d1 : (stateAt real entry 1).regs.PSTATE.DIT = entry.regs.PSTATE.DIT := by
    obtain ⟨out, run, dit, _, _⟩ := DefaultHeapShimEffects.shim_class real spec config rows mapping _ scope
      (HeapV2.image base) base base offS budget 0 catalogue (by omega) page (aligned 0) _ (pre.inv 0 (by omega))
      (NativeShimTails.btiC_tailVAt real entry) rfl ob0
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
    exact dit
  have d2 : (stateAt real entry 2).regs.PSTATE.DIT = (stateAt real entry 1).regs.PSTATE.DIT := by
    obtain ⟨out, run, dit, _, _⟩ := DefaultHeapShimEffects.shim_class real spec config rows mapping _ scope
      (HeapV2.image base) base base offS budget 1 catalogue (by omega) page (aligned 1) _ (pre.inv 1 (by omega))
      (RtDit.Release.classE_toV tail1) hw1 ob1
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
    exact dit
  obtain ⟨out, run, saved, _, _⟩ := DefaultHeapShimEffects.shim_mrs9 real spec config rows mapping _ scope
    (HeapV2.image base) base base offS budget 2 catalogue (by omega) page (aligned 2) _ (pre.inv 2 (by omega)) prof2 ob2
  have encoded : (stateAt real entry 3).regs.gpr[9] =
      (0#39 +++ (stateAt real entry 2).regs.PSTATE.DIT) +++ 0#24 := by
    rw [ArmBridge.CruxGenGuarded.EvSteps.stateAt_succ_of run]
    exact saved
  rw [encoded, d2, d1, RtDit.Window.enc_bit]

#print axioms body_deployment
#print axioms prologue_run_facts
#print axioms body_deployment_of_prologue
#print axioms prologue_saved_dit
end ReleaseProfile.DefaultHeapRun
