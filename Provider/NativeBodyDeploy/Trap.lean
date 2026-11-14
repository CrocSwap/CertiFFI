-- TrapBodyDeployInv, the trap analogue of bodyDeployInv. For every
-- state x satisfying the step-7 shim invariant and the SAME RunFacts7 as D, NativeTrapG.TrapPremises at x over the
-- decision-181 code-only trap map, plus ONE trap-only run fact: checkCurrentS1Pure at x (register-only S1 config
-- check; the prologue writes no translation registers). All other inputs are entry-level / static (TrapEntry).
import NativeBodyDeploy.Inv
import NativeTrapG.General
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace NativeBodyDeploy
open ArmBridge.CruxGenGuarded.Release (shimMap)

/-- The trap roots' consumer map. -/
abbrev trapMap {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) : ArmCert.Premises.TranslationAgreesV1.ConsumerMap :=
  HeapV2E17.consumerMapOn HeapV2E17.noData pins base.toNat mapping (rowsFootprint spec.imageRows).byte

/-- Closed membership restricts from the shim map to the code-only trap map (its Permitted is contained). -/
theorem closed_trap_of_shimMap {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {base : BitVec 64} {pins : HeapV2E17.Pins}
    {s : ArmCertWalk.State}
    (h : ClosedMembershipAt spec config rows mapping (shimMap spec mapping base pins) s) :
    ClosedMembershipAt spec config rows mapping (trapMap spec mapping base pins) s := by
  intro va acc aligned size perm
  apply h va acc aligned size
  apply HeapV2E17.permittedShim_of_on
  rcases perm with ⟨a, m, hS, _⟩ | hc
  · exact hS.elim
  · exact Or.inr hc

/-- Entry-level / static premises for the trap body premises. -/
structure TrapEntry {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (scope : Nat → Prop) (offS : Nat → BitVec 64) (e : NativeState)
    (rows : List PermissionRow) (tableRows : NativeSourceInit.Plan) : Prop where
  static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte
  agrees : ConsumerMapAgrees spec mapping (trapMap spec mapping base pins)
  page : base.toNat % 4096 = 0
  low : base.toNat < 2 ^ 54
  hoff : offS 7 = HeapV2Compose.offsetOf 0
  presentE : HeapV2StepCerts.C3.DataPresent pins mapping e
  x0E : HeapV2StepCerts.RegBind.regVal e (.x 0) = BitVec.ofInt 64 ((pins.x0 : Nat) : Int)
  x1E : HeapV2StepCerts.RegBind.regVal e (.x 1) = BitVec.ofInt 64 ((pins.x1 : Nat) : Int)
  satE : NativeSourceInit.Satisfies (HeapV2.entryPlan base mapping HeapV2StepCerts.codeOffsets tableRows) e.mem
  planAvoidsSlot : ∀ row ∈ HeapV2.entryPlan base mapping HeapV2StepCerts.codeOffsets tableRows,
    ¬ RtShim2.ShimMem.slotBytes pins mapping row.1
  codeMapped : ∀ o ∈ HeapV2StepCerts.codeOffsets, ∃ pa, mapping (MemReloc.imageAddress base o) = some pa
  codePresent : ∀ o ∈ HeapV2StepCerts.codeOffsets, ∃ byte, HeapV2.image base o = some byte
  tables : ∀ row ∈ imageRowsPlan spec.imageRows, row ∈ tableRows
  declared : PermissionRowsDeclared rows spec.imageRows

/-- **TrapBodyDeployInv**: TrapPremises at every step-7 shim state, from TrapEntry and RunFacts7. -/
theorem trapBodyDeployInv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (scope : Nat → Prop) (offS : Nat → BitVec 64)
    (budget bodyBudget : Nat) (e : NativeState) (tableRows : NativeSourceInit.Plan)
    (E : TrapEntry spec mapping base pins scope offS e rows tableRows) (hbudget : budget - 7 = bodyBudget) :
    ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope (HeapV2.image base) base base offS
        budget 7 x →
      RunFacts7 pins mapping e x →
      checkCurrentS1Pure spec config rows x.regs = true →
      NativeTrapG.TrapPremises spec config rows mapping (trapMap spec mapping base pins) base pins tableRows bodyBudget x := by
  intro x i7 R checkedX
  have x0 := R.x0.trans E.x0E
  have x1 := R.x1.trans E.x1E
  simp only [HeapV2StepCerts.RegBind.regVal] at x0 x1
  exact
  { static := E.static
    agrees := E.agrees
    page := E.page
    low := E.low
    regsOK :=
      { pins := i7.v2.v1.pins
        features := i7.v2.v1.features
        debug := i7.v2.v1.debug
        gic := i7.v2.v1.gic
        pc := by rw [i7.v2.v1.pc, E.hoff]
        branch := i7.v2.branch
        sp := R.sp
        x0 := x0
        x1 := x1
        post2 := i7.post2
        mode := i7.mode
        edebug := i7.debug
        feat := i7.feat
        dcache := i7.dcache
        checked := checkedX
        noUpd := i7.noUpd }
    memOK :=
      { sat := fun row mem => by rw [R.memPre row.1 (E.planAvoidsSlot row mem)]; exact E.satE row mem
        codeMapped := E.codeMapped
        codePresent := E.codePresent
        tables := E.tables
        declared := E.declared
        present := present_shim R.memPre R.slotPresent E.presentE }
    closed := ChainInvV2.closed_of_before_fetch x (closed_trap_of_shimMap i7.v2.closed)
    quiet := by rw [← hbudget]; exact i7.v2.v1.quiet }

#print axioms closed_trap_of_shimMap
#print axioms trapBodyDeployInv
end NativeBodyDeploy
