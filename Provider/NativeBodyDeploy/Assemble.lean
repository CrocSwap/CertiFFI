-- DeploymentPremises at the body entry sigma7 assembled
-- from the shim invariant at step 7 (as produced by RtShim2.ShimBranch.plan_shim_bl inside shim_release_v2_inv),
-- the deployment-static facts (BodyStatic, all checkable on the deployment), and the transfers owned by
-- (closedC: closed membership over the BODY consumer map cmap at sigma7),
--   memory (placedC : body code placed at sigma7; presentC : DataPresent at sigma7; both from memPre),
--   the release chain (sp / x0 / x1 register pins, qOf sigma7 = qOf e, CallerResidue at sigma7).
import RtShim2.ShimInv
import HeapV2StepCerts.E17General.Base
import Bridge.CruxGenGuarded.ReleaseHeadline
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace NativeBodyDeploy
open ArmBridge.CruxGenGuarded.Release (shimMap)

/-- The deployment-static fields of DeploymentPremises (each a deployment check, as Memory's codeStatic_of_checks). -/
structure BodyStatic {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) : Prop where
  static : HeapV2StepCerts.CodeStatic mapping base (rowsFootprint spec.imageRows).byte
  dataStatic : HeapV2StepCerts.C3.DataStatic pins mapping (rowsFootprint spec.imageRows)
  pinAligned : ∀ i, HeapV2E17.pin pins i % 16 = 0
  codeD : ImageTableSeparated HeapV2StepCerts.codeScope base mapping (HeapV2StepCerts.MemNext.dataBytes pins mapping)
  sep : RtSaved.SlotSep pins mapping
  mapped : ∃ n, mapping (RtSaved.slotVA pins) = some n
  page : base.toNat % 4096 = 0
  low : base.toNat < 2 ^ 54
  agrees : ConsumerMapAgrees spec mapping (cmap spec mapping base pins)
  nodup : (spec.logicalRows.map (·.logical)).Nodup

/-- **D assembly.** DeploymentPremises at x (= sigma7) from the step-7 shim invariant and the named inputs. -/
theorem bodyDeploy {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (offS : Nat → BitVec 64) (budget bodyBudget : Nat) (x : NativeState)
    (S : BodyStatic spec mapping base pins)
    (i7 : RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope image loadBase base offS budget 7 x)
    (hoff : offS 7 = HeapV2Compose.offsetOf 0) (hbudget : budget - 7 = bodyBudget)
    (closedC : ClosedMembershipAt spec config rows mapping (cmap spec mapping base pins)
      (ArmBridge.CruxGenGuarded.beforeFetchState x))
    (placedC : MemReloc.ImageOn HeapV2StepCerts.codeScope (HeapV2.image base) x base mapping)
    (presentC : HeapV2StepCerts.C3.DataPresent pins mapping x)
    (spX : x.regs.SP_EL0 = BitVec.ofInt 64 ((pins.sp : Nat) : Int))
    (x0X : HeapV2StepCerts.RegBind.regVal x (.x 0) = BitVec.ofInt 64 ((pins.x0 : Nat) : Int))
    (x1X : HeapV2StepCerts.RegBind.regVal x (.x 1) = BitVec.ofInt 64 ((pins.x1 : Nat) : Int))
    (np : HeapV2StepCerts.ValBind.NormalPath pins (qOf x))
    (residue : RtBl.CallerInv.CallerResidue x) :
    DeploymentPremises spec config rows mapping base pins x bodyBudget where
  static := S.static
  dataStatic := S.dataStatic
  pinAligned := S.pinAligned
  codeD := S.codeD
  sep := S.sep
  mapped := S.mapped
  page := S.page
  low := S.low
  agrees := S.agrees
  np := np
  init3 :=
    { v2 := { v1 := { pins := i7.v2.v1.pins
                      features := i7.v2.v1.features
                      debug := i7.v2.v1.debug
                      current := i7.v2.v1.current
                      quiet := by rw [Nat.sub_zero, ← hbudget]; exact i7.v2.v1.quiet
                      gic := i7.v2.v1.gic
                      pc := by rw [i7.v2.v1.pc, hoff] }
              closed := closedC
              placed := placedC
              branch := i7.v2.branch }
      regBind := HeapV2StepCerts.RegBind.initial spX x0X x1X
      present := presentC
      raw := i7.raw
      noUpd := i7.noUpd
      post2 := i7.post2
      mode := i7.mode
      debug := i7.debug
      feat := i7.feat
      dcache := i7.dcache }
  nodup := S.nodup
  residue := residue

#print axioms bodyDeploy
end NativeBodyDeploy
