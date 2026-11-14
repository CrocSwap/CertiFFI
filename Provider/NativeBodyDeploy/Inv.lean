-- (heap-v2 premise D): BodyDeployInv, the invariant-indexed replacement for shim_release_v2_inv's `dp`.
-- For every state x satisfying the step-7 shim invariant (plan_shim_bl's output inside shim_release_v2_inv) and the
-- run facts the shim chain gives at sigma7 relative to the shim entry e, DeploymentPremises x. All other inputs are
-- ENTRY / deployment-static premises; no stateAt.
import NativeBodyDeploy.Assemble
import TranslateShim.ClosedCmap
import RtShim2.ShimMem
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace NativeBodyDeploy
open ArmBridge.CruxGenGuarded.Release (shimMap)

/-- What the shim prologue gives at sigma7 = x relative to the shim entry e (all from the chain inside
    shim_release_v2_inv: memPre/slot from the STP store and frame, SP from sub sp + BL, x0..x3 untouched by the
    prologue, CallerResidue from controls6 + BL SysEq2). -/
structure RunFacts7 (pins : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (e x : NativeState) : Prop where
  memPre : ∀ a, ¬ RtShim2.ShimMem.slotBytes pins mapping a → x.mem[a]? = e.mem[a]?
  slotPresent : ∀ a, RtShim2.ShimMem.slotBytes pins mapping a → (x.mem[a]?).isSome
  sp : x.regs.SP_EL0 = BitVec.ofInt 64 ((pins.sp : Nat) : Int)
  x0 : HeapV2StepCerts.RegBind.regVal x (.x 0) = HeapV2StepCerts.RegBind.regVal e (.x 0)
  x1 : HeapV2StepCerts.RegBind.regVal x (.x 1) = HeapV2StepCerts.RegBind.regVal e (.x 1)
  q : qOf x = qOf e
  residue : RtBl.CallerInv.CallerResidue x

/-- The entry-level / deployment premises D needs (besides release_heapv2's existing ones). -/
structure BodyEntry {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (scope : Nat → Prop) (offS : Nat → BitVec 64) (e : NativeState) : Prop where
  S : BodyStatic spec mapping base pins
  hoff : offS 7 = HeapV2Compose.offsetOf 0
  hscope : ∀ o, HeapV2StepCerts.codeScope o → scope o
  presentE : HeapV2StepCerts.C3.DataPresent pins mapping e
  x0E : HeapV2StepCerts.RegBind.regVal e (.x 0) = BitVec.ofInt 64 ((pins.x0 : Nat) : Int)
  x1E : HeapV2StepCerts.RegBind.regVal e (.x 1) = BitVec.ofInt 64 ((pins.x1 : Nat) : Int)
  normal : HeapV2StepCerts.ValBind.NormalPath pins (qOf e)

/-- DataPresent across the prologue: unchanged outside the slot, slot bytes present (Memory's dataPresent_shim, inline). -/
theorem present_shim {pins : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} {e x : NativeState}
    (memPre : ∀ a, ¬ RtShim2.ShimMem.slotBytes pins mapping a → x.mem[a]? = e.mem[a]?)
    (slotPresent : ∀ a, RtShim2.ShimMem.slotBytes pins mapping a → (x.mem[a]?).isSome)
    (h : HeapV2StepCerts.C3.DataPresent pins mapping e) : HeapV2StepCerts.C3.DataPresent pins mapping x :=
  HeapV2StepCerts.C3.DataPresent.carry (fun a ha => by
    by_cases hs : RtShim2.ShimMem.slotBytes pins mapping a
    · exact slotPresent a hs
    · rw [memPre a hs]; exact ha) h

/-- **BodyDeployInv**: the `dp` premise of shim_release_v2_inv, invariant-indexed. -/
theorem bodyDeployInv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (scope : Nat → Prop) (offS : Nat → BitVec 64)
    (budget bodyBudget : Nat) (e : NativeState)
    (E : BodyEntry spec mapping base pins scope offS e) (hbudget : budget - 7 = bodyBudget) :
    ∀ x, RtShim2.ShimInv spec config rows mapping (shimMap spec mapping base pins) scope (HeapV2.image base) base base offS
        budget 7 x →
      RunFacts7 pins mapping e x → DeploymentPremises spec config rows mapping base pins x bodyBudget := by
  intro x i7 R
  exact bodyDeploy spec config rows mapping base pins scope (HeapV2.image base) base offS budget bodyBudget x E.S i7
    E.hoff hbudget (TranslateShim.closed_cmap_of_shim x i7) (fun o h => i7.v2.placed o (E.hscope o h))
    (present_shim R.memPre R.slotPresent E.presentE) R.sp (R.x0.trans E.x0E) (R.x1.trans E.x1E)
    (by rw [R.q]; exact E.normal) R.residue

#print axioms present_shim
#print axioms bodyDeployInv
end NativeBodyDeploy
