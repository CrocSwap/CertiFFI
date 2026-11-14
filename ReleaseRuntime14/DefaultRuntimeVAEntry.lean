-- The caller's VA input view at entry and its conversion to the anchored byte view.
import DefaultRuntimeC00Roots
import ArmCertPipe.PhysicalInit

open ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmCertValue

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultRuntime

structure VADeploymentPremises {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (pinv : Nat → Nat)
    (regions : List Region) (σ0 : Sym) (inputs : List (BitVec 64)) (plan : List StepV)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (capacity : Nat) (past : Nat → Nat)
    (entry : NativeState) : Prop where
  separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte
  page : base.toNat % 4096 = 0
  low : base.toNat < 2 ^ 54
  agrees : ConsumerMapAgrees spec mapping m
  room : plan.length ≤ budget
  init : InvG spec config rows mapping m scope image loadBase base offset budget
    (ArmCertPipe.AgreesAt mapping pinv regions σ0 inputs plan) catalogue entry capacity past 0 entry

#check "CURRENT_DECL VADeploymentPremises.anchored"
theorem VADeploymentPremises.anchored {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
    {base : BitVec 64} {offset : Nat → BitVec 64} {budget : Nat} {pinv : Nat → Nat}
    {regions : List Region} {σ0 : Sym} {inputs : List (BitVec 64)} {plan : List StepV}
    {catalogue : NativeMteTagCheck.ControlCatalogue} {capacity : Nat} {past : Nat → Nat}
    {entry : NativeState} {bytePA : ArmCertValue.Physical.BytePA}
    (dp : VADeploymentPremises spec config rows mapping m scope image loadBase base offset budget
      pinv regions σ0 inputs plan catalogue capacity past entry)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (view : ∀ r j i k, σ0.memB r j = some (i, k) →
      bytePA r j = mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + j))) :
    DeploymentPremises spec config rows mapping m scope image loadBase base offset budget
      bytePA regions σ0 inputs plan catalogue capacity past entry :=
  ⟨dp.separated, dp.page, dp.low, dp.agrees, dp.room, nodup,
    ⟨dp.init.core, ArmCertPipe.Physical.zero_of_legacy dp.init.extra view, dp.init.statusRows, dp.init.trace⟩⟩

#print axioms VADeploymentPremises.anchored
end ReleaseProfile.DefaultRuntime
