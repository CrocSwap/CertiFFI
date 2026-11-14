-- H-P1 end to end with RegionsInjective and slotSep discharged from the walk:
-- regionsInjective_of_walk / slotSep_of_walk. Remaining premises:
--   catalogued: DataBytesLinear (interim row), NoDoubleMapPA + NoDoubleMapSlot (comp:deploy:no-double-mapping),
--               RegionsDisjoint + alignment + slot disjointness/bounds (caller contract);
-- pending producers (asked of): AccessLeaf, SlotLeaf (E17 / shim walk facts), hpres (input presence at σ7).
import HP1Int.Functional
import TranslateMem.WalkInjSlot
import TranslateMem.WalkE17
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue.HeapV2Plan
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
open ArmBridge.Draft ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General

theorem functional_heapv2_walk (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
    (base : BitVec 64) {offS : Nat → BitVec 64} (budget : Nat) (e : NativeState) {callerPC : BitVec 64}
    (ch : RtDit.Release.ShimChain real spec config rows mapping pins scope image loadBase base offS budget e callerPC)
    (memPre : ∀ a, ¬ RtShim2.ShimMem.slotBytes pins mapping a → (stateAt real e 7).mem[a]? = e.mem[a]?)
    (memPost : ∀ a : Nat, (stateAt real e 369).mem[a]? = (stateAt real e 364).mem[a]?)
    (bodyBudget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins (stateAt real e 7) bodyBudget) (hb : 357 ≤ bodyBudget)
    -- catalogued rows
    (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (ndPA : TranslateMem.NoDoubleMapPA pins mapping) (ndSlot : TranslateMem.NoDoubleMapSlot pins mapping)
    (hd : TranslateMem.RegionsDisjoint pins) (aligned : pins.sp % 16 = 0 ∧ pins.x0 % 16 = 0 ∧ pins.x1 % 16 = 0)
    (slotDisj : pins.x1 + 32 ≤ pins.sp ∨ pins.sp + 16 ≤ pins.x1) (spHi : pins.sp + 16 ≤ 2 ^ 64)
    -- walk facts (producers pending)
    (walk : TranslateMem.AccessLeaf pins mapping) (slotLeaf : TranslateMem.SlotLeaf pins mapping)
    (hpres : ∀ j, j < 32 → ∃ b, Release.bufByte mapping (stateAt real e 7) pins.x1 j = some b) :
    Release.Functional mapping pins e (stateAt real e 369) :=
  functional_heapv2 real spec config rows mapping pins base budget e ch memPre memPost
    (TranslateMem.slotSep_of_walk pins mapping hd aligned walk dbl slotLeaf ndSlot slotDisj spHi)
    bodyBudget dp hb dbl (TranslateMem.regionsInjective_of_walk pins mapping hd aligned walk dbl ndPA) hpres

#print axioms functional_heapv2_walk

/-- The shim slot at pins.sp is a leaf output address: the shim chain's closed membership at state 3 (STP) under the
    shim consumer map, which permits the 16-byte data access at sp. -/
theorem slotLeaf_of_chain (real : Type) [Sail.SailReal real] {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {pins : HeapV2E17.Pins} {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
    {base : BitVec 64} {offS : Nat → BitVec 64} {budget : Nat} {e : NativeState} {callerPC : BitVec 64}
    (ch : RtDit.Release.ShimChain real spec config rows mapping pins scope image loadBase base offS budget e callerPC) :
    TranslateMem.SlotLeaf pins mapping :=
  TranslateMem.slotLeaf_of_closed pins (ch.inv 3 (Or.inl (by decide))).v2.closed
    (acc := TranslateMem.dataAcc true) (aligned := true) (size := 16)
    (Or.inr (Or.inr ⟨true, rfl, rfl, TranslateMem.dataAcc_shape true⟩))

#print axioms slotLeaf_of_chain

/-- H-P1 Functional with only catalogued premises (plus the structural shim chain / memory frames / DeploymentPremises):
 AccessLeaf, SlotLeaf and input presence from WalkE17. -/
theorem functional_heapv2_cat (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
    (base : BitVec 64) {offS : Nat → BitVec 64} (budget : Nat) (e : NativeState) {callerPC : BitVec 64}
    (ch : RtDit.Release.ShimChain real spec config rows mapping pins scope image loadBase base offS budget e callerPC)
    (memPre : ∀ a, ¬ RtShim2.ShimMem.slotBytes pins mapping a → (stateAt real e 7).mem[a]? = e.mem[a]?)
    (memPost : ∀ a : Nat, (stateAt real e 369).mem[a]? = (stateAt real e 364).mem[a]?)
    (bodyBudget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins (stateAt real e 7) bodyBudget) (hb : 357 ≤ bodyBudget)
    (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (ndPA : TranslateMem.NoDoubleMapPA pins mapping) (ndSlot : TranslateMem.NoDoubleMapSlot pins mapping)
    (hd : TranslateMem.RegionsDisjoint pins) (aligned : pins.sp % 16 = 0 ∧ pins.x0 % 16 = 0 ∧ pins.x1 % 16 = 0)
    (slotDisj : pins.x1 + 32 ≤ pins.sp ∨ pins.sp + 16 ≤ pins.x1) (spHi : pins.sp + 16 ≤ 2 ^ 64) :
    Release.Functional mapping pins e (stateAt real e 369) :=
  functional_heapv2_walk real spec config rows mapping pins base budget e ch memPre memPost bodyBudget dp hb
    dbl ndPA ndSlot hd aligned slotDisj spHi (TranslateMem.accessLeaf_of_dp dp) (slotLeaf_of_chain real ch)
    (TranslateMem.input_present_of_dp dp)

#print axioms functional_heapv2_cat

end ArmCertValue.HeapV2Plan
