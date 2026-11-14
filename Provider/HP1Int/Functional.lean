-- H-P1 end to end (certiffi): Release.Functional for heap-v2 on the release run, from
-- * hsteps_all (357/357 per-step value facts: class/branch/BL/RET steps, Memory memory steps,
-- value tails v8 incl. Sbcs64),
--   * Memory's shim frame (shimFrameV_heapv2: ShimChain + prologue/epilogue memory frames + slotSep),
--   * the named premises DeploymentPremises at σ7, DataBytesLinear, RegionsInjective and input presence at σ7.
import HP1Int.Steps
import ArmCertShim.ShimFrameV
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue.HeapV2Plan
open ArmCertValue CertiFFI.Prog.Generic.ModelRunView
open ArmBridge.Draft ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.CruxGenGuarded HeapV2StepCerts.E17General

/-- Functional from the shim frame as one structure (any source of ShimFrameV). -/
theorem functional_of_frame (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (e : NativeState) (budget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins (stateAt real e 7) budget) (hb : 357 ≤ budget)
    (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (inj : ArmCertValue.HeapV2Mem.RegionsInjective pins mapping)
    (hpres : ∀ j, j < 32 → ∃ b, Release.bufByte mapping (stateAt real e 7) pins.x1 j = some b)
    (sf : ArmCertShim.ShimFrameV real mapping pins e) :
    Release.Functional mapping pins e (stateAt real e 369) :=
  functional_inst real spec config rows mapping base pins e budget dp hb
    (hsteps_all real spec config rows mapping base pins (stateAt real e 7) budget dp hb dbl inj)
    hpres sf.inUnchanged sf.outUnchanged sf.x0Out

#print axioms functional_of_frame

/-- Functional from Memory's heap-v2 shim chain and its memory frames. -/
theorem functional_heapv2 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
    (base : BitVec 64) {offS : Nat → BitVec 64} (budget : Nat) (e : NativeState) {callerPC : BitVec 64}
    (ch : RtDit.Release.ShimChain real spec config rows mapping pins scope image loadBase base offS budget e callerPC)
    (memPre : ∀ a, ¬ RtShim2.ShimMem.slotBytes pins mapping a → (stateAt real e 7).mem[a]? = e.mem[a]?)
    (memPost : ∀ a : Nat, (stateAt real e 369).mem[a]? = (stateAt real e 364).mem[a]?)
    (slotSep : ∀ j, j < 32 → ∀ q, mapping (BitVec.ofNat 64 (pins.x1 + j)) = some q →
      ¬ RtShim2.ShimMem.slotBytes pins mapping q)
    (bodyBudget : Nat)
    (dp : DeploymentPremises spec config rows mapping base pins (stateAt real e 7) bodyBudget) (hb : 357 ≤ bodyBudget)
    (dbl : ArmCertValue.HeapV2Mem.DataBytesLinear pins mapping)
    (inj : ArmCertValue.HeapV2Mem.RegionsInjective pins mapping)
    (hpres : ∀ j, j < 32 → ∃ b, Release.bufByte mapping (stateAt real e 7) pins.x1 j = some b) :
    Release.Functional mapping pins e (stateAt real e 369) :=
  functional_of_frame real spec config rows mapping base pins e bodyBudget dp hb dbl inj hpres
    (ArmCertShim.shimFrameV_heapv2 real ch memPre memPost slotSep)

#print axioms functional_heapv2

end ArmCertValue.HeapV2Plan
