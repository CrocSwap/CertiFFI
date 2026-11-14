-- Memory: the shim frame facts certiffi's functional_inst takes as hypotheses.
-- Generic (ShimFrameVG / shimFrameVG_of: any in/out buffers, buffer length, slot PA set and run indices) and the
-- heap-v2 instance (ShimFrameV / shimFrameV_heapv2; memPre / memPost from RtShimG.HeapV2.shim_pre_mem / shim_chain_mem).
import RtDit6.ShimChain
import RtShim2.ShimMem
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
namespace ArmCertShim
open ArmBridge.Draft ArmBridge.CruxGenGuarded

/-- Generic shim frame: the input buffer is unchanged from the caller's entry state to the body's start, the output
buffer and x0 are unchanged from the body's end to the caller's return state. -/
structure ShimFrameVG (mapping : BitVec 64 → Option Nat) (inBase outBase n : Nat)
    (sEntry sBody sBodyEnd sRet : NativeState) : Prop where
  inUnchanged : ∀ j, j < n → Release.bufByte mapping sBody inBase j = Release.bufByte mapping sEntry inBase j
  outUnchanged : ∀ i, i < n → Release.bufByte mapping sRet outBase i = Release.bufByte mapping sBodyEnd outBase i
  x0Out : sRet.regs.gpr[0] = sBodyEnd.regs.gpr[0]

/-- ShimFrameVG from: the prologue writes only the slot, the epilogue writes nothing, x0 kept, and the slot's PAs
are not input-buffer PAs (RegionsInjective over {I, O, F, slot}). -/
theorem shimFrameVG_of (mapping : BitVec 64 → Option Nat) (slot : Nat → Prop) (inBase outBase n : Nat)
    (sEntry sBody sBodyEnd sRet : NativeState)
    (memPre : ∀ a, ¬ slot a → sBody.mem[a]? = sEntry.mem[a]?)
    (memPost : ∀ a : Nat, sRet.mem[a]? = sBodyEnd.mem[a]?)
    (x0 : sRet.regs.gpr[0] = sBodyEnd.regs.gpr[0])
    (slotSep : ∀ j, j < n → ∀ q, mapping (BitVec.ofNat 64 (inBase + j)) = some q → ¬ slot q) :
    ShimFrameVG mapping inBase outBase n sEntry sBody sBodyEnd sRet := by
  refine ⟨fun j hj => ?_, fun i _ => ?_, x0⟩
  · unfold Release.bufByte
    cases hm : mapping (BitVec.ofNat 64 (inBase + j)) with
    | none => rfl
    | some q => exact memPre q (slotSep j hj q hm)
  · unfold Release.bufByte
    cases mapping (BitVec.ofNat 64 (outBase + i)) with
    | none => rfl
    | some q => exact memPost q

/-- The heap-v2 instance (fields exactly as certiffi's functional_inst hypotheses inUnch / outUnch / x0Out). -/
abbrev ShimFrameV (real : Type) [Sail.SailReal real] (mapping : BitVec 64 → Option Nat) (pins : HeapV2E17.Pins)
    (e : NativeState) : Prop :=
  ShimFrameVG mapping pins.x1 pins.x0 32 e (stateAt real e 7) (stateAt real e 364) (stateAt real e 369)

theorem shimFrameV_heapv2 (real : Type) [Sail.SailReal real] {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {pins : HeapV2E17.Pins}
    {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word}
    {base : BitVec 64} {offS : Nat → BitVec 64} {budget : Nat} {e : NativeState} {callerPC : BitVec 64}
    (ch : RtDit.Release.ShimChain real spec config rows mapping pins scope image loadBase base offS budget e callerPC)
    (memPre : ∀ a, ¬ RtShim2.ShimMem.slotBytes pins mapping a → (stateAt real e 7).mem[a]? = e.mem[a]?)
    (memPost : ∀ a : Nat, (stateAt real e 369).mem[a]? = (stateAt real e 364).mem[a]?)
    (slotSep : ∀ j, j < 32 → ∀ q, mapping (BitVec.ofNat 64 (pins.x1 + j)) = some q →
      ¬ RtShim2.ShimMem.slotBytes pins mapping q) :
    ShimFrameV real mapping pins e :=
  shimFrameVG_of mapping _ pins.x1 pins.x0 32 e _ _ _ memPre memPost
    (ch.keepPost ⟨0, by decide⟩ (by decide) (by decide)) slotSep

#print axioms shimFrameVG_of
#print axioms shimFrameV_heapv2
end ArmCertShim
