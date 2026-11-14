-- (H-P4): the DIT step family over e17_general's deployment and dit_at (entry_dit over ChainInv3).
import RtDit.Branch
import HeapV2StepCerts.E17General.Base
import Bridge.CruxGenGuarded.ChainInvV4At
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4 HeapV2StepCerts.E17General
open ArmBridge.Boundary ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace RtDit

/-- The DIT step family over e17_general's deployment. -/
def DitStep (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : HeapV2E17.Pins) (entry : NativeState) (budget k : Nat) : Prop :=
  ∀ x, I4 spec config rows mapping base pins entry budget k x →
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT

/-- entry_dit at a ChainInv3 state. -/
theorem dit_at (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (x : NativeState)
    (inv : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x)
    (ob : FetchObligations spec config rows mapping w x)
    (tail : ∀ (final : NativeState) (enc0 : __InstrEnc), DitFetched spec config rows mapping m x final (budget - (k + 1)) →
      ∃ fin, nativeTail real x w enc0 final = .ok () fin ∧ fin.regs.PSTATE.DIT = final.regs.PSTATE.DIT) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  exact entry_dit real spec config rows mapping w x inv.v2.v1.pins inv.v2.v1.gic inv.v2.v1.features inv.v2.v1.debug
    (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned inv.v2.v1.current m inv.v2.closed inv.raw
    inv.noUpd ob tail

#print axioms dit_at
end RtDit
