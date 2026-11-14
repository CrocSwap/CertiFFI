-- Memory (H-P2): the residue run's invariant I5 = I4 ∧ Res (E17General's ChainInv v4 instance plus the frame residue).
import HeapV2StepCerts.Residue.Core
import HeapV2StepCerts.E17General.Base
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
namespace HeapV2StepCerts.Residue.Run
open ArmBridge.Draft ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInvV4
open HeapV2StepCerts.E17General
set_option autoImplicit false

abbrev I5 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget k : Nat) (x : NativeState) : Prop :=
  I4 spec config rows mapping base pins entry budget k x ∧
    Residue.ResL pins mapping base (entry.regs.gpr[19]) (entry.regs.gpr[30]) entry k x

def MemStepsG5 (real : Type) [Sail.SailReal real] {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (pins : HeapV2E17.Pins) (entry : NativeState) (budget : Nat) : Prop :=
  ∀ k, k < 357 → isMem k = true →
    Uget.Chain.Step real (I5 spec config rows mapping base pins entry budget k) (I5 spec config rows mapping base pins entry budget (k + 1))

theorem low_of' {base : BitVec 64} (c : BitVec 64) (hc : c.toNat < 2 ^ 20) (hb : base.toNat < 2 ^ 54) :
    (base + c).toNat < 2 ^ 55 := low_of c hc hb

end HeapV2StepCerts.Residue.Run
