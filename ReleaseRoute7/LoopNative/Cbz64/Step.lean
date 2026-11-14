import LoopNative.Encoding
import LoopNative.BranchStep
import LoopNative.Cbz64.TailTaken
import LoopNative.Cbz64.TailNot
import LoopNative.Cbz64.PcTaken
import LoopNative.Cbz64.PcNot
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts
namespace LoopNative.Cbz64
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false

/-- Whole actual Sail step; both value and landing-PC tails are discharged. -/
theorem step_taken (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rt : BitVec 5) (imm19 : BitVec 19) (hrt : Rt.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (hc : condition Rt x)
    (hlow : (target imm19 x).toNat < 2 ^ 55)
    (nextPlaced : target imm19 x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (Dispatch.selected Rt imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds [] none x fin ∧
      fin.mem = x.mem ∧ fin.regs._Z = x.regs._Z ∧ fin.regs._PC = target imm19 x := by
  exact BranchStep.run real spec config rows mapping m scope image loadBase separated base offset budget extra
    k room page aligned (Dispatch.selected Rt imm19) 118 (target imm19) x inv
    (TailTaken.tail_z real x Rt imm19 hrt hc hlow (Encoding.Cbz64_noEret Rt imm19) _)
    (PcTaken.tail_p real x Rt imm19 hrt hc hlow (Encoding.Cbz64_noEret Rt imm19)) nextPlaced obligations

#print axioms step_taken

/-- Whole actual Sail step; both value and landing-PC tails are discharged. -/
theorem step_not_taken (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rt : BitVec 5) (imm19 : BitVec 19) (hrt : Rt.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (hc : ¬ condition Rt x)
    (nextPlaced : (fun s => s.regs._PC + 4#64) x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (Dispatch.selected Rt imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds [] none x fin ∧
      fin.mem = x.mem ∧ fin.regs._Z = x.regs._Z ∧ fin.regs._PC = (fun s => s.regs._PC + 4#64) x := by
  exact BranchStep.run real spec config rows mapping m scope image loadBase separated base offset budget extra
    k room page aligned (Dispatch.selected Rt imm19) 118 ((fun s => s.regs._PC + 4#64)) x inv
    (TailNot.tail_z real x Rt imm19 hrt hc (Encoding.Cbz64_noEret Rt imm19) _)
    (PcNot.tail_p real x Rt imm19 hrt hc (Encoding.Cbz64_noEret Rt imm19)) nextPlaced obligations

#print axioms step_not_taken

end LoopNative.Cbz64
