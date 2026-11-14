-- (runtime14 P3): the final-RET route over ChainInvG. branch_vholdsG needs next x = base + offset (k+1),
-- which a function's last step (return to the caller's LR) cannot meet; StepFact only needs success + VHolds +
-- MemVHolds, so the RET route takes the next PC = X30 with next offset (X30 - base).
import ArmCertPipe.ChainInvG
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
namespace NativeR14Ret
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.ChainInvV3 HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts

theorem ret_vholdsG (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (K : Int) (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (tail : TranslateStepV.BranchX.BranchTailNZ real w K x (next x))
    (obligations : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, g, sp, n, z, c, v, mem⟩ :=
    TranslateStepV.BranchX.entry_branch_next_X real spec config rows mapping w K x inv.v2.v1.pins (next x)
      (next x - base) tail inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (by rw [BitVec.add_comm, BitVec.sub_add_cancel])
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio
      obligations.present obligations.perAcc obligations.code
  exact ⟨fin, run, TranslateStepV.BranchX.vholds_nil g sp n z c v, mem⟩

#print axioms ret_vholdsG
end NativeR14Ret
