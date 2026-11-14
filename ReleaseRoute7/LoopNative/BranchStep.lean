import ArmCertPipe.ChainInvG
import TranslateStepV.BranchXZ
import NativeR14Ret.PcX

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.EntryActualFetch
open ArmCert.HookQuiet.V0 (HookQuiet)

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

namespace LoopNative.BranchStep
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts

/-- Join the value/vector frame and landing-PC tails on one actual Sail step.
Specialized class adapters construct BOTH tails internally from their actual
decoder/dispatch proofs; public loop cards never assume these callbacks. -/
theorem run (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (word : BitVec 32) (metadata : Int) (next : NativeState → BitVec 64)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (valueTail : TranslateStepV.BranchX.BranchTailNZZ real word metadata x (next x))
    (pcTail : NativeR14Ret.Pc.BranchTailP real word metadata x (next x))
    (nextPlaced : next x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping word x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds [] none x fin ∧
      fin.mem = x.mem ∧ fin.regs._Z = x.regs._Z ∧ fin.regs._PC = next x := by
  have quiet : HookQuiet ((budget - (k + 1)) + 1) x := by
    have index : budget - (k + 1) + 1 = budget - k := by omega
    rw [index]; exact inv.v2.v1.quiet
  obtain ⟨fin, step, gpr, sp, n, z, c, v, memory, vector⟩ :=
    TranslateStepV.BranchX.entry_branch_next_XZ real spec config rows mapping word metadata x inv.v2.v1.pins
      (next x) (offset (k + 1)) valueTail inv.v2.v1.gic inv.v2.v1.features inv.v2.v1.debug
      (budget - (k + 1)) quiet base (offset k) inv.v2.v1.pc page aligned nextPlaced
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch inv.raw inv.noUpd
      obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio obligations.present
      obligations.perAcc obligations.code
  have pc := NativeR14Ret.Pc.branch_fpcG real spec config rows mapping m scope image loadBase base offset budget extra
    k room page aligned word metadata next x inv pcTail obligations fin step
  exact ⟨fin, step, TranslateStepV.BranchX.vholds_nil gpr sp n z c v, memory, vector, pc⟩

#print axioms run

end LoopNative.BranchStep
