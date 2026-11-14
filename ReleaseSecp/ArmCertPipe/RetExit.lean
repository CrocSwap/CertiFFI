-- Actual fetched RET step with the return PC and architectural frames retained.
import ArmCertPipe.ChainInvG
import ArmCertPipe.RetFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft
open ArmBridge.Boundary ArmBridge.CruxGenGuarded.EntryActualFetch
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCertPipe.RetExit

/-- Conditional engine helper. The concrete program derives the invariant and
fetch obligations internally; this theorem does not admit a caller contract. -/
theorem step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat)
    (extra : Nat → NativeState → Prop) (k : Nat) (x : NativeState)
    (inv : ChainInvG spec config rows mapping consumer scope image loadBase base offset budget extra k x)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (rn : BitVec 5) (valid : rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (ArmBridge.CruxGenGuarded.EntryBodyRet.W rn) 31 12 == 879088#20) = false)
    (low : (x.regs.gpr[(GPRSummary.key rn.toNat).val]).toNat < 2 ^ 55)
    (fetch : FetchObligations spec config rows mapping (ArmBridge.CruxGenGuarded.EntryBodyRet.W rn) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      fin.regs.gpr = x.regs.gpr ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧
      fin.regs.PSTATE.N = x.regs.PSTATE.N ∧ fin.regs.PSTATE.Z = x.regs.PSTATE.Z ∧
      fin.regs.PSTATE.C = x.regs.PSTATE.C ∧ fin.regs.PSTATE.V = x.regs.PSTATE.V ∧
      fin.mem = x.mem ∧ ArmCertMemPipe.TLSFrame.tp fin = ArmCertMemPipe.TLSFrame.tp x ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs._PC = x.regs.gpr[(GPRSummary.key rn.toNat).val] := by
  have quiet : ArmCert.HookQuiet.V0.HookQuiet ((budget - (k + 1)) + 1) x := by
    have eq : budget - (k + 1) + 1 = budget - k := by omega
    rw [eq]
    exact inv.v2.v1.quiet
  exact BranchFrame.entry_branch_next_XTZ real spec config rows mapping
    (ArmBridge.CruxGenGuarded.EntryBodyRet.W rn) 94 x inv.v2.v1.pins
    (base + offset (k + 1)) (offset (k + 1))
    (fun fin => fin.regs._PC = x.regs.gpr[(GPRSummary.key rn.toNat).val])
    (RetFrame.tail_nzZ real x rn valid noEret low _) inv.v2.v1.gic inv.v2.v1.features
    inv.v2.v1.debug (budget - (k + 1)) quiet base (offset k) inv.v2.v1.pc page aligned rfl
    inv.v2.v1.current consumer inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
    inv.raw inv.noUpd fetch.queryOf fetch.rawOf fetch.vaOf fetch.mmio fetch.present fetch.perAcc fetch.code

#print axioms step
end ArmCertPipe.RetExit
