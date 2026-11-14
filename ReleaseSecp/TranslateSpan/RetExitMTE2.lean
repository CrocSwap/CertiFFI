-- Actual fetched RET with branch pins independent of the MTE2 feature bit.
import TranslateSpan.RetFrameMTE2
import ArmCertPipe.ChainInvG

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace TranslateSpan.RetExitMTE2

theorem step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (consumer : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat) (x : NativeState)
    (inv : ChainInv spec config rows base offset budget k x)
    (closed : ClosedMembershipAt spec config rows mapping consumer (beforeFetchState x))
    (placed : MemReloc.ImageOn scope image x loadBase mapping)
    (branch : BranchMTE2.Pins x) (raw : RawImageAt spec.imageRows x.mem)
    (noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
      NoUpdateRows {spec.params with haft := hostHAFT x.regs} acc spec.imageRows = true)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (rn : BitVec 5) (valid : rn.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (EntryBodyRet.W rn) 31 12 == 879088#20) = false)
    (low : (x.regs.gpr[(GPRSummary.key rn.toNat).val]).toNat < 2 ^ 55)
    (fetch : FetchObligations spec config rows mapping (EntryBodyRet.W rn) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      fin.regs.gpr = x.regs.gpr ∧ fin.regs.SP_EL0 = x.regs.SP_EL0 ∧
      fin.regs.PSTATE.N = x.regs.PSTATE.N ∧ fin.regs.PSTATE.Z = x.regs.PSTATE.Z ∧
      fin.regs.PSTATE.C = x.regs.PSTATE.C ∧ fin.regs.PSTATE.V = x.regs.PSTATE.V ∧
      fin.mem = x.mem ∧ ArmCertMemPipe.TLSFrame.tp fin = ArmCertMemPipe.TLSFrame.tp x ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs._PC = x.regs.gpr[(GPRSummary.key rn.toNat).val] := by
  have quiet : ArmCert.HookQuiet.V0.HookQuiet ((budget - (k + 1)) + 1) x := by
    have eq : budget - (k + 1) + 1 = budget - k := by omega
    rw [eq]
    exact inv.quiet
  exact BranchFrameMTE2.entry_branch_next_XTZ real spec config rows mapping
    (EntryBodyRet.W rn) 94 x inv.pins (base + offset (k + 1)) (offset (k + 1))
    (fun fin => fin.regs._PC = x.regs.gpr[(GPRSummary.key rn.toNat).val])
    (RetFrameMTE2.tail_nzZ real x rn valid noEret low _) inv.gic inv.features inv.debug
    (budget - (k + 1)) quiet base (offset k) inv.pc page aligned rfl inv.current consumer closed
    scope image loadBase placed separated branch raw noUpd fetch.queryOf fetch.rawOf fetch.vaOf
    fetch.mmio fetch.present fetch.perAcc fetch.code

#print axioms step
end TranslateSpan.RetExitMTE2
