-- Route 7 unit 3: CurrentInv branch steps for CBZ X / CBNZ X (branchEventStep) and RET (branchEventExit).
import DefaultRuntimeBranchRoute
import DefaultRuntimeBranchTails
import DefaultHeapCbzTail
import RuntimeFrames.Routes
import RuntimeFrames.BranchTail
import Route7Cbnz.Tail
import Route7Cbz.TailFrame
import Route7Cbnz.TailFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCertWalk ArmCert.Translate.Model
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Route7Steps
attribute [local instance 10] Classical.propDecidable

/-! No-ERET facts: word bit 30 (extracted bit 18) is 0 for CBZ/CBNZ X and 1 in the ERET pattern; RET as loops' RetABI. -/
theorem noEret_cbz (Rt : BitVec 5) (imm19 : BitVec 19) :
    (Sail.BitVec.extractLsb (ArmBridge.CruxGenGuarded.EntryBodyCbz.W Rt imm19) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (ArmBridge.CruxGenGuarded.EntryBodyCbz.W Rt imm19) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v : BitVec 20 => v.getLsbD 18) h
    simp only [ArmBridge.CruxGenGuarded.EntryBodyCbz.W, NativeEntryBodyDispatch.Cbz.selected, NativeEntryBodyDispatch.Cbz.word,
      Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at bit
    simp at bit
  simpa using ne

theorem noEret_cbnz (Rt : BitVec 5) (imm19 : BitVec 19) :
    (Sail.BitVec.extractLsb (Route7Cbnz.Tail.W Rt imm19) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (Route7Cbnz.Tail.W Rt imm19) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v : BitVec 20 => v.getLsbD 18) h
    simp only [Route7Cbnz.Tail.W, Route7Cbnz.Dispatch.selected, Route7Cbnz.Dispatch.word,
      Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at bit
    simp at bit
  simpa using ne

theorem noEret_ret (Rn : BitVec 5) :
    (Sail.BitVec.extractLsb (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v : BitVec 20 => v.getLsbD 11) h
    simp only [ArmBridge.CruxGenGuarded.EntryBodyRet.W, NativeEntryBodyDispatch.Ret.selected, NativeEntryBodyDispatch.Ret.word,
      Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at bit
    simp at bit
  simpa using ne

variable (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
include separated room page aligned

/-- CBZ X over CurrentInv: successor PC = nextPC (taken target or PC+4 by the CBZ condition). -/
theorem cbz64 (Rt : BitVec 5) (imm19 : BitVec 19) (x : NativeState)
    (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hlow : (x.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) (nextPC : BitVec 64)
    (hnext : (if Crypto.CruxCbz.cbzC 1#1 Rt x then x.regs._PC + sign_extend (imm19 ++ 0#2) 64 else x.regs._PC + 4#64) = nextPC)
    (nextPlaced : nextPC = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (ArmBridge.CruxGenGuarded.EntryBodyCbz.W Rt imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ NativeEntry.Effects.Frame {} x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have kept := ReleaseProfile.RuntimeFrames.branchEventStep_frame real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ArmBridge.CruxGenGuarded.EntryBodyCbz.W Rt imm19) 118
      (fun _ => nextPC) x inv
      (ReleaseProfile.DefaultHeapCbzTail.tail_at real x Rt imm19 (noEret_cbz Rt imm19) hlow nextPC hnext)
      (Route7Cbz.TailFrame.tail_at real x Rt imm19 (noEret_cbz Rt imm19) hlow nextPC hnext)
      nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, _, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ArmBridge.CruxGenGuarded.EntryBodyCbz.W Rt imm19) 118
      (fun _ => nextPC) x inv
      (ReleaseProfile.DefaultHeapCbzTail.tail_at real x Rt imm19 (noEret_cbz Rt imm19) hlow nextPC hnext)
      nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice⟩

/-- CBNZ X over CurrentInv: successor PC = nextPC (taken target or PC+4 by cbzCond with op = 1). -/
theorem cbnz64 (Rt : BitVec 5) (imm19 : BitVec 19) (x : NativeState)
    (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hlow : (x.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) (nextPC : BitVec 64)
    (hnext : (if ReleaseProfile.HeapCbzAction.cbzCond x 1#1 1#1 Rt then x.regs._PC + sign_extend (imm19 ++ 0#2) 64
      else x.regs._PC + 4#64) = nextPC)
    (nextPlaced : nextPC = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (Route7Cbnz.Tail.W Rt imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ NativeEntry.Effects.Frame {} x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have kept := ReleaseProfile.RuntimeFrames.branchEventStep_frame real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (Route7Cbnz.Tail.W Rt imm19) 117
      (fun _ => nextPC) x inv
      (Route7Cbnz.Tail.tail_at real x Rt imm19 (noEret_cbnz Rt imm19) hlow nextPC hnext)
      (Route7Cbnz.TailFrame.tail_at real x Rt imm19 (noEret_cbnz Rt imm19) hlow nextPC hnext)
      nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, _, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (Route7Cbnz.Tail.W Rt imm19) 117
      (fun _ => nextPC) x inv
      (Route7Cbnz.Tail.tail_at real x Rt imm19 (noEret_cbnz Rt imm19) hlow nextPC hnext)
      nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice⟩

/-- RET Xn over CurrentInv (route exit): PC = Xn. -/
theorem ret (Rn : BitVec 5) (hRn : Rn.toNat < 31) (x : NativeState)
    (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hlow : (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (ob : FetchObligations spec config rows mapping (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._PC = x.regs.gpr[(GPRSummary.key Rn.toNat).val] ∧
      ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ NativeEntry.Effects.Frame {} x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 := by
  have kept := ReleaseProfile.RuntimeFrames.branchEventExit_frame real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) 94
      (fun _ => x.regs.gpr[(GPRSummary.key Rn.toNat).val]) x inv
      (ReleaseProfile.DefaultRuntimeBranch.RichRet.tail_at real x Rn hRn (noEret_ret Rn) hlow _ rfl)
      (ReleaseProfile.RuntimeFrames.Branch.RichRet.tail_at real x Rn hRn (noEret_ret Rn) hlow _ rfl)
      nodup ob
  obtain ⟨fin, run, pc, holds, mem, sys, z, dit, _, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventExit real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) 94
      (fun _ => x.regs.gpr[(GPRSummary.key Rn.toNat).val]) x inv
      (ReleaseProfile.DefaultRuntimeBranch.RichRet.tail_at real x Rn hRn (noEret_ret Rn) hlow _ rfl)
      nodup ob
  exact ⟨fin, run, pc, holds, mem, sys, z, dit, kept fin run, choice⟩

end Route7Steps

#print axioms Route7Steps.cbz64
#print axioms Route7Steps.cbnz64
#print axioms Route7Steps.ret
