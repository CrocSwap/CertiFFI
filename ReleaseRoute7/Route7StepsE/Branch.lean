-- Route 7 CT0 (loops): event-exposing copies of Route7Steps.Branch wrappers (same proofs; the step
-- EvShape that the originals discard is returned as the last conjunct).
import Route7Steps.Branch
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
variable (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
include separated room page aligned

/-- CBZ X over CurrentInv: successor PC = nextPC (taken target or PC+4 by the CBZ condition).  Event-exposing copy (loops CT0): also returns the step EvShape (no data records).-/
theorem cbz64E (Rt : BitVec 5) (imm19 : BitVec 19) (x : NativeState)
    (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hlow : (x.regs._PC + sign_extend (imm19 ++ 0#2) 64).toNat < 2 ^ 55) (nextPC : BitVec 64)
    (hnext : (if Crypto.CruxCbz.cbzC 1#1 Rt x then x.regs._PC + sign_extend (imm19 ++ 0#2) 64 else x.regs._PC + 4#64) = nextPC)
    (nextPlaced : nextPC = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (ArmBridge.CruxGenGuarded.EntryBodyCbz.W Rt imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ NativeEntry.Effects.Frame {} x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 ∧
      StepEvents.EvShape spec mapping [] x fin := by
  have kept := ReleaseProfile.RuntimeFrames.branchEventStep_frame real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ArmBridge.CruxGenGuarded.EntryBodyCbz.W Rt imm19) 118
      (fun _ => nextPC) x inv
      (ReleaseProfile.DefaultHeapCbzTail.tail_at real x Rt imm19 (noEret_cbz Rt imm19) hlow nextPC hnext)
      (Route7Cbz.TailFrame.tail_at real x Rt imm19 (noEret_cbz Rt imm19) hlow nextPC hnext)
      nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ArmBridge.CruxGenGuarded.EntryBodyCbz.W Rt imm19) 118
      (fun _ => nextPC) x inv
      (ReleaseProfile.DefaultHeapCbzTail.tail_at real x Rt imm19 (noEret_cbz Rt imm19) hlow nextPC hnext)
      nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice, ev⟩

/-- CBNZ X over CurrentInv: successor PC = nextPC (taken target or PC+4 by cbzCond with op = 1).  Event-exposing copy (loops CT0): also returns the step EvShape (no data records).-/
theorem cbnz64E (Rt : BitVec 5) (imm19 : BitVec 19) (x : NativeState)
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
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ NativeEntry.Effects.Frame {} x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 ∧
      StepEvents.EvShape spec mapping [] x fin := by
  have kept := ReleaseProfile.RuntimeFrames.branchEventStep_frame real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (Route7Cbnz.Tail.W Rt imm19) 117
      (fun _ => nextPC) x inv
      (Route7Cbnz.Tail.tail_at real x Rt imm19 (noEret_cbnz Rt imm19) hlow nextPC hnext)
      (Route7Cbnz.TailFrame.tail_at real x Rt imm19 (noEret_cbnz Rt imm19) hlow nextPC hnext)
      nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (Route7Cbnz.Tail.W Rt imm19) 117
      (fun _ => nextPC) x inv
      (Route7Cbnz.Tail.tail_at real x Rt imm19 (noEret_cbnz Rt imm19) hlow nextPC hnext)
      nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice, ev⟩

/-- RET Xn over CurrentInv (route exit): PC = Xn.  Event-exposing copy (loops CT0): also returns the step EvShape (no data records).-/
theorem retE (Rn : BitVec 5) (hRn : Rn.toNat < 31) (x : NativeState)
    (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hlow : (x.regs.gpr[(GPRSummary.key Rn.toNat).val]).toNat < 2 ^ 55)
    (ob : FetchObligations spec config rows mapping (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ fin.regs._PC = x.regs.gpr[(GPRSummary.key Rn.toNat).val] ∧
      ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ NativeEntry.Effects.Frame {} x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 ∧
      StepEvents.EvShape spec mapping [] x fin := by
  have kept := ReleaseProfile.RuntimeFrames.branchEventExit_frame real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) 94
      (fun _ => x.regs.gpr[(GPRSummary.key Rn.toNat).val]) x inv
      (ReleaseProfile.DefaultRuntimeBranch.RichRet.tail_at real x Rn hRn (noEret_ret Rn) hlow _ rfl)
      (ReleaseProfile.RuntimeFrames.Branch.RichRet.tail_at real x Rn hRn (noEret_ret Rn) hlow _ rfl)
      nodup ob
  obtain ⟨fin, run, pc, holds, mem, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventExit real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ArmBridge.CruxGenGuarded.EntryBodyRet.W Rn) 94
      (fun _ => x.regs.gpr[(GPRSummary.key Rn.toNat).val]) x inv
      (ReleaseProfile.DefaultRuntimeBranch.RichRet.tail_at real x Rn hRn (noEret_ret Rn) hlow _ rfl)
      nodup ob
  exact ⟨fin, run, pc, holds, mem, sys, z, dit, kept fin run, choice, ev⟩

end Route7Steps
#print axioms Route7Steps.cbz64E
#print axioms Route7Steps.cbnz64E
#print axioms Route7Steps.retE
