-- Route 7 CT0 (loops): event-exposing copies of Route7Move.Steps wrappers (CMP / ADD shifted / B.cond;
-- same proofs, the discarded step EvShape is returned as the last conjunct).
import Route7Move.Steps
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCertWalk ArmCert.Translate.Model
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option Elab.async false

namespace Route7Move
theorem subsShift64ZRdE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rn Rm : BitVec 5) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.SubsShift64ZRd.selected Rn 0#6 Rm) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.SubsShift64ZRd.selected Rn 0#6 Rm) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds [] (some (ArmCertValue.R14.SubsShift64ZRd.fl Rn Rm)) x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      NativeEntry.Effects.Frame NativeEntryBodyFlag.SubsShift64ZRd.writes x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 ∧
      StepEvents.EvShape spec mapping [] x fin := by
  have kept := ReleaseProfile.RuntimeFrames.classEventStep_frame real spec config rows mapping m scope image loadBase
    separated base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.SubsShift64ZRd.selected Rn 0#6 Rm)
    NativeEntryBodyFlag.SubsShift64ZRd.writes 17 [] (some (ArmCertValue.R14.SubsShift64ZRd.fl Rn Rm))
    (fun s => s.regs._PC + 4#64) x inv (ArmCertValue.R14.SubsShift64ZRd.tailX real x Rn 0#6 Rm rn rm rfl noEret)
    (ReleaseProfile.DefaultRuntimeScalarChoice.tail_SubsShift64ZRd real x Rn 0#6 Rm rn rm noEret) nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.SubsShift64ZRd.selected Rn 0#6 Rm)
      NativeEntryBodyFlag.SubsShift64ZRd.writes 17 [] (some (ArmCertValue.R14.SubsShift64ZRd.fl Rn Rm))
      (fun s => s.regs._PC + 4#64) x inv (ArmCertValue.R14.SubsShift64ZRd.tailX real x Rn 0#6 Rm rn rm rfl noEret)
      (ReleaseProfile.DefaultRuntimeScalarChoice.tail_SubsShift64ZRd real x Rn 0#6 Rm rn rm noEret) nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice, ev⟩

theorem addShift64E (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rd Rn Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31)
    (noEret : (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds (ArmCertValue.R14.AddShift64.upd Rd Rn Rm) none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      NativeEntry.Effects.Frame NativeEntryBodyAdapters.AddShift64.writes x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 ∧
      StepEvents.EvShape spec mapping [] x fin := by
  have kept := ReleaseProfile.RuntimeFrames.classEventStep_frame real spec config rows mapping m scope image loadBase
    separated base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm)
    NativeEntryBodyAdapters.AddShift64.writes 14 (ArmCertValue.R14.AddShift64.upd Rd Rn Rm) none
    (fun s => s.regs._PC + 4#64) x inv (ArmCertValue.R14.AddShift64.tailX real x Rd Rn 0#6 Rm rd rn rm rfl noEret ⟨⟩)
    (ReleaseProfile.DefaultRuntimeScalarChoice.tail_AddShift64 real x Rd Rn 0#6 Rm rd rn rm ⟨⟩ noEret) nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.AddShift64.selected Rd Rn 0#6 Rm)
      NativeEntryBodyAdapters.AddShift64.writes 14 (ArmCertValue.R14.AddShift64.upd Rd Rn Rm) none
      (fun s => s.regs._PC + 4#64) x inv (ArmCertValue.R14.AddShift64.tailX real x Rd Rn 0#6 Rm rd rn rm rfl noEret ⟨⟩)
      (ReleaseProfile.DefaultRuntimeScalarChoice.tail_AddShift64 real x Rd Rn 0#6 Rm rd rn rm ⟨⟩ noEret) nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice, ev⟩

attribute [local instance 10] Classical.propDecidable in

theorem bcondE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (cond : BitVec 4) (imm19 : BitVec 19)
    (noEret : (Sail.BitVec.extractLsb (ReleaseProfile.DefaultRuntimeBcondEventTail.W cond imm19) 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (hlow : (x.regs._PC + sign_extend (imm19 +++ 0#2) 64).toNat < 2 ^ 55) (nextPC : BitVec 64)
    (hnext : (if Crypto.BcondCore.bcondC cond x.regs then x.regs._PC + sign_extend (imm19 +++ 0#2) 64
      else x.regs._PC + 4#64) = nextPC)
    (nextPlaced : nextPC = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (ReleaseProfile.DefaultRuntimeBcondEventTail.W cond imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds [] none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ NativeEntry.Effects.Frame {} x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 ∧
      StepEvents.EvShape spec mapping [] x fin := by
  have kept := ReleaseProfile.RuntimeFrames.branchEventStep_frame real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ReleaseProfile.DefaultRuntimeBcondEventTail.W cond imm19) 69
      (fun _ => nextPC) x inv
      (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x cond imm19 noEret hlow nextPC hnext)
      (ReleaseProfile.Route7BcondTailFrame.tail_at real x cond imm19 noEret hlow nextPC hnext)
      nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.branchEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (ReleaseProfile.DefaultRuntimeBcondEventTail.W cond imm19) 69
      (fun _ => nextPC) x inv
      (ReleaseProfile.DefaultRuntimeBcondEventTail.tail_at real x cond imm19 noEret hlow nextPC hnext)
      nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice, ev⟩

/-! ## CMP X0, X1 → B.EQ / B.LO -/

end Route7Move
#print axioms Route7Move.subsShift64ZRdE
#print axioms Route7Move.addShift64E
#print axioms Route7Move.bcondE
