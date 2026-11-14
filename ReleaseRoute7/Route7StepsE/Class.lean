-- Route 7 CT0 (loops): event-exposing copies of Route7Steps.Class wrappers (same proofs; the step
-- EvShape that the originals discard is returned as the last conjunct).
import Route7Steps.Class
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
theorem addImm64E (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rd Rn : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds (ArmCertValue.AddImm64.upd Rd Rn imm12) none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      NativeEntry.Effects.Frame NativeEntryBodyAdapters.AddImm64.writes x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 ∧
      StepEvents.EvShape spec mapping [] x fin := by
  have kept := ReleaseProfile.RuntimeFrames.classEventStep_frame real spec config rows mapping m scope image loadBase
    separated base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12) NativeEntryBodyAdapters.AddImm64.writes 18 (ArmCertValue.AddImm64.upd Rd Rn imm12) none
    (fun s => s.regs._PC + 4#64) x inv (ArmCertValue.AddImm64.tailX real x Rd Rn imm12 rd rn (noEret_add Rd Rn imm12) ⟨⟩) (ReleaseProfile.DefaultRuntimeScalarChoice.tail_AddImm64 real x Rd Rn imm12 rd rn ⟨⟩ (noEret_add Rd Rn imm12)) nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12) NativeEntryBodyAdapters.AddImm64.writes 18 (ArmCertValue.AddImm64.upd Rd Rn imm12) none
      (fun s => s.regs._PC + 4#64) x inv (ArmCertValue.AddImm64.tailX real x Rd Rn imm12 rd rn (noEret_add Rd Rn imm12) ⟨⟩) (ReleaseProfile.DefaultRuntimeScalarChoice.tail_AddImm64 real x Rd Rn imm12 rd rn ⟨⟩ (noEret_add Rd Rn imm12)) nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice, ev⟩

theorem subImm64E (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rd Rn : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (Route7Sub.Dispatch.selected Rd Rn imm12) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds (Route7Sub.upd Rd Rn imm12) none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      NativeEntry.Effects.Frame Route7Sub.Adapter.writes x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 ∧
      StepEvents.EvShape spec mapping [] x fin := by
  have kept := ReleaseProfile.RuntimeFrames.classEventStep_frame real spec config rows mapping m scope image loadBase
    separated base offset budget k catalogue room page aligned (Route7Sub.Dispatch.selected Rd Rn imm12) Route7Sub.Adapter.writes 20 (Route7Sub.upd Rd Rn imm12) none
    (fun s => s.regs._PC + 4#64) x inv (Route7Sub.tailX real x Rd Rn imm12 rd rn (noEret_sub Rd Rn imm12)) (Route7Sub.TailChoice.tail_SubImm64 real x Rd Rn imm12 rd rn ⟨⟩ (noEret_sub Rd Rn imm12)) nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (Route7Sub.Dispatch.selected Rd Rn imm12) Route7Sub.Adapter.writes 20 (Route7Sub.upd Rd Rn imm12) none
      (fun s => s.regs._PC + 4#64) x inv (Route7Sub.tailX real x Rd Rn imm12 rd rn (noEret_sub Rd Rn imm12)) (Route7Sub.TailChoice.tail_SubImm64 real x Rd Rn imm12 rd rn ⟨⟩ (noEret_sub Rd Rn imm12)) nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice, ev⟩

theorem mov64E (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rd Rm : BitVec 5) (rd : Rd.toNat < 31) (rm : Rm.toNat < 31)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (ob : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds (Route7Mov.upd Rd Rm) none x fin ∧ fin.mem = x.mem ∧ SysEq2 x.regs fin.regs ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      NativeEntry.Effects.Frame NativeEntryBodyAdapters.OrrMov64.writes x.regs fin.regs ∧ NativeMteTagCheck.ChoiceDelta x fin 0 ∧
      StepEvents.EvShape spec mapping [] x fin := by
  have kept := ReleaseProfile.RuntimeFrames.classEventStep_frame real spec config rows mapping m scope image loadBase
    separated base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) NativeEntryBodyAdapters.OrrMov64.writes 55 (Route7Mov.upd Rd Rm) none
    (fun s => s.regs._PC + 4#64) x inv (Route7Mov.tailX real x Rd Rm rd rm (noEret_mov Rd Rm)) (ReleaseProfile.DefaultRuntimeScalarChoice.tail_OrrMov64 real x Rd 0#6 Rm rd rm rfl ⟨⟩ (noEret_mov Rd Rm)) nodup nextPlaced ob
  obtain ⟨fin, run, inv', holds, mem, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.classEventStep real spec config rows mapping m scope image loadBase separated
      base offset budget k catalogue room page aligned (NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) NativeEntryBodyAdapters.OrrMov64.writes 55 (Route7Mov.upd Rd Rm) none
      (fun s => s.regs._PC + 4#64) x inv (Route7Mov.tailX real x Rd Rm rd rm (noEret_mov Rd Rm)) (ReleaseProfile.DefaultRuntimeScalarChoice.tail_OrrMov64 real x Rd 0#6 Rm rd rm rfl ⟨⟩ (noEret_mov Rd Rm)) nodup nextPlaced ob
  exact ⟨fin, run, inv', holds, mem, sys, z, dit, kept fin run, choice, ev⟩

end Route7Steps
#print axioms Route7Steps.addImm64E
#print axioms Route7Steps.subImm64E
#print axioms Route7Steps.mov64E
