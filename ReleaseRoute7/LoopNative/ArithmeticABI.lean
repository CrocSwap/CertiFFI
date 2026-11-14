import LoopNative.ClassFrame
import LoopNative.Arithmetic
import LoopNative.Mov64
import LoopNative.AddImm64
import LoopNative.SubImm64.Value
import RtG.ClassNextG
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false


namespace LoopNative.AddImm64
theorem next_abi (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rd Rn : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) k x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) (k + 1) fin ∧
      ArmCertValue.VHolds (upd Rd Rn imm12) none x fin ∧ fin.mem = x.mem ∧
      fin.regs._PC = x.regs._PC + 4#64 ∧ NativeEntry.Effects.Frame {} x.regs fin.regs := by
  have kept := ClassFrame.frameG real spec config rows mapping
    m scope image loadBase separated base offset budget (fun _ _ => True) k room page aligned
    (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12) NativeEntryBodyAdapters.AddImm64.writes 18 (fun s => s.regs._PC + 4#64)
    (upd Rd Rn imm12) none x inv (tailX real x Rd Rn imm12 rd rn (noEret Rd Rn imm12)) nextPlaced obligations
  obtain ⟨fin, run, nextInv, holds, memory, pc⟩ := next real spec config rows mapping m scope image loadBase
    separated base offset budget k room page aligned Rd Rn imm12 rd rn x inv nextPlaced obligations
  exact ⟨fin, run, nextInv, holds, memory, pc, kept fin run⟩
#print axioms next_abi
end LoopNative.AddImm64

namespace LoopNative.SubImm64
theorem next_abi (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rd Rn : BitVec 5) (imm12 : BitVec 12) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) k x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (LoopNative.SubImm64.Dispatch.selected Rd Rn imm12) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) (k + 1) fin ∧
      ArmCertValue.VHolds (upd Rd Rn imm12) none x fin ∧ fin.mem = x.mem ∧
      fin.regs._PC = x.regs._PC + 4#64 ∧ NativeEntry.Effects.Frame {} x.regs fin.regs := by
  have kept := ClassFrame.frameG real spec config rows mapping
    m scope image loadBase separated base offset budget (fun _ _ => True) k room page aligned
    (LoopNative.SubImm64.Dispatch.selected Rd Rn imm12) Adapter.writes 20 (fun s => s.regs._PC + 4#64)
    (upd Rd Rn imm12) none x inv (tailX real x Rd Rn imm12 rd rn (noEret Rd Rn imm12)) nextPlaced obligations
  obtain ⟨fin, run, nextInv, holds, memory, pc⟩ := next real spec config rows mapping m scope image loadBase
    separated base offset budget k room page aligned Rd Rn imm12 rd rn x inv nextPlaced obligations
  exact ⟨fin, run, nextInv, holds, memory, pc, kept fin run⟩
#print axioms next_abi
end LoopNative.SubImm64

namespace LoopNative.Mov64
theorem next_abi (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rd Rm : BitVec 5) (rd : Rd.toNat < 31) (rm : Rm.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) k x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) (k + 1) fin ∧
      ArmCertValue.VHolds (upd Rd Rm) none x fin ∧ fin.mem = x.mem ∧
      fin.regs._PC = x.regs._PC + 4#64 ∧ NativeEntry.Effects.Frame {} x.regs fin.regs := by
  have kept := ClassFrame.frameG real spec config rows mapping
    m scope image loadBase separated base offset budget (fun _ _ => True) k room page aligned
    (NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) NativeEntryBodyAdapters.OrrMov64.writes 55 (fun s => s.regs._PC + 4#64)
    (upd Rd Rm) none x inv (tailX real x Rd Rm rd rm (noEret Rd Rm)) nextPlaced obligations
  obtain ⟨fin, run, nextInv, holds, memory, pc⟩ := next real spec config rows mapping m scope image loadBase
    separated base offset budget k room page aligned Rd Rm rd rm x inv nextPlaced obligations
  exact ⟨fin, run, nextInv, holds, memory, pc, kept fin run⟩
#print axioms next_abi
end LoopNative.Mov64
