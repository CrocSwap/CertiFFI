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
theorem noEret (Rd Rn : BitVec 5) (imm12 : BitVec 12) :
    (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v : BitVec 20 => v.getLsbD 18) h
    simp only [NativeEntryBodyDispatch.AddImm64.selected, NativeEntryBodyDispatch.AddImm64.word, Sail.BitVec.extractLsb, BitVec.extractLsb,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at bit
    simp at bit
  simpa using ne

theorem next (real : Type) [Sail.SailReal real]
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
      fin.regs._PC = x.regs._PC + 4#64 := by
  obtain ⟨fin, run, nextInv, holds, memory, _⟩ := RtG.nextG_class real spec config rows mapping m scope image loadBase
    separated base offset budget (fun _ _ => True) k room page aligned (NativeEntryBodyDispatch.AddImm64.selected Rd Rn imm12)
    NativeEntryBodyAdapters.AddImm64.writes 18 (fun s => s.regs._PC + 4#64) (upd Rd Rn imm12) none x inv
    (tailX real x Rd Rn imm12 rd rn (noEret Rd Rn imm12)) nextPlaced obligations (fun _ _ _ _ => True.intro)
  exact ⟨fin, run, nextInv, holds, memory, nextInv.v2.v1.pc.trans nextPlaced.symm⟩
#print axioms noEret
#print axioms next
end LoopNative.AddImm64

namespace LoopNative.SubImm64
theorem noEret (Rd Rn : BitVec 5) (imm12 : BitVec 12) :
    (Sail.BitVec.extractLsb (LoopNative.SubImm64.Dispatch.selected Rd Rn imm12) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (LoopNative.SubImm64.Dispatch.selected Rd Rn imm12) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v : BitVec 20 => v.getLsbD 14) h
    simp only [LoopNative.SubImm64.Dispatch.selected, LoopNative.SubImm64.Dispatch.word, Sail.BitVec.extractLsb, BitVec.extractLsb,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at bit
    simp at bit
  simpa using ne

theorem next (real : Type) [Sail.SailReal real]
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
      fin.regs._PC = x.regs._PC + 4#64 := by
  obtain ⟨fin, run, nextInv, holds, memory, _⟩ := RtG.nextG_class real spec config rows mapping m scope image loadBase
    separated base offset budget (fun _ _ => True) k room page aligned (LoopNative.SubImm64.Dispatch.selected Rd Rn imm12)
    Adapter.writes 20 (fun s => s.regs._PC + 4#64) (upd Rd Rn imm12) none x inv
    (tailX real x Rd Rn imm12 rd rn (noEret Rd Rn imm12)) nextPlaced obligations (fun _ _ _ _ => True.intro)
  exact ⟨fin, run, nextInv, holds, memory, nextInv.v2.v1.pc.trans nextPlaced.symm⟩
#print axioms noEret
#print axioms next
end LoopNative.SubImm64

namespace LoopNative.Mov64
theorem noEret (Rd Rm : BitVec 5) :
    (Sail.BitVec.extractLsb (NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) 31 12 == 879088#20) = false := by
  have ne : Sail.BitVec.extractLsb (NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm) 31 12 ≠ 879088#20 := by
    intro h
    have bit := congrArg (fun v : BitVec 20 => v.getLsbD 18) h
    simp only [NativeEntryBodyDispatch.OrrMov64.selected, NativeEntryBodyDispatch.OrrMov64.word, Sail.BitVec.extractLsb, BitVec.extractLsb,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at bit
    simp at bit
  simpa using ne

theorem next (real : Type) [Sail.SailReal real]
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
      fin.regs._PC = x.regs._PC + 4#64 := by
  obtain ⟨fin, run, nextInv, holds, memory, _⟩ := RtG.nextG_class real spec config rows mapping m scope image loadBase
    separated base offset budget (fun _ _ => True) k room page aligned (NativeEntryBodyDispatch.OrrMov64.selected Rd 0#6 Rm)
    NativeEntryBodyAdapters.OrrMov64.writes 55 (fun s => s.regs._PC + 4#64) (upd Rd Rm) none x inv
    (tailX real x Rd Rm rd rm (noEret Rd Rm)) nextPlaced obligations (fun _ _ _ _ => True.intro)
  exact ⟨fin, run, nextInv, holds, memory, nextInv.v2.v1.pc.trans nextPlaced.symm⟩
#print axioms noEret
#print axioms next
end LoopNative.Mov64
