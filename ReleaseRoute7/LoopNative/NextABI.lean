import LoopNative.BranchFramed
import LoopNative.MemoryFrame
import LoopNative.Next
import LoopNative.Cbz64.Step
import LoopNative.Cbnz64.Step
import LoopNative.Cbz64.Rich
import LoopNative.Cbnz64.Rich
import LoopNative.LdrbU.Step
import LoopNative.StrbU.Step
import RtG.NextG
import ArmCertMemPipe.NextG2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ClosedChain ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.ChainInvV3
open HeapV2StepCerts HeapV2StepCerts.BranchStepV3 NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false


namespace LoopNative.Cbz64
theorem next_taken_abi (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rt : BitVec 5) (imm19 : BitVec 19) (hrt : Rt.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) k x)
    (hc : condition Rt x)
    (hlow : (target imm19 x).toNat < 2 ^ 55)
    (nextPlaced : target imm19 x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (Dispatch.selected Rt imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) (k + 1) fin ∧
      ArmCertValue.VHolds [] none x fin ∧
      fin.mem = x.mem ∧ fin.regs._Z = x.regs._Z ∧ fin.regs._PC = target imm19 x ∧ NativeEntry.Effects.Frame {} x.regs fin.regs := by
  have kept := BranchFrame.frameG real spec config rows mapping m scope image loadBase separated base offset budget
    (fun _ _ => True) k room page aligned (Dispatch.selected Rt imm19) 118 (target imm19) x inv
    (Framed.tail_taken real x Rt imm19 hrt hc hlow (Encoding.Cbz64_noEret Rt imm19)) nextPlaced obligations
  obtain ⟨fin, run, nextInv, holds, memory, vector, pc⟩ := next_taken real spec config rows mapping m scope image loadBase
    separated base offset budget k room page aligned Rt imm19 hrt x inv hc hlow nextPlaced obligations
  exact ⟨fin, run, nextInv, holds, memory, vector, pc, kept fin run⟩
#print axioms next_taken_abi
theorem next_not_taken_abi (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rt : BitVec 5) (imm19 : BitVec 19) (hrt : Rt.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) k x)
    (hc : ¬ condition Rt x)
    (nextPlaced : (fun s => s.regs._PC + 4#64) x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (Dispatch.selected Rt imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) (k + 1) fin ∧
      ArmCertValue.VHolds [] none x fin ∧
      fin.mem = x.mem ∧ fin.regs._Z = x.regs._Z ∧ fin.regs._PC = (fun s => s.regs._PC + 4#64) x ∧ NativeEntry.Effects.Frame {} x.regs fin.regs := by
  have kept := BranchFrame.frameG real spec config rows mapping m scope image loadBase separated base offset budget
    (fun _ _ => True) k room page aligned (Dispatch.selected Rt imm19) 118 ((fun s => s.regs._PC + 4#64)) x inv
    (Framed.tail_not real x Rt imm19 hrt hc (Encoding.Cbz64_noEret Rt imm19)) nextPlaced obligations
  obtain ⟨fin, run, nextInv, holds, memory, vector, pc⟩ := next_not_taken real spec config rows mapping m scope image loadBase
    separated base offset budget k room page aligned Rt imm19 hrt x inv hc nextPlaced obligations
  exact ⟨fin, run, nextInv, holds, memory, vector, pc, kept fin run⟩
#print axioms next_not_taken_abi
end LoopNative.Cbz64

namespace LoopNative.Cbnz64
theorem next_taken_abi (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rt : BitVec 5) (imm19 : BitVec 19) (hrt : Rt.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) k x)
    (hc : condition Rt x)
    (hlow : (target imm19 x).toNat < 2 ^ 55)
    (nextPlaced : target imm19 x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (Dispatch.selected Rt imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) (k + 1) fin ∧
      ArmCertValue.VHolds [] none x fin ∧
      fin.mem = x.mem ∧ fin.regs._Z = x.regs._Z ∧ fin.regs._PC = target imm19 x ∧ NativeEntry.Effects.Frame {} x.regs fin.regs := by
  have kept := BranchFrame.frameG real spec config rows mapping m scope image loadBase separated base offset budget
    (fun _ _ => True) k room page aligned (Dispatch.selected Rt imm19) 117 (target imm19) x inv
    (Framed.tail_taken real x Rt imm19 hrt hc hlow (Encoding.Cbnz64_noEret Rt imm19)) nextPlaced obligations
  obtain ⟨fin, run, nextInv, holds, memory, vector, pc⟩ := next_taken real spec config rows mapping m scope image loadBase
    separated base offset budget k room page aligned Rt imm19 hrt x inv hc hlow nextPlaced obligations
  exact ⟨fin, run, nextInv, holds, memory, vector, pc, kept fin run⟩
#print axioms next_taken_abi
theorem next_not_taken_abi (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (Rt : BitVec 5) (imm19 : BitVec 19) (hrt : Rt.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) k x)
    (hc : ¬ condition Rt x)
    (nextPlaced : (fun s => s.regs._PC + 4#64) x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (Dispatch.selected Rt imm19) x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) (k + 1) fin ∧
      ArmCertValue.VHolds [] none x fin ∧
      fin.mem = x.mem ∧ fin.regs._Z = x.regs._Z ∧ fin.regs._PC = (fun s => s.regs._PC + 4#64) x ∧ NativeEntry.Effects.Frame {} x.regs fin.regs := by
  have kept := BranchFrame.frameG real spec config rows mapping m scope image loadBase separated base offset budget
    (fun _ _ => True) k room page aligned (Dispatch.selected Rt imm19) 117 ((fun s => s.regs._PC + 4#64)) x inv
    (Framed.tail_not real x Rt imm19 hrt hc (Encoding.Cbnz64_noEret Rt imm19)) nextPlaced obligations
  obtain ⟨fin, run, nextInv, holds, memory, vector, pc⟩ := next_not_taken real spec config rows mapping m scope image loadBase
    separated base offset budget k room page aligned Rt imm19 hrt x inv hc nextPlaced obligations
  exact ⟨fin, run, nextInv, holds, memory, vector, pc, kept fin run⟩
#print axioms next_not_taken_abi
end LoopNative.Cbnz64

namespace LoopNative.LdrbU
open ArmCertMemPipe ArmCertMemPipe.LdrbU
theorem next_abi (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) k x)
    (facts : Facts spec config rows mapping m imm12 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.LdrbUoff.selected Rt Rn imm12) x)
    : ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) (k + 1) fin ∧
      RegBind.Holds [ (.x (RegBind.rk Rt), .drop)] x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → (fun _ => False) a)) ∧
      Pay mapping imm12 Rn Rt x fin ∧ SysEq2 x.regs fin.regs ∧ NativeEntry.Effects.Frame {} x.regs fin.regs := by
  let sel := NativeEntryBodyDispatch.LdrbUoff.selected Rt Rn imm12
  have dispatch : DispatchAt real sel
      (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 0#2) 633 := by
    intro pc t see
    exact NativeEntryBodyDispatch.LdrbUoff.dispatch_at real pc Rt Rn imm12 t (by simpa using see)
  have noEret := Encoding.LdrbU_noEret Rt Rn imm12
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec config rows mapping m imm12 Rn f := by
    intro f hg _ hm
    rw [Facts, addr_congr Rn imm12 hg, hm]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping imm12 Rn Rt f g → Pay mapping imm12 Rn Rt x g := by
    intro f g hg hs hm hz ⟨pa, data, mp, by8, gg, gs, gm, gz⟩
    refine ⟨pa, data, by rw [← addr_congr Rn imm12 hg]; exact mp, by rw [← hm]; exact by8, ?_, by rw [gs, hs],
      by rw [gm, hm], by rw [gz, hz]⟩
    rw [gg]; simp only [MemClass.LdrbU.post, CryptoMem.MemCore.setGpr, hg]
  have kept :=
    MemoryFrame.frameG real spec config rows mapping m scope image loadBase separated base offset budget (fun _ _ => True) k room page
      aligned sel {} 633 [(.x (RegBind.rk Rt), .drop)] (fun s => s.regs._PC + 4#64)
      (Facts spec config rows mapping m imm12 Rn) (fun _ => False) (Pay mapping imm12 Rn Rt) (fun _ _ _ _ h => h)
      x inv xferX xferPay (tailG real spec config rows mapping m sel 633 (by decide) imm12 Rn Rt hRn hRt dispatch noEret _ x)
      nextPlaced obligations
  obtain ⟨fin, run, nextInv, holds, written, pay, sys⟩ :=
    mem_nextG2 real spec config rows mapping m scope image loadBase separated base offset budget (fun _ _ => True) k room page
      aligned sel {} 633 [(.x (RegBind.rk Rt), .drop)] (fun s => s.regs._PC + 4#64)
      (Facts spec config rows mapping m imm12 Rn) (fun _ => False) (Pay mapping imm12 Rn Rt) (fun _ _ _ _ h => h)
      x inv xferX xferPay (tailG real spec config rows mapping m sel 633 (by decide) imm12 Rn Rt hRn hRt dispatch noEret _ x)
      nextPlaced obligations (fun _ _ => True.intro)
  exact ⟨fin, run, nextInv, holds, written, pay, sys, kept fin run⟩

#print axioms next_abi
end LoopNative.LdrbU

namespace LoopNative.StrbU
open ArmCertMemPipe ArmCertMemPipe.StrbU
theorem next_abi (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) k x)
    (facts : Facts spec mapping m D imm12 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.StrbUoff.selected Rt Rn imm12) x)
    : ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget (fun _ _ => True) (k + 1) fin ∧
      RegBind.Holds [] x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)) ∧
      Pay mapping imm12 Rn Rt x fin ∧ SysEq2 x.regs fin.regs ∧ NativeEntry.Effects.Frame {} x.regs fin.regs := by
  let sel := NativeEntryBodyDispatch.StrbUoff.selected Rt Rn imm12
  have dispatch : DispatchAt real sel
      (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 0#2) 651 := by
    intro pc t see
    exact NativeEntryBodyDispatch.StrbUoff.dispatch_at real pc Rt Rn imm12 t (by simpa using see)
  have noEret := Encoding.StrbU_noEret Rt Rn imm12
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec mapping m D imm12 Rn f := by
    intro f hg _ _
    rw [Facts, addr_congr Rn imm12 hg]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping imm12 Rn Rt f g → Pay mapping imm12 Rn Rt x g := by
    intro f g hg hs hm hz ⟨pa, mp, gm, gg, gs, gz⟩
    refine ⟨pa, by rw [← addr_congr Rn imm12 hg]; exact mp, ?_, by rw [gg, hg], by rw [gs, hs], by rw [gz, hz]⟩
    rw [gm, hm]; simp only [MemClass.StrbU.stData, hg]
  have kept :=
    MemoryFrame.frameG real spec config rows mapping m scope image loadBase separated base offset budget (fun _ _ => True) k room page
      aligned sel {} 651 [] (fun s => s.regs._PC + 4#64)
      (Facts spec mapping m D imm12 Rn) D (Pay mapping imm12 Rn Rt) codeD
      x inv xferX xferPay (tailG real spec config rows mapping m sel 651 (by decide) imm12 Rn Rt hRn hRt dispatch noEret D x)
      nextPlaced obligations
  obtain ⟨fin, run, nextInv, holds, written, pay, sys⟩ :=
    mem_nextG2 real spec config rows mapping m scope image loadBase separated base offset budget (fun _ _ => True) k room page
      aligned sel {} 651 [] (fun s => s.regs._PC + 4#64)
      (Facts spec mapping m D imm12 Rn) D (Pay mapping imm12 Rn Rt) codeD
      x inv xferX xferPay (tailG real spec config rows mapping m sel 651 (by decide) imm12 Rn Rt hRn hRt dispatch noEret D x)
      nextPlaced obligations (fun _ _ => True.intro)
  exact ⟨fin, run, nextInv, holds, written, pay, sys, kept fin run⟩

#print axioms next_abi
end LoopNative.StrbU
