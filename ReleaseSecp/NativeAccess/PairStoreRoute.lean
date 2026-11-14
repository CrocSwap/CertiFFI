import NativeAccess.PairStoreTail
import ArmCertMemPipe.RouteG
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
set_option Elab.async false
namespace NativeAccess.PairStoreRoute
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts ArmCertMemPipe
open NativeAccess.PairStoreTail NativeAccess.LdpBytes

/-- Actual modelStep with internally transported fetch/action facts. Conditional
on the current ChainInvG and fetch obligations; no future-state run premise. -/
theorem stp_bytes_routeG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (profile : AccessProfile) (pins : ProfileAt profile x)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (facts : ByteFacts domain spec mapping m D imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      RegBind.Holds [] x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)) ∧
      BytePay mapping Rt Rt2 imm7 Rn x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      ByteFacts domain spec mapping m D imm7 Rn f := by
    intro f hg _ hm
    simpa only [ByteFacts,pairAddr,hg,hm] using facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → BytePay mapping Rt Rt2 imm7 Rn f g → BytePay mapping Rt Rt2 imm7 Rn x g := by
    intro f g hg hs hm hz ⟨pa,calls,mp,mem,requests,payload,gg,gs,gz⟩
    refine ⟨pa,calls,?_,?_,?_,?_,gg.trans hg,gs.trans hs,gz.trans hz⟩
    · simpa only [pairAddr,hg] using mp
    · simpa only [hm] using mem
    · simpa only [pairAddr,hg] using requests
    · simpa only [ArmCertMem.StpEval.stpData,hg] using payload
  obtain ⟨fin,run,holds,writes,pay⟩ :=
    mem_routeG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [] (fun s => s.regs._PC + 4#64)
      (ByteFacts domain spec mapping m D imm7 Rn) D (BytePay mapping Rt Rt2 imm7 Rn) codeD
      x inv xferX xferPay
      (stp_bytes_tailG real domain spec config rows mapping m sel K hK imm7 Rn Rt Rt2 hRn hRt hRt2
        dispatch noEret D x profile pins)
      nextPlaced obligations
  exact ⟨fin,run,holds,writes,pay⟩

#print axioms stp_bytes_routeG

/-- Actual modelStep with internally transported fetch/action facts. Conditional
on the current ChainInvG and fetch obligations; no future-state run premise. -/
theorem stp_one_routeG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (profile : AccessProfile) (pins : ProfileAt profile x)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (facts : OneFacts spec mapping m D imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      RegBind.Holds [] x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)) ∧
      OnePay mapping Rt Rt2 imm7 Rn x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      OneFacts spec mapping m D imm7 Rn f := by
    intro f hg _ hm
    simpa only [OneFacts,pairAddr,hg,hm] using facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → OnePay mapping Rt Rt2 imm7 Rn f g → OnePay mapping Rt Rt2 imm7 Rn x g := by
    intro f g hg hs hm hz ⟨pa,calls,mp,mem,requests,payload,gg,gs,gz⟩
    refine ⟨pa,calls,?_,?_,?_,?_,gg.trans hg,gs.trans hs,gz.trans hz⟩
    · simpa only [pairAddr,hg] using mp
    · simpa only [hm] using mem
    · simpa only [pairAddr,hg] using requests
    · simpa only [ArmCertMem.StpEval.stpData,hg] using payload
  obtain ⟨fin,run,holds,writes,pay⟩ :=
    mem_routeG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [] (fun s => s.regs._PC + 4#64)
      (OneFacts spec mapping m D imm7 Rn) D (OnePay mapping Rt Rt2 imm7 Rn) codeD
      x inv xferX xferPay
      (stp_one_tailG real domain spec config rows mapping m sel K hK imm7 Rn Rt Rt2 hRn hRt hRt2
        dispatch noEret D x profile pins)
      nextPlaced obligations
  exact ⟨fin,run,holds,writes,pay⟩

#print axioms stp_one_routeG

/-- Actual modelStep with internally transported fetch/action facts. Conditional
on the current ChainInvG and fetch obligations; no future-state run premise. -/
theorem stp_split_routeG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (profile : AccessProfile) (pins : ProfileAt profile x)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (facts : SplitFacts spec mapping m D imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      RegBind.Holds [] x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)) ∧
      SplitPay mapping Rt Rt2 imm7 Rn x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      SplitFacts spec mapping m D imm7 Rn f := by
    intro f hg _ hm
    simpa only [SplitFacts,pairAddr,hg,hm] using facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → SplitPay mapping Rt Rt2 imm7 Rn f g → SplitPay mapping Rt Rt2 imm7 Rn x g := by
    intro f g hg hs hm hz ⟨pa,calls,mp,mem,requests,payload,gg,gs,gz⟩
    refine ⟨pa,calls,?_,?_,?_,?_,gg.trans hg,gs.trans hs,gz.trans hz⟩
    · simpa only [pairAddr,hg] using mp
    · simpa only [hm] using mem
    · simpa only [pairAddr,hg] using requests
    · simpa only [ArmCertMem.StpEval.stpData,hg] using payload
  obtain ⟨fin,run,holds,writes,pay⟩ :=
    mem_routeG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [] (fun s => s.regs._PC + 4#64)
      (SplitFacts spec mapping m D imm7 Rn) D (SplitPay mapping Rt Rt2 imm7 Rn) codeD
      x inv xferX xferPay
      (stp_split_tailG real domain spec config rows mapping m sel K hK imm7 Rn Rt Rt2 hRn hRt hRt2
        dispatch noEret D x profile pins)
      nextPlaced obligations
  exact ⟨fin,run,holds,writes,pay⟩

#print axioms stp_split_routeG

end NativeAccess.PairStoreRoute
