import NativeAccess.PairNext
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
set_option Elab.async false
namespace NativeAccess.PairDispatch
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts ArmCertMemPipe
open NativeAccess.LdpBytes

theorem ldp_bytes_nextG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (profile : AccessProfile) (pins : ProfileAt profile x)
    (facts : PairTail.ByteFacts domain mapping m imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      PairNext.Packet spec config rows mapping m scope image loadBase base offset budget k
        [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] (fun _ => False) (PairTail.BytePay mapping Rt Rt2 imm7 Rn) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      PairTail.ByteFacts domain mapping m imm7 Rn f := by
    intro f hg _ hm
    simpa only [PairTail.ByteFacts,pairAddr,hg,hm] using facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → PairTail.BytePay mapping Rt Rt2 imm7 Rn f g → PairTail.BytePay mapping Rt Rt2 imm7 Rn x g := by
    intro f g hg hs hm hz ⟨pa,data,mp,bytes,gg,gs,gm,gz⟩
    refine ⟨pa,data,?_,?_,?_,gs.trans hs,gm.trans hm,gz.trans hz⟩
    · simpa only [pairAddr,hg] using mp
    · simpa only [hm] using bytes
    · simpa only [ArmCertMem.LdpEval.ldpPost,CryptoMem.MemCore.setGpr,hg] using gg
  exact PairNext.mem_nextG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] (fun s => s.regs._PC + 4#64)
      (PairTail.ByteFacts domain mapping m imm7 Rn) (fun _ => False) (PairTail.BytePay mapping Rt Rt2 imm7 Rn) (fun _ _ _ _ h => h)
      x inv xferX xferPay
      (PairTail.ldp_bytes_tailG real domain spec config rows mapping m sel K hK imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt
        dispatch noEret _ x profile pins)
      nextPlaced obligations

#print axioms ldp_bytes_nextG

theorem ldp_one_nextG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (profile : AccessProfile) (pins : ProfileAt profile x)
    (facts : PairTail.OneFacts mapping m imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      PairNext.Packet spec config rows mapping m scope image loadBase base offset budget k
        [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] (fun _ => False) (PairTail.OnePay mapping Rt Rt2 imm7 Rn) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      PairTail.OneFacts mapping m imm7 Rn f := by
    intro f hg _ hm
    simpa only [PairTail.OneFacts,pairAddr,hg,hm] using facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → PairTail.OnePay mapping Rt Rt2 imm7 Rn f g → PairTail.OnePay mapping Rt Rt2 imm7 Rn x g := by
    intro f g hg hs hm hz ⟨pa,data,mp,bytes,gg,gs,gm,gz⟩
    refine ⟨pa,data,?_,?_,?_,gs.trans hs,gm.trans hm,gz.trans hz⟩
    · simpa only [pairAddr,hg] using mp
    · simpa only [hm] using bytes
    · simpa only [ArmCertMem.LdpEval.ldpPost,CryptoMem.MemCore.setGpr,hg] using gg
  exact PairNext.mem_nextG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] (fun s => s.regs._PC + 4#64)
      (PairTail.OneFacts mapping m imm7 Rn) (fun _ => False) (PairTail.OnePay mapping Rt Rt2 imm7 Rn) (fun _ _ _ _ h => h)
      x inv xferX xferPay
      (PairTail.ldp_one_tailG real domain spec config rows mapping m sel K hK imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt
        dispatch noEret _ x profile pins)
      nextPlaced obligations

#print axioms ldp_one_nextG

theorem ldp_split_nextG (real : Type) [Sail.SailReal real]
    (domain : BitVec 64 → Prop) (spec : TopologyImageSpec (fun q => domain q.va))
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rn Rt Rt2 : BitVec 5)
    (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (profile : AccessProfile) (pins : ProfileAt profile x)
    (facts : PairTail.SplitFacts mapping m imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      PairNext.Packet spec config rows mapping m scope image loadBase base offset budget k
        [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] (fun _ => False) (PairTail.SplitPay mapping Rt Rt2 imm7 Rn) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      PairTail.SplitFacts mapping m imm7 Rn f := by
    intro f hg _ hm
    simpa only [PairTail.SplitFacts,pairAddr,hg,hm] using facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → PairTail.SplitPay mapping Rt Rt2 imm7 Rn f g → PairTail.SplitPay mapping Rt Rt2 imm7 Rn x g := by
    intro f g hg hs hm hz ⟨pa,data,mp,bytes,gg,gs,gm,gz⟩
    refine ⟨pa,data,?_,?_,?_,gs.trans hs,gm.trans hm,gz.trans hz⟩
    · simpa only [pairAddr,hg] using mp
    · simpa only [hm] using bytes
    · simpa only [ArmCertMem.LdpEval.ldpPost,CryptoMem.MemCore.setGpr,hg] using gg
  exact PairNext.mem_nextG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [(.x (RegBind.rk Rt),.drop),(.x (RegBind.rk Rt2),.drop)] (fun s => s.regs._PC + 4#64)
      (PairTail.SplitFacts mapping m imm7 Rn) (fun _ => False) (PairTail.SplitPay mapping Rt Rt2 imm7 Rn) (fun _ _ _ _ h => h)
      x inv xferX xferPay
      (PairTail.ldp_split_tailG real domain spec config rows mapping m sel K hK imm7 Rn Rt Rt2 hRn hRt hRt2 hRtt
        dispatch noEret _ x profile pins)
      nextPlaced obligations

#print axioms ldp_split_nextG

theorem stp_bytes_nextG (real : Type) [Sail.SailReal real]
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
    (facts : PairStoreTail.ByteFacts domain spec mapping m D imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      PairNext.Packet spec config rows mapping m scope image loadBase base offset budget k
        [] D (PairStoreTail.BytePay mapping Rt Rt2 imm7 Rn) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      PairStoreTail.ByteFacts domain spec mapping m D imm7 Rn f := by
    intro f hg _ hm
    simpa only [PairStoreTail.ByteFacts,pairAddr,hg,hm] using facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → PairStoreTail.BytePay mapping Rt Rt2 imm7 Rn f g → PairStoreTail.BytePay mapping Rt Rt2 imm7 Rn x g := by
    intro f g hg hs hm hz ⟨pa,calls,mp,mem,requests,payload,gg,gs,gz⟩
    refine ⟨pa,calls,?_,?_,?_,?_,gg.trans hg,gs.trans hs,gz.trans hz⟩
    · simpa only [pairAddr,hg] using mp
    · simpa only [hm] using mem
    · simpa only [pairAddr,hg] using requests
    · simpa only [ArmCertMem.StpEval.stpData,hg] using payload
  exact PairNext.mem_nextG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [] (fun s => s.regs._PC + 4#64)
      (PairStoreTail.ByteFacts domain spec mapping m D imm7 Rn) D (PairStoreTail.BytePay mapping Rt Rt2 imm7 Rn) codeD
      x inv xferX xferPay
      (PairStoreTail.stp_bytes_tailG real domain spec config rows mapping m sel K hK imm7 Rn Rt Rt2 hRn hRt hRt2
        dispatch noEret D x profile pins)
      nextPlaced obligations

#print axioms stp_bytes_nextG

theorem stp_one_nextG (real : Type) [Sail.SailReal real]
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
    (facts : PairStoreTail.OneFacts spec mapping m D imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      PairNext.Packet spec config rows mapping m scope image loadBase base offset budget k
        [] D (PairStoreTail.OnePay mapping Rt Rt2 imm7 Rn) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      PairStoreTail.OneFacts spec mapping m D imm7 Rn f := by
    intro f hg _ hm
    simpa only [PairStoreTail.OneFacts,pairAddr,hg,hm] using facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → PairStoreTail.OnePay mapping Rt Rt2 imm7 Rn f g → PairStoreTail.OnePay mapping Rt Rt2 imm7 Rn x g := by
    intro f g hg hs hm hz ⟨pa,calls,mp,mem,requests,payload,gg,gs,gz⟩
    refine ⟨pa,calls,?_,?_,?_,?_,gg.trans hg,gs.trans hs,gz.trans hz⟩
    · simpa only [pairAddr,hg] using mp
    · simpa only [hm] using mem
    · simpa only [pairAddr,hg] using requests
    · simpa only [ArmCertMem.StpEval.stpData,hg] using payload
  exact PairNext.mem_nextG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [] (fun s => s.regs._PC + 4#64)
      (PairStoreTail.OneFacts spec mapping m D imm7 Rn) D (PairStoreTail.OnePay mapping Rt Rt2 imm7 Rn) codeD
      x inv xferX xferPay
      (PairStoreTail.stp_one_tailG real domain spec config rows mapping m sel K hK imm7 Rn Rt Rt2 hRn hRt hRt2
        dispatch noEret D x profile pins)
      nextPlaced obligations

#print axioms stp_one_nextG

theorem stp_split_nextG (real : Type) [Sail.SailReal real]
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
    (facts : PairStoreTail.SplitFacts spec mapping m D imm7 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      PairNext.Packet spec config rows mapping m scope image loadBase base offset budget k
        [] D (PairStoreTail.SplitPay mapping Rt Rt2 imm7 Rn) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      PairStoreTail.SplitFacts spec mapping m D imm7 Rn f := by
    intro f hg _ hm
    simpa only [PairStoreTail.SplitFacts,pairAddr,hg,hm] using facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → PairStoreTail.SplitPay mapping Rt Rt2 imm7 Rn f g → PairStoreTail.SplitPay mapping Rt Rt2 imm7 Rn x g := by
    intro f g hg hs hm hz ⟨pa,calls,mp,mem,requests,payload,gg,gs,gz⟩
    refine ⟨pa,calls,?_,?_,?_,?_,gg.trans hg,gs.trans hs,gz.trans hz⟩
    · simpa only [pairAddr,hg] using mp
    · simpa only [hm] using mem
    · simpa only [pairAddr,hg] using requests
    · simpa only [ArmCertMem.StpEval.stpData,hg] using payload
  exact PairNext.mem_nextG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [] (fun s => s.regs._PC + 4#64)
      (PairStoreTail.SplitFacts spec mapping m D imm7 Rn) D (PairStoreTail.SplitPay mapping Rt Rt2 imm7 Rn) codeD
      x inv xferX xferPay
      (PairStoreTail.stp_split_tailG real domain spec config rows mapping m sel K hK imm7 Rn Rt Rt2 hRn hRt hRt2
        dispatch noEret D x profile pins)
      nextPlaced obligations

#print axioms stp_split_nextG

end NativeAccess.PairDispatch
