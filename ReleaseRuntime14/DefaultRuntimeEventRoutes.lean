-- Actual decoded default memory routes with full-step event and choice results.
import DefaultMemRoute
import DefaultRuntimeEventTails
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000
namespace ReleaseProfile.DefaultLdrU64
open ArmCertMemPipe ArmCertMemPipe.LdrU64
private theorem addr_congr {f x : NativeState} (Rn : BitVec 5) (imm12 : BitVec 12)
    (hg : f.regs.gpr = x.regs.gpr) :
    MemClass.LdrU64.addr f Rn imm12 = MemClass.LdrU64.addr x Rn imm12 := by
  simp only [MemClass.LdrU64.addr, hg]

open ArmCertMemPipe ArmCertMemPipe.LdrU64
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

#check "CURRENT_DECL LdrU64.routeE"
theorem routeE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 3#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (facts : Facts spec config rows mapping m imm12 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultRuntime.MemoryStep spec config rows mapping m scope image loadBase base offset budget k catalogue 1
        [(.x (RegBind.rk Rt), .drop)] (fun _ => False) (Pay mapping imm12 Rn Rt)
        (DataRecs.dataRecs spec (MemClass.LdrU64.addr x Rn imm12) false 8) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec config rows mapping m imm12 Rn f := by
    intro f hg _ hm
    rw [Facts, addr_congr Rn imm12 hg, hm]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping imm12 Rn Rt f g → Pay mapping imm12 Rn Rt x g := by
    intro f g hg hs hm hz ⟨pa, data, mp, by8, gg, gs, gm, gz⟩
    refine ⟨pa, data, by rw [← addr_congr Rn imm12 hg]; exact mp, by rw [← hm]; exact by8, ?_, by rw [gs, hs],
      by rw [gm, hm], by rw [gz, hz]⟩
    rw [gg]; simp only [MemClass.LdrU64.post, CryptoMem.MemCore.setGpr, hg]
  obtain ⟨fin, run, current, regs, footprint, pay, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.mem_route real spec config rows mapping m scope image loadBase separated base offset budget k catalogue 1 room page
      aligned sel {} K [(.x (RegBind.rk Rt), .drop)] (fun s => s.regs._PC + 4#64)
      (Facts spec config rows mapping m imm12 Rn) (fun _ => False) (Pay mapping imm12 Rn Rt) (fun f => DataRecs.dataRecs spec (MemClass.LdrU64.addr f Rn imm12) false 8) nodup (fun _ _ _ _ h => h)
      x inv allowed (fun f hg hs => by simp only [MemClass.LdrU64.addr, hg, hs]) xferX xferPay (ReleaseProfile.DefaultLdrU64.tailGE real spec config rows mapping m sel K hK imm12 Rn Rt hRn hRt dispatch noEret _ catalogue x)
      nextPlaced obligations rfl
  exact ⟨fin, run, ⟨current, regs, footprint, pay, sys, z, dit, ev, choice⟩⟩

#print axioms routeE
end ReleaseProfile.DefaultLdrU64

namespace ReleaseProfile.DefaultLdrU64Sp
open ArmCertMemPipe ArmCertMemPipe.LdrU64Sp
private theorem addr_congr {f x : NativeState} (imm12 : BitVec 12)
    (hs : f.regs.SP_EL0 = x.regs.SP_EL0) :
    MemClass.LdrU64Sp.addr f imm12 = MemClass.LdrU64Sp.addr x imm12 := by
  simp only [MemClass.LdrU64Sp.addr, hs]

open ArmCertMemPipe ArmCertMemPipe.LdrU64Sp
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

#check "CURRENT_DECL LdrU64Sp.routeE"
theorem routeE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rt : BitVec 5) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 1#2 3#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (facts : Facts spec config rows mapping m imm12 x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultRuntime.MemoryStep spec config rows mapping m scope image loadBase base offset budget k catalogue 1
        [(.x (RegBind.rk Rt), .drop)] (fun _ => False) (Pay mapping imm12 Rt)
        (DataRecs.dataRecs spec (MemClass.LdrU64Sp.addr x imm12) false 8) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec config rows mapping m imm12 f := by
    intro f hg hs hm
    rw [Facts, addr_congr imm12 hs, hm, hs]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping imm12 Rt f g → Pay mapping imm12 Rt x g := by
    intro f g hg hs hm hz ⟨pa, data, mp, by8, gg, gs, gm, gz⟩
    refine ⟨pa, data, by rw [← addr_congr imm12 hs]; exact mp, by rw [← hm]; exact by8, ?_, by rw [gs, hs],
      by rw [gm, hm], by rw [gz, hz]⟩
    rw [gg]; simp only [MemClass.LdrU64Sp.post, CryptoMem.MemCore.setGpr, hg]
  obtain ⟨fin, run, current, regs, footprint, pay, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.mem_route real spec config rows mapping m scope image loadBase separated base offset budget k catalogue 1 room page
      aligned sel {} K [(.x (RegBind.rk Rt), .drop)] (fun s => s.regs._PC + 4#64)
      (Facts spec config rows mapping m imm12) (fun _ => False) (Pay mapping imm12 Rt) (fun f => DataRecs.dataRecs spec (MemClass.LdrU64Sp.addr f imm12) false 8) nodup (fun _ _ _ _ h => h)
      x inv allowed (fun f hg hs => by simp only [MemClass.LdrU64Sp.addr, hg, hs]) xferX xferPay (ReleaseProfile.DefaultLdrU64Sp.tailGE real spec config rows mapping m sel K hK imm12 Rt hRt dispatch noEret _ catalogue x)
      nextPlaced obligations rfl
  exact ⟨fin, run, ⟨current, regs, footprint, pay, sys, z, dit, ev, choice⟩⟩

#print axioms routeE
end ReleaseProfile.DefaultLdrU64Sp

namespace ReleaseProfile.DefaultLdrbU
open ArmCertMemPipe ArmCertMemPipe.LdrbU
private theorem addr_congr {f x : NativeState} (Rn : BitVec 5) (imm12 : BitVec 12)
    (hg : f.regs.gpr = x.regs.gpr) :
    MemClass.LdrbU.addr f Rn imm12 = MemClass.LdrbU.addr x Rn imm12 := by
  simp only [MemClass.LdrbU.addr, hg]

open ArmCertMemPipe ArmCertMemPipe.LdrbU
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

#check "CURRENT_DECL LdrbU.routeE"
theorem routeE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 0#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (facts : Facts spec config rows mapping m imm12 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultRuntime.MemoryStep spec config rows mapping m scope image loadBase base offset budget k catalogue 1
        [(.x (RegBind.rk Rt), .drop)] (fun _ => False) (Pay mapping imm12 Rn Rt)
        (DataRecs.dataRecs spec (MemClass.LdrbU.addr x Rn imm12) false 1) x fin := by
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
  obtain ⟨fin, run, current, regs, footprint, pay, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.mem_route real spec config rows mapping m scope image loadBase separated base offset budget k catalogue 1 room page
      aligned sel {} K [(.x (RegBind.rk Rt), .drop)] (fun s => s.regs._PC + 4#64)
      (Facts spec config rows mapping m imm12 Rn) (fun _ => False) (Pay mapping imm12 Rn Rt) (fun f => DataRecs.dataRecs spec (MemClass.LdrbU.addr f Rn imm12) false 1) nodup (fun _ _ _ _ h => h)
      x inv allowed (fun f hg hs => by simp only [MemClass.LdrbU.addr, hg, hs]) xferX xferPay (ReleaseProfile.DefaultLdrbU.tailGE real spec config rows mapping m sel K hK imm12 Rn Rt hRn hRt dispatch noEret _ catalogue x)
      nextPlaced obligations rfl
  exact ⟨fin, run, ⟨current, regs, footprint, pay, sys, z, dit, ev, choice⟩⟩

#print axioms routeE
end ReleaseProfile.DefaultLdrbU

namespace ReleaseProfile.DefaultLdpPost
open ArmCertMemPipe ArmCertMemPipe.LdpPost
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

#check "CURRENT_DECL LdpPost.routeE"
theorem routeE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (c : Int) (hc : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 c)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt 31#5 Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (facts : Facts spec mapping m x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultRuntime.MemoryStep spec config rows mapping m scope image loadBase base offset budget k catalogue 1
        [(.x (RegBind.rk Rt), .drop), (.x (RegBind.rk Rt2), .drop), (.sp, .set .sp c)] (fun _ => False) (Pay mapping Rt Rt2 imm7)
        (DataRecs.dataRecs spec (x.regs.SP_EL0) false 16) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec mapping m f := by
    intro f _ hs hm
    rw [Facts, hs, hm]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping Rt Rt2 imm7 f g → Pay mapping Rt Rt2 imm7 x g := by
    intro f g hg hs hm hz ⟨pa, data, mp, by16, gg, gs, gm, gz⟩
    refine ⟨pa, data, by rw [← hs]; exact mp, by rw [← hm]; exact by16, ?_, by rw [gs, hs], by rw [gm, hm], by rw [gz, hz]⟩
    rw [gg]; simp only [MemClass.LdpPost.ldpPost, MemClass.LdpPost.spWrite_eq, CryptoMem.MemCore.setGpr, hg]
  obtain ⟨fin, run, current, regs, footprint, pay, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.mem_route real spec config rows mapping m scope image loadBase separated base offset budget k catalogue 1 room page
      aligned sel {} K [(.x (RegBind.rk Rt), .drop), (.x (RegBind.rk Rt2), .drop), (.sp, .set .sp c)]
      (fun s => s.regs._PC + 4#64) (Facts spec mapping m) (fun _ => False) (Pay mapping Rt Rt2 imm7) (fun f => DataRecs.dataRecs spec (f.regs.SP_EL0) false 16) nodup (fun _ _ _ _ h => h)
      x inv allowed (fun f hg hs => by simp only [hs]) xferX xferPay
      (ReleaseProfile.DefaultLdpPost.tailGE real spec config rows mapping m sel K hK imm7 Rt Rt2 hRt hRt2 hRtt c hc dispatch noEret _ catalogue x)
      nextPlaced obligations rfl
  exact ⟨fin, run, ⟨current, regs, footprint, pay, sys, z, dit, ev, choice⟩⟩

#print axioms routeE
end ReleaseProfile.DefaultLdpPost

namespace ReleaseProfile.DefaultStrU32
open ArmCertMemPipe ArmCertMemPipe.StrU32
private theorem addr_congr {f x : NativeState} (Rn : BitVec 5) (imm12 : BitVec 12)
    (hg : f.regs.gpr = x.regs.gpr) :
    MemClass.StrU32.addr f Rn imm12 = MemClass.StrU32.addr x Rn imm12 := by
  simp only [MemClass.StrU32.addr, hg]

open ArmCertMemPipe ArmCertMemPipe.StrU32
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

#check "CURRENT_DECL StrU32.routeE"
theorem routeE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (facts : Facts spec mapping m D imm12 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultRuntime.MemoryStep spec config rows mapping m scope image loadBase base offset budget k catalogue 1
        [] D (Pay mapping imm12 Rn Rt)
        (DataRecs.dataRecs spec (MemClass.StrU32.addr x Rn imm12) true 4) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec mapping m D imm12 Rn f := by
    intro f hg _ _
    rw [Facts, addr_congr Rn imm12 hg]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping imm12 Rn Rt f g → Pay mapping imm12 Rn Rt x g := by
    intro f g hg hs hm hz ⟨pa, mp, gm, gg, gs, gz⟩
    refine ⟨pa, by rw [← addr_congr Rn imm12 hg]; exact mp, ?_, by rw [gg, hg], by rw [gs, hs], by rw [gz, hz]⟩
    rw [gm, hm]; simp only [MemClass.StrU32.stData, hg]
  obtain ⟨fin, run, current, regs, footprint, pay, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.mem_route real spec config rows mapping m scope image loadBase separated base offset budget k catalogue 1 room page
      aligned sel {} K [] (fun s => s.regs._PC + 4#64)
      (Facts spec mapping m D imm12 Rn) D (Pay mapping imm12 Rn Rt) (fun f => DataRecs.dataRecs spec (MemClass.StrU32.addr f Rn imm12) true 4) nodup codeD
      x inv allowed (fun f hg hs => by simp only [MemClass.StrU32.addr, hg, hs]) xferX xferPay (ReleaseProfile.DefaultStrU32.tailGE real spec config rows mapping m sel K hK imm12 Rn Rt hRn hRt dispatch noEret D catalogue x)
      nextPlaced obligations rfl
  exact ⟨fin, run, ⟨current, regs, footprint, pay, sys, z, dit, ev, choice⟩⟩

#print axioms routeE
end ReleaseProfile.DefaultStrU32

namespace ReleaseProfile.DefaultStrU64Sp
open ArmCertMemPipe ArmCertMemPipe.StrU64Sp
private theorem addr_congr {f x : NativeState} (imm12 : BitVec 12)
    (hs : f.regs.SP_EL0 = x.regs.SP_EL0) :
    MemClass.StrU64Sp.addr f imm12 = MemClass.StrU64Sp.addr x imm12 := by
  simp only [MemClass.StrU64Sp.addr, hs]

open ArmCertMemPipe ArmCertMemPipe.StrU64Sp
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

#check "CURRENT_DECL StrU64Sp.routeE"
theorem routeE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rt : BitVec 5) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 0#2 3#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (facts : Facts spec mapping m D imm12 x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultRuntime.MemoryStep spec config rows mapping m scope image loadBase base offset budget k catalogue 1
        [] D (Pay mapping imm12 Rt)
        (DataRecs.dataRecs spec (MemClass.StrU64Sp.addr x imm12) true 8) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec mapping m D imm12 f := by
    intro f hg hs _
    rw [Facts, addr_congr imm12 hs, hs]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping imm12 Rt f g → Pay mapping imm12 Rt x g := by
    intro f g hg hs hm hz ⟨pa, mp, gm, gg, gs, gz⟩
    refine ⟨pa, by rw [← addr_congr imm12 hs]; exact mp, ?_, by rw [gg, hg], by rw [gs, hs], by rw [gz, hz]⟩
    rw [gm, hm]; simp only [MemClass.StrU64Sp.stData, hg]
  obtain ⟨fin, run, current, regs, footprint, pay, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.mem_route real spec config rows mapping m scope image loadBase separated base offset budget k catalogue 1 room page
      aligned sel {} K [] (fun s => s.regs._PC + 4#64)
      (Facts spec mapping m D imm12) D (Pay mapping imm12 Rt) (fun f => DataRecs.dataRecs spec (MemClass.StrU64Sp.addr f imm12) true 8) nodup codeD
      x inv allowed (fun f hg hs => by simp only [MemClass.StrU64Sp.addr, hg, hs]) xferX xferPay (ReleaseProfile.DefaultStrU64Sp.tailGE real spec config rows mapping m sel K hK imm12 Rt hRt dispatch noEret D catalogue x)
      nextPlaced obligations rfl
  exact ⟨fin, run, ⟨current, regs, footprint, pay, sys, z, dit, ev, choice⟩⟩

#print axioms routeE
end ReleaseProfile.DefaultStrU64Sp

namespace ReleaseProfile.DefaultStrbU
open ArmCertMemPipe ArmCertMemPipe.StrbU
private theorem addr_congr {f x : NativeState} (Rn : BitVec 5) (imm12 : BitVec 12)
    (hg : f.regs.gpr = x.regs.gpr) :
    MemClass.StrbU.addr f Rn imm12 = MemClass.StrbU.addr x Rn imm12 := by
  simp only [MemClass.StrbU.addr, hg]

open ArmCertMemPipe ArmCertMemPipe.StrbU
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

#check "CURRENT_DECL StrbU.routeE"
theorem routeE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 0#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (facts : Facts spec mapping m D imm12 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultRuntime.MemoryStep spec config rows mapping m scope image loadBase base offset budget k catalogue 1
        [] D (Pay mapping imm12 Rn Rt)
        (DataRecs.dataRecs spec (MemClass.StrbU.addr x Rn imm12) true 1) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec mapping m D imm12 Rn f := by
    intro f hg _ _
    rw [Facts, addr_congr Rn imm12 hg]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping imm12 Rn Rt f g → Pay mapping imm12 Rn Rt x g := by
    intro f g hg hs hm hz ⟨pa, mp, gm, gg, gs, gz⟩
    refine ⟨pa, by rw [← addr_congr Rn imm12 hg]; exact mp, ?_, by rw [gg, hg], by rw [gs, hs], by rw [gz, hz]⟩
    rw [gm, hm]; simp only [MemClass.StrbU.stData, hg]
  obtain ⟨fin, run, current, regs, footprint, pay, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.mem_route real spec config rows mapping m scope image loadBase separated base offset budget k catalogue 1 room page
      aligned sel {} K [] (fun s => s.regs._PC + 4#64)
      (Facts spec mapping m D imm12 Rn) D (Pay mapping imm12 Rn Rt) (fun f => DataRecs.dataRecs spec (MemClass.StrbU.addr f Rn imm12) true 1) nodup codeD
      x inv allowed (fun f hg hs => by simp only [MemClass.StrbU.addr, hg, hs]) xferX xferPay (ReleaseProfile.DefaultStrbU.tailGE real spec config rows mapping m sel K hK imm12 Rn Rt hRn hRt dispatch noEret D catalogue x)
      nextPlaced obligations rfl
  exact ⟨fin, run, ⟨current, regs, footprint, pay, sys, z, dit, ev, choice⟩⟩

#print axioms routeE
end ReleaseProfile.DefaultStrbU

namespace ReleaseProfile.DefaultStpPre
open ArmCertMemPipe ArmCertMemPipe.StpPre
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

#check "CURRENT_DECL StpPre.routeE"
theorem routeE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (c : Int) (hc : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 c)
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt 31#5 Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (facts : Facts spec mapping m D imm7 x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultRuntime.MemoryStep spec config rows mapping m scope image loadBase base offset budget k catalogue 1
        [(.sp, .set .sp c)] D (Pay mapping Rt Rt2 imm7)
        (DataRecs.dataRecs spec (MemClass.StpPre.ldpAddr x imm7) true 16) x fin := by
  have aEq : ∀ f : NativeState, f.regs.SP_EL0 = x.regs.SP_EL0 → MemClass.StpPre.ldpAddr f imm7 = MemClass.StpPre.ldpAddr x imm7 := by
    intro f hs; simp only [MemClass.StpPre.ldpAddr, hs]
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec mapping m D imm7 f := by
    intro f _ hs _
    rw [Facts, aEq f hs, hs]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping Rt Rt2 imm7 f g → Pay mapping Rt Rt2 imm7 x g := by
    intro f g hg hs hm hz ⟨pa, mp, gm, gg, gs, gz⟩
    refine ⟨pa, by rw [← aEq f hs]; exact mp, ?_, by rw [gg, hg], by rw [gs, aEq f hs], by rw [gz, hz]⟩
    rw [gm, hm]; simp only [MemClass.StpPre.stpData, hg]
  obtain ⟨fin, run, current, regs, footprint, pay, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.mem_route real spec config rows mapping m scope image loadBase separated base offset budget k catalogue 1 room page
      aligned sel {} K [(.sp, .set .sp c)] (fun s => s.regs._PC + 4#64)
      (Facts spec mapping m D imm7) D (Pay mapping Rt Rt2 imm7) (fun f => DataRecs.dataRecs spec (MemClass.StpPre.ldpAddr f imm7) true 16) nodup codeD
      x inv allowed (fun f hg hs => by simp only [MemClass.StpPre.ldpAddr, hg, hs]) xferX xferPay (ReleaseProfile.DefaultStpPre.tailGE real spec config rows mapping m sel K hK imm7 Rt Rt2 hRt hRt2 c hc dispatch noEret D catalogue x)
      nextPlaced obligations rfl
  exact ⟨fin, run, ⟨current, regs, footprint, pay, sys, z, dit, ev, choice⟩⟩

#print axioms routeE
end ReleaseProfile.DefaultStpPre

namespace ReleaseProfile.DefaultLdrU32
open ArmCertMemPipe ArmCertMemPipe.LdrU32
private theorem addr_congr {f x : NativeState} (Rn : BitVec 5) (imm12 : BitVec 12)
    (hg : f.regs.gpr = x.regs.gpr) :
    MemClass.LdrU32.addr f Rn imm12 = MemClass.LdrU32.addr x Rn imm12 := by
  simp only [MemClass.LdrU32.addr, hg]

open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

#check "CURRENT_DECL routeE"
theorem routeE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (facts : Facts spec config rows mapping m imm12 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultRuntime.MemoryStep spec config rows mapping m scope image loadBase base offset budget k catalogue 1
        [(.x (RegBind.rk Rt), .drop)] (fun _ => False) (Pay mapping imm12 Rn Rt)
        (DataRecs.dataRecs spec (MemClass.LdrU32.addr x Rn imm12) false 4) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec config rows mapping m imm12 Rn f := by
    intro f hg _ hm
    rw [Facts, addr_congr Rn imm12 hg, hm]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping imm12 Rn Rt f g → Pay mapping imm12 Rn Rt x g := by
    intro f g hg hs hm hz ⟨pa, data, mp, by8, gg, gs, gm, gz⟩
    refine ⟨pa, data, by rw [← addr_congr Rn imm12 hg]; exact mp, by rw [← hm]; exact by8, ?_, by rw [gs, hs],
      by rw [gm, hm], by rw [gz, hz]⟩
    rw [gg]; simp only [MemClass.LdrU32.post, CryptoMem.MemCore.setGpr, hg]
  obtain ⟨fin, run, current, regs, footprint, pay, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.mem_route real spec config rows mapping m scope image loadBase separated base offset budget k catalogue 1 room page
      aligned sel {} K [(.x (RegBind.rk Rt), .drop)] (fun s => s.regs._PC + 4#64)
      (Facts spec config rows mapping m imm12 Rn) (fun _ => False) (Pay mapping imm12 Rn Rt) (fun f => DataRecs.dataRecs spec (MemClass.LdrU32.addr f Rn imm12) false 4) nodup (fun _ _ _ _ h => h)
      x inv allowed (fun f hg hs => by simp only [MemClass.LdrU32.addr, hg, hs]) xferX xferPay (ReleaseProfile.DefaultLdrU32.tailGE real spec config rows mapping m sel K hK imm12 Rn Rt hRn hRt dispatch noEret _ catalogue x)
      nextPlaced obligations rfl
  exact ⟨fin, run, ⟨current, regs, footprint, pay, sys, z, dit, ev, choice⟩⟩

#print axioms routeE
end ReleaseProfile.DefaultLdrU32

namespace ReleaseProfile.DefaultLdpOff
open ArmCertMemPipe ArmCertMemPipe.LdpOff
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

#check "CURRENT_DECL LdpOff.routeE"
theorem routeE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (facts : Facts spec mapping m imm7 x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultRuntime.MemoryStep spec config rows mapping m scope image loadBase base offset budget k catalogue 1
        [(.x (RegBind.rk Rt), .drop), (.x (RegBind.rk Rt2), .drop)] (fun _ => False) (Pay mapping Rt Rt2 imm7)
        (DataRecs.dataRecs spec (ArmCertMem.LdpEval.ldpAddr x imm7) false 16) x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec mapping m imm7 f := by
    intro f _ hs hm
    rw [Facts, show ArmCertMem.LdpEval.ldpAddr f imm7 = ArmCertMem.LdpEval.ldpAddr x imm7 by simp only [ArmCertMem.LdpEval.ldpAddr, hs], hs, hm]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping Rt Rt2 imm7 f g → Pay mapping Rt Rt2 imm7 x g := by
    intro f g hg hs hm hz ⟨pa, data, mp, by16, gg, gs, gm, gz⟩
    refine ⟨pa, data, by rw [show ArmCertMem.LdpEval.ldpAddr x imm7 = ArmCertMem.LdpEval.ldpAddr f imm7 by simp only [ArmCertMem.LdpEval.ldpAddr, hs]]; exact mp,
      by rw [← hm]; exact by16, ?_, by rw [gs, hs], by rw [gm, hm], by rw [gz, hz]⟩
    rw [gg]; simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr, hg]
  obtain ⟨fin, run, current, regs, footprint, pay, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.mem_route real spec config rows mapping m scope image loadBase separated base offset budget k catalogue 1 room page
      aligned sel {} K [(.x (RegBind.rk Rt), .drop), (.x (RegBind.rk Rt2), .drop)]
      (fun s => s.regs._PC + 4#64) (Facts spec mapping m imm7) (fun _ => False) (Pay mapping Rt Rt2 imm7) (fun f => DataRecs.dataRecs spec (ArmCertMem.LdpEval.ldpAddr f imm7) false 16) nodup (fun _ _ _ _ h => h)
      x inv allowed (fun f hg hs => by simp only [ArmCertMem.LdpEval.ldpAddr, hg, hs]) xferX xferPay
      (ReleaseProfile.DefaultLdpOff.tailGE real spec config rows mapping m sel K hK imm7 Rt Rt2 hRt hRt2 hRtt dispatch noEret _ catalogue x)
      nextPlaced obligations rfl
  exact ⟨fin, run, ⟨current, regs, footprint, pay, sys, z, dit, ev, choice⟩⟩

#print axioms routeE
end ReleaseProfile.DefaultLdpOff

namespace ReleaseProfile.DefaultStpOff
open ArmCertMemPipe ArmCertMemPipe.StpOff
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

#check "CURRENT_DECL StpOff.routeE"
theorem routeE (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt 31#5 Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (facts : Facts spec mapping m D imm7 x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (nodup : (spec.logicalRows.map (·.logical)).Nodup) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultRuntime.MemoryStep spec config rows mapping m scope image loadBase base offset budget k catalogue 1
        [] D (Pay mapping Rt Rt2 imm7)
        (DataRecs.dataRecs spec (ArmCertMem.LdpEval.ldpAddr x imm7) true 16) x fin := by
  have aEq : ∀ f : NativeState, f.regs.SP_EL0 = x.regs.SP_EL0 → ArmCertMem.LdpEval.ldpAddr f imm7 = ArmCertMem.LdpEval.ldpAddr x imm7 := by
    intro f hs; simp only [ArmCertMem.LdpEval.ldpAddr, hs]
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec mapping m D imm7 f := by
    intro f _ hs _
    rw [Facts, aEq f hs, hs]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping Rt Rt2 imm7 f g → Pay mapping Rt Rt2 imm7 x g := by
    intro f g hg hs hm hz ⟨pa, mp, gm, gg, gs, gz⟩
    refine ⟨pa, by rw [← aEq f hs]; exact mp, ?_, by rw [gg, hg], by rw [gs, hs], by rw [gz, hz]⟩
    rw [gm, hm]; simp only [ArmCertMem.StpEval.stpData, hg]
  obtain ⟨fin, run, current, regs, footprint, pay, sys, z, dit, ev, choice⟩ :=
    ReleaseProfile.DefaultRuntime.mem_route real spec config rows mapping m scope image loadBase separated base offset budget k catalogue 1 room page
      aligned sel {} K [] (fun s => s.regs._PC + 4#64)
      (Facts spec mapping m D imm7) D (Pay mapping Rt Rt2 imm7) (fun f => DataRecs.dataRecs spec (ArmCertMem.LdpEval.ldpAddr f imm7) true 16) nodup codeD
      x inv allowed (fun f hg hs => by simp only [ArmCertMem.LdpEval.ldpAddr, hg, hs]) xferX xferPay (ReleaseProfile.DefaultStpOff.tailGE real spec config rows mapping m sel K hK imm7 Rt Rt2 hRt hRt2 dispatch noEret D catalogue x)
      nextPlaced obligations rfl
  exact ⟨fin, run, ⟨current, regs, footprint, pay, sys, z, dit, ev, choice⟩⟩

#print axioms routeE
end ReleaseProfile.DefaultStpOff
