-- Physical byte and register effects of the actual runtime memory routes.
import DefaultRuntimeEventRoutes
import ArmCertStepV.Core
import ArmCertValue.PhysicalMemory

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.EntryActualFetch
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultLdpOff
open ArmCertMemPipe ArmCertMemPipe.LdpOff
#check "CURRENT_DECL LdpOff.routePhysical"
theorem routePhysical (real : Type) [Sail.SailReal real]
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ pa : Nat, mapping (ArmCertMem.LdpEval.ldpAddr x imm7) = some pa → ∀ j : Nat, j < 16 →
      bytePA r (8 * w + j) = some (pa + j))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.x (RegBind.rk Rt), .drop), (.x (RegBind.rk Rt2), .drop)]) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds vus none x fin ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping (DataRecs.dataRecs spec (ArmCertMem.LdpEval.ldpAddr x imm7) false 16) x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions
        [.load (.x (RegBind.rk Rt)) r w, .load (.x (RegBind.rk Rt2)) r (w + 1)] x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  obtain ⟨fin, run, result⟩ :=
    ReleaseProfile.DefaultLdpOff.routeE real spec config rows mapping m scope image loadBase separated base offset budget k catalogue
      room page aligned sel K hK imm7 Rt Rt2 hRt hRt2 hRtt dispatch noEret x inv allowed facts nextPlaced obligations nodup
  obtain ⟨pa, data, mp, by16, gg, _, gm, gz⟩ := result.pay
  refine ⟨fin, run, result.current, ArmCertValue.StepVCore.vholds_of_holds compat rfl result.regs gz, result.z, result.dit, result.events, ?_, result.choice⟩
  have hne : (GPRSummary.key Rt2.toNat).val ≠ (GPRSummary.key Rt.toNat).val := by
    have k1 : ∀ n : Fin 31, (GPRSummary.key n.val).val = n.val := by decide
    rw [k1 ⟨Rt2.toNat, hRt2⟩, k1 ⟨Rt.toNat, hRt⟩]
    intro h; exact hRtt (BitVec.eq_of_toNat_eq h.symm)
  have vlo : fin.regs.gpr[(RegBind.rk Rt).val] = ArmCertMem.LdpEval.ldpLo data := by
    rw [gg]; simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr, RegBind.rk]
    rw [Vector.getElem_set_ne _ _ hne, Vector.getElem_set_self]
  have vhi : fin.regs.gpr[(RegBind.rk Rt2).val] = ArmCertMem.LdpEval.ldpHi data := by
    rw [gg]; simp only [ArmCertMem.LdpEval.ldpPost, CryptoMem.MemCore.setGpr, RegBind.rk]
    rw [Vector.getElem_set_self]
  refine ArmCertValue.Physical.memV_loadPair bytePA regions x fin _ _ r w pa.toNat (fun j => data.extractLsb' (8 * j) 8) gm by16
    (fun j hj => ?_) (fun j hj => ?_) (lin pa.toNat mp)
  · show _ = ArmCertValue.MemRegion.byteOf (fin.regs.gpr[(RegBind.rk Rt).val]) j
    rw [vlo, show ArmCertMem.LdpEval.ldpLo data = MemClass.LdpPost.ldpLo data from rfl, MemClass.LdpPost.lo_byte data j hj]
  · show _ = ArmCertValue.MemRegion.byteOf (fin.regs.gpr[(RegBind.rk Rt2).val]) j
    rw [vhi, show ArmCertMem.LdpEval.ldpHi data = MemClass.LdpPost.ldpHi data from rfl, MemClass.LdpPost.hi_byte data j hj]

#print axioms routePhysical
end ReleaseProfile.DefaultLdpOff

namespace ReleaseProfile.DefaultLdpPost
open ArmCertMemPipe ArmCertMemPipe.LdpPost
#check "CURRENT_DECL LdpPost.routePhysical"
theorem routePhysical (real : Type) [Sail.SailReal real]
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ pa : Nat, mapping x.regs.SP_EL0 = some pa → ∀ j : Nat, j < 16 →
      bytePA r (8 * w + j) = some (pa + j))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.x (RegBind.rk Rt), .drop), (.x (RegBind.rk Rt2), .drop), (.sp, .set .sp c)]) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds vus none x fin ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping (DataRecs.dataRecs spec (x.regs.SP_EL0) false 16) x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions
        [.load (.x (RegBind.rk Rt)) r w, .load (.x (RegBind.rk Rt2)) r (w + 1)] x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  obtain ⟨fin, run, result⟩ :=
    ReleaseProfile.DefaultLdpPost.routeE real spec config rows mapping m scope image loadBase separated base offset budget k catalogue
      room page aligned sel K hK imm7 Rt Rt2 hRt hRt2 hRtt c hc dispatch noEret x inv allowed facts nextPlaced obligations nodup
  obtain ⟨pa, data, mp, by16, gg, _, gm, gz⟩ := result.pay
  refine ⟨fin, run, result.current, ArmCertValue.StepVCore.vholds_of_holds compat rfl result.regs gz, result.z, result.dit, result.events, ?_, result.choice⟩
  have hne : (GPRSummary.key Rt2.toNat).val ≠ (GPRSummary.key Rt.toNat).val := by
    have k1 : ∀ n : Fin 31, (GPRSummary.key n.val).val = n.val := by decide
    rw [k1 ⟨Rt2.toNat, hRt2⟩, k1 ⟨Rt.toNat, hRt⟩]
    intro h; exact hRtt (BitVec.eq_of_toNat_eq h.symm)
  have vlo : fin.regs.gpr[(RegBind.rk Rt).val] = MemClass.LdpPost.ldpLo data := by
    rw [gg]; simp only [MemClass.LdpPost.ldpPost, MemClass.LdpPost.spWrite_eq, CryptoMem.MemCore.setGpr, RegBind.rk]
    rw [Vector.getElem_set_ne _ _ hne, Vector.getElem_set_self]
  have vhi : fin.regs.gpr[(RegBind.rk Rt2).val] = MemClass.LdpPost.ldpHi data := by
    rw [gg]; simp only [MemClass.LdpPost.ldpPost, MemClass.LdpPost.spWrite_eq, CryptoMem.MemCore.setGpr, RegBind.rk]
    rw [Vector.getElem_set_self]
  refine ArmCertValue.Physical.memV_loadPair bytePA regions x fin _ _ r w pa.toNat (fun j => data.extractLsb' (8 * j) 8) gm by16
    (fun j hj => ?_) (fun j hj => ?_) (lin pa.toNat mp)
  · show _ = ArmCertValue.MemRegion.byteOf (fin.regs.gpr[(RegBind.rk Rt).val]) j
    rw [vlo, MemClass.LdpPost.lo_byte data j hj]
  · show _ = ArmCertValue.MemRegion.byteOf (fin.regs.gpr[(RegBind.rk Rt2).val]) j
    rw [vhi, MemClass.LdpPost.hi_byte data j hj]

#print axioms routePhysical
end ReleaseProfile.DefaultLdpPost

namespace ReleaseProfile.DefaultLdrU32
open ArmCertMemPipe ArmCertMemPipe.LdrU32
#check "CURRENT_DECL LdrU32.routePhysical"
theorem routePhysical (real : Type) [Sail.SailReal real]
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (j : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.LdrU32.addr x Rn imm12) = some pa → ∀ t : Nat, t < 4 →
      bytePA r (j + t) = some (pa + t))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.x (RegBind.rk Rt), .drop)]) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds vus none x fin ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping (DataRecs.dataRecs spec (MemClass.LdrU32.addr x Rn imm12) false 4) x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions [.load32 (.x (RegBind.rk Rt)) r j] x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  obtain ⟨fin, run, result⟩ :=
    ReleaseProfile.DefaultLdrU32.routeE real spec config rows mapping m scope image loadBase separated base offset budget k catalogue
      room page aligned sel K hK imm12 Rn Rt hRn hRt dispatch noEret x inv allowed facts nextPlaced obligations nodup
  obtain ⟨pa, data, mp, by8, gg, _, gm, gz⟩ := result.pay
  refine ⟨fin, run, result.current, ArmCertValue.StepVCore.vholds_of_holds compat rfl result.regs gz, result.z, result.dit, result.events, ?_, result.choice⟩
  have hval : fin.regs.gpr[(RegBind.rk Rt).val] = MemClass.LdrU32.val data := by
    rw [gg]
    show (x.regs.gpr.set (GPRSummary.key Rt.toNat).val (MemClass.LdrU32.val data) (GPRSummary.key Rt.toNat).isLt)[(GPRSummary.key Rt.toNat).val] = _
    rw [Vector.getElem_set_self]
  refine ArmCertValue.Physical.memV_of_mem bytePA regions x fin _ gm (fun e he => ?_)
  rw [List.mem_singleton] at he; subst he
  refine ⟨fun e he => ?_, fun r h => by simp at h, fun r h => by simp at h⟩
  rw [List.mem_singleton] at he; subst he
  refine ⟨data.setWidth 64, ?_, fun t ht => ?_, ?_⟩
  · simp only [BitVec.toNat_setWidth]; omega
  · show (bytePA _ _).bind _ = _
    rw [lin pa.toNat mp t ht, Option.bind_some, by8 t ht, MemClass.LdrU32.byte_eq data t ht]
  · show fin.regs.gpr[(RegBind.rk Rt).val] = _
    rw [hval, MemClass.LdrU32.val_eq]

#print axioms routePhysical
end ReleaseProfile.DefaultLdrU32

namespace ReleaseProfile.DefaultLdrU64
open ArmCertMemPipe ArmCertMemPipe.LdrU64
#check "CURRENT_DECL LdrU64.routePhysical"
theorem routePhysical (real : Type) [Sail.SailReal real]
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.LdrU64.addr x Rn imm12) = some pa → ∀ j : Nat, j < 8 →
      bytePA r (8 * w + j) = some (pa + j))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.x (RegBind.rk Rt), .drop)]) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds vus none x fin ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping (DataRecs.dataRecs spec (MemClass.LdrU64.addr x Rn imm12) false 8) x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions [.load (.x (RegBind.rk Rt)) r w] x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  obtain ⟨fin, run, result⟩ :=
    ReleaseProfile.DefaultLdrU64.routeE real spec config rows mapping m scope image loadBase separated base offset budget k catalogue
      room page aligned sel K hK imm12 Rn Rt hRn hRt dispatch noEret x inv allowed facts nextPlaced obligations nodup
  obtain ⟨pa, data, mp, by8, gg, _, gm, gz⟩ := result.pay
  refine ⟨fin, run, result.current, ArmCertValue.StepVCore.vholds_of_holds compat rfl result.regs gz, result.z, result.dit, result.events, ?_, result.choice⟩
  refine ArmCertValue.Physical.memV_loads bytePA regions x fin _ gm (fun e he => ⟨_, r, w, List.mem_singleton.1 he, ?_⟩)
  have hb := ArmCertValue.Physical.regionBytes_of_span bytePA x r w pa.toNat data (lin pa.toNat mp) by8
  rw [ArmCertValue.Physical.regionWord_of_bytes bytePA x r w data hb]
  show some data = some (fin.regs.gpr[(RegBind.rk Rt).val])
  rw [gg]
  show some data = some ((x.regs.gpr.set (GPRSummary.key Rt.toNat).val (MemClass.LdrU64.val data) (GPRSummary.key Rt.toNat).isLt)[(GPRSummary.key Rt.toNat).val])
  rw [Vector.getElem_set_self, MemClass.LdrU64.val_eq]

#print axioms routePhysical
end ReleaseProfile.DefaultLdrU64

namespace ReleaseProfile.DefaultLdrU64Sp
open ArmCertMemPipe ArmCertMemPipe.LdrU64Sp
#check "CURRENT_DECL LdrU64Sp.routePhysical"
theorem routePhysical (real : Type) [Sail.SailReal real]
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.LdrU64Sp.addr x imm12) = some pa → ∀ j : Nat, j < 8 →
      bytePA r (8 * w + j) = some (pa + j))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.x (RegBind.rk Rt), .drop)]) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds vus none x fin ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping (DataRecs.dataRecs spec (MemClass.LdrU64Sp.addr x imm12) false 8) x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions [.load (.x (RegBind.rk Rt)) r w] x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  obtain ⟨fin, run, result⟩ :=
    ReleaseProfile.DefaultLdrU64Sp.routeE real spec config rows mapping m scope image loadBase separated base offset budget k catalogue
      room page aligned sel K hK imm12 Rt hRt dispatch noEret x inv allowed facts nextPlaced obligations nodup
  obtain ⟨pa, data, mp, by8, gg, _, gm, gz⟩ := result.pay
  refine ⟨fin, run, result.current, ArmCertValue.StepVCore.vholds_of_holds compat rfl result.regs gz, result.z, result.dit, result.events, ?_, result.choice⟩
  refine ArmCertValue.Physical.memV_loads bytePA regions x fin _ gm (fun e he => ⟨_, r, w, List.mem_singleton.1 he, ?_⟩)
  have hb := ArmCertValue.Physical.regionBytes_of_span bytePA x r w pa.toNat data (lin pa.toNat mp) by8
  rw [ArmCertValue.Physical.regionWord_of_bytes bytePA x r w data hb]
  show some data = some (fin.regs.gpr[(RegBind.rk Rt).val])
  rw [gg]
  show some data = some ((x.regs.gpr.set (GPRSummary.key Rt.toNat).val (MemClass.LdrU64Sp.val data) (GPRSummary.key Rt.toNat).isLt)[(GPRSummary.key Rt.toNat).val])
  rw [Vector.getElem_set_self, MemClass.LdrU64Sp.val_eq]

#print axioms routePhysical
end ReleaseProfile.DefaultLdrU64Sp

namespace ReleaseProfile.DefaultLdrbU
open ArmCertMemPipe ArmCertMemPipe.LdrbU
#check "CURRENT_DECL LdrbU.routePhysical"
theorem routePhysical (real : Type) [Sail.SailReal real]
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (j : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.LdrbU.addr x Rn imm12) = some pa →
      bytePA r j = some pa)
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.x (RegBind.rk Rt), .drop)]) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds vus none x fin ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping (DataRecs.dataRecs spec (MemClass.LdrbU.addr x Rn imm12) false 1) x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions [.loadb (.x (RegBind.rk Rt)) r j] x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  obtain ⟨fin, run, result⟩ :=
    ReleaseProfile.DefaultLdrbU.routeE real spec config rows mapping m scope image loadBase separated base offset budget k catalogue
      room page aligned sel K hK imm12 Rn Rt hRn hRt dispatch noEret x inv allowed facts nextPlaced obligations nodup
  obtain ⟨pa, data, mp, by8, gg, _, gm, gz⟩ := result.pay
  refine ⟨fin, run, result.current, ArmCertValue.StepVCore.vholds_of_holds compat rfl result.regs gz, result.z, result.dit, result.events, ?_, result.choice⟩
  have hval : fin.regs.gpr[(RegBind.rk Rt).val] = MemClass.LdrbU.val data := by
    rw [gg]
    show (x.regs.gpr.set (GPRSummary.key Rt.toNat).val (MemClass.LdrbU.val data) (GPRSummary.key Rt.toNat).isLt)[(GPRSummary.key Rt.toNat).val] = _
    rw [Vector.getElem_set_self]
  refine ArmCertValue.Physical.memV_of_mem bytePA regions x fin _ gm (fun e he => ?_)
  rw [List.mem_singleton] at he; subst he
  refine ⟨fun e he => ?_, fun r h => by simp at h, fun r h => by simp at h⟩
  rw [List.mem_singleton] at he; subst he
  refine ⟨data, ?_, ?_⟩
  · show (bytePA _ _).bind _ = _
    rw [lin pa.toNat mp, Option.bind_some]
    have h0 := by8 0 (by decide)
    simp only [Nat.add_zero] at h0
    rw [h0]; congr 1
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [BitVec.getLsbD_extractLsb', hi]
  · show fin.regs.gpr[(RegBind.rk Rt).val] = _
    rw [hval, MemClass.LdrbU.val_eq]

#print axioms routePhysical
end ReleaseProfile.DefaultLdrbU

namespace ReleaseProfile.DefaultStpOff
open ArmCertMemPipe ArmCertMemPipe.StpOff
#check "CURRENT_DECL StpOff.routePhysical"
theorem routePhysical (real : Type) [Sail.SailReal real]
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ pa : Nat, mapping (ArmCertMem.LdpEval.ldpAddr x imm7) = some pa → ∀ j : Nat, j < 16 →
      bytePA r (8 * w + j) = some (pa + j))
    (miss : ∀ pa : Nat, mapping (ArmCertMem.LdpEval.ldpAddr x imm7) = some pa →
      ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words →
        ArmCertValue.Physical.ByteFree [.store (.x (RegBind.rk Rt)) r w, .store (.x (RegBind.rk Rt2)) r (w + 1)] r' j' → ∀ q,
        bytePA r' j' = some q → ¬ (pa ≤ q ∧ q < pa + 16))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus []) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds vus none x fin ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping (DataRecs.dataRecs spec (ArmCertMem.LdpEval.ldpAddr x imm7) true 16) x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions
        [.store (.x (RegBind.rk Rt)) r w, .store (.x (RegBind.rk Rt2)) r (w + 1)] x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  obtain ⟨fin, run, result⟩ :=
    ReleaseProfile.DefaultStpOff.routeE real spec config rows mapping m scope image loadBase separated base offset budget k catalogue
      room page aligned sel K hK imm7 Rt Rt2 hRt hRt2 dispatch noEret D codeD x inv allowed facts nextPlaced obligations nodup
  obtain ⟨pa, mp, gm, gg, _, gz⟩ := result.pay
  refine ⟨fin, run, result.current, ArmCertValue.StepVCore.vholds_of_holds compat rfl result.regs gz, result.z, result.dit, result.events, ?_, result.choice⟩
  exact ArmCertValue.Physical.memV_storePair bytePA regions x fin _ _ r w pa.toNat _
    (fun j hj => by rw [gm, MemM1.MemWriteD1.wfold_get, if_pos (by omega), show pa.toNat + j - pa.toNat = j by omega])
    (fun q hq => by rw [gm, MemM1.MemWriteD1.wfold_get, if_neg hq])
    (fun j hj => by rw [show ArmCertMem.StpEval.stpData x Rt Rt2 = MemClass.StpPre.stpData x Rt Rt2 from rfl]; exact MemClass.StpPre.stpByte_lo x Rt Rt2 j hj) (fun j hj => by rw [show ArmCertMem.StpEval.stpData x Rt Rt2 = MemClass.StpPre.stpData x Rt Rt2 from rfl]; exact MemClass.StpPre.stpByte_hi x Rt Rt2 j hj)
    (lin pa.toNat mp) (miss pa.toNat mp)

#print axioms routePhysical
end ReleaseProfile.DefaultStpOff

namespace ReleaseProfile.DefaultStpPre
open ArmCertMemPipe ArmCertMemPipe.StpPre
#check "CURRENT_DECL StpPre.routePhysical"
theorem routePhysical (real : Type) [Sail.SailReal real]
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.StpPre.ldpAddr x imm7) = some pa → ∀ j : Nat, j < 16 →
      bytePA r (8 * w + j) = some (pa + j))
    (miss : ∀ pa : Nat, mapping (MemClass.StpPre.ldpAddr x imm7) = some pa →
      ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words →
        ArmCertValue.Physical.ByteFree [.store (.x (RegBind.rk Rt)) r w, .store (.x (RegBind.rk Rt2)) r (w + 1)] r' j' → ∀ q,
        bytePA r' j' = some q → ¬ (pa ≤ q ∧ q < pa + 16))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.sp, .set .sp c)]) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds vus none x fin ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping (DataRecs.dataRecs spec (MemClass.StpPre.ldpAddr x imm7) true 16) x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions
        [.store (.x (RegBind.rk Rt)) r w, .store (.x (RegBind.rk Rt2)) r (w + 1)] x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  obtain ⟨fin, run, result⟩ :=
    ReleaseProfile.DefaultStpPre.routeE real spec config rows mapping m scope image loadBase separated base offset budget k catalogue
      room page aligned sel K hK imm7 Rt Rt2 hRt hRt2 c hc dispatch noEret D codeD x inv allowed facts nextPlaced obligations nodup
  obtain ⟨pa, mp, gm, gg, _, gz⟩ := result.pay
  refine ⟨fin, run, result.current, ArmCertValue.StepVCore.vholds_of_holds compat rfl result.regs gz, result.z, result.dit, result.events, ?_, result.choice⟩
  exact ArmCertValue.Physical.memV_storePair bytePA regions x fin _ _ r w pa.toNat _
    (fun j hj => by rw [gm, MemM1.MemWriteD1.wfold_get, if_pos (by omega), show pa.toNat + j - pa.toNat = j by omega])
    (fun q hq => by rw [gm, MemM1.MemWriteD1.wfold_get, if_neg hq])
    (fun j hj => MemClass.StpPre.stpByte_lo x Rt Rt2 j hj) (fun j hj => MemClass.StpPre.stpByte_hi x Rt Rt2 j hj)
    (lin pa.toNat mp) (miss pa.toNat mp)

#print axioms routePhysical
end ReleaseProfile.DefaultStpPre

namespace ReleaseProfile.DefaultStrU32
open ArmCertMemPipe ArmCertMemPipe.StrU32
#check "CURRENT_DECL StrU32.routePhysical"
theorem routePhysical (real : Type) [Sail.SailReal real]
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (j : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.StrU32.addr x Rn imm12) = some pa → ∀ t : Nat, t < 4 →
      bytePA r (j + t) = some (pa + t))
    (miss : ∀ pa : Nat, mapping (MemClass.StrU32.addr x Rn imm12) = some pa →
      ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words →
        ArmCertValue.Physical.ByteFree [.store32 (.x (RegBind.rk Rt)) r j] r' j' → ∀ q,
        bytePA r' j' = some q → ¬ (pa ≤ q ∧ q < pa + 4))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus []) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds vus none x fin ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping (DataRecs.dataRecs spec (MemClass.StrU32.addr x Rn imm12) true 4) x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions [.store32 (.x (RegBind.rk Rt)) r j] x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  obtain ⟨fin, run, result⟩ :=
    ReleaseProfile.DefaultStrU32.routeE real spec config rows mapping m scope image loadBase separated base offset budget k catalogue
      room page aligned sel K hK imm12 Rn Rt hRn hRt dispatch noEret D codeD x inv allowed facts nextPlaced obligations nodup
  obtain ⟨pa, mp, gm, _, _, gz⟩ := result.pay
  refine ⟨fin, run, result.current, ArmCertValue.StepVCore.vholds_of_holds compat rfl result.regs gz, result.z, result.dit, result.events, ?_, result.choice⟩
  refine ArmCertValue.Physical.memV_of_writes bytePA regions x fin _ pa.toNat 4
    (fun q hq => by rw [gm, MemM1.MemWriteD1.wfold_get, if_neg hq]) (miss pa.toNat mp) (fun e he => ?_)
  rw [List.mem_singleton] at he; subst he
  refine ⟨fun e he => ?_, fun r h => by simp at h, fun r h => by simp at h⟩
  rw [List.mem_singleton] at he; subst he
  intro t ht
  show (bytePA _ _).bind _ = _
  rw [lin pa.toNat mp t ht, Option.bind_some, gm, MemM1.MemWriteD1.wfold_get, if_pos (by omega),
    show pa.toNat + t - pa.toNat = t by omega, MemClass.StrU32.stByte x Rt t ht]
  rfl
#print axioms routePhysical
end ReleaseProfile.DefaultStrU32

namespace ReleaseProfile.DefaultStrU64Sp
open ArmCertMemPipe ArmCertMemPipe.StrU64Sp
#check "CURRENT_DECL StrU64Sp.routePhysical"
theorem routePhysical (real : Type) [Sail.SailReal real]
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.StrU64Sp.addr x imm12) = some pa → ∀ j : Nat, j < 8 →
      bytePA r (8 * w + j) = some (pa + j))
    (miss : ∀ pa : Nat, mapping (MemClass.StrU64Sp.addr x imm12) = some pa →
      ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words →
        ArmCertValue.Physical.ByteFree [.store (.x (RegBind.rk Rt)) r w] r' j' → ∀ q,
        bytePA r' j' = some q → ¬ (pa ≤ q ∧ q < pa + 8))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus []) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds vus none x fin ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping (DataRecs.dataRecs spec (MemClass.StrU64Sp.addr x imm12) true 8) x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions [.store (.x (RegBind.rk Rt)) r w] x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  obtain ⟨fin, run, result⟩ :=
    ReleaseProfile.DefaultStrU64Sp.routeE real spec config rows mapping m scope image loadBase separated base offset budget k catalogue
      room page aligned sel K hK imm12 Rt hRt dispatch noEret D codeD x inv allowed facts nextPlaced obligations nodup
  obtain ⟨pa, mp, gm, _, _, gz⟩ := result.pay
  refine ⟨fin, run, result.current, ArmCertValue.StepVCore.vholds_of_holds compat rfl result.regs gz, result.z, result.dit, result.events, ?_, result.choice⟩
  refine ArmCertValue.Physical.memV_of_writes bytePA regions x fin _ pa.toNat 8
    (fun q hq => by rw [gm, MemM1.MemWriteD1.wfold_get, if_neg hq]) (miss pa.toNat mp) (fun e he => ?_)
  rw [List.mem_singleton] at he; subst he
  refine ⟨fun e he => ?_, fun r h => by simp at h, fun r h => by simp at h⟩
  rw [List.mem_singleton] at he; subst he
  show ArmCertValue.Physical.regionWord bytePA fin r w = some (x.regs.gpr[(RegBind.rk Rt).val])
  refine ArmCertValue.Physical.regionWord_of_bytes bytePA fin r w _ (fun j hj => ?_)
  rw [ArmCertValue.Physical.regionByte, lin pa.toNat mp j hj, Option.bind_some, gm, MemM1.MemWriteD1.wfold_get,
    if_pos (by omega), show pa.toNat + j - pa.toNat = j by omega, MemClass.StrU64Sp.stByte]
  rfl

#print axioms routePhysical
end ReleaseProfile.DefaultStrU64Sp

namespace ReleaseProfile.DefaultStrbU
open ArmCertMemPipe ArmCertMemPipe.StrbU
#check "CURRENT_DECL StrbU.routePhysical"
theorem routePhysical (real : Type) [Sail.SailReal real]
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
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (j : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.StrbU.addr x Rn imm12) = some pa →
      bytePA r j = some pa)
    (miss : ∀ pa : Nat, mapping (MemClass.StrbU.addr x Rn imm12) = some pa →
      ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words →
        ArmCertValue.Physical.ByteFree [.storeb (.x (RegBind.rk Rt)) r j] r' j' → ∀ q,
        bytePA r' j' = some q → ¬ (pa ≤ q ∧ q < pa + 1))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus []) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin ∧
      ArmCertValue.VHolds vus none x fin ∧
      fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧ StepEvents.EvShape spec mapping (DataRecs.dataRecs spec (MemClass.StrbU.addr x Rn imm12) true 1) x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions [.storeb (.x (RegBind.rk Rt)) r j] x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ 1) := by
  obtain ⟨fin, run, result⟩ :=
    ReleaseProfile.DefaultStrbU.routeE real spec config rows mapping m scope image loadBase separated base offset budget k catalogue
      room page aligned sel K hK imm12 Rn Rt hRn hRt dispatch noEret D codeD x inv allowed facts nextPlaced obligations nodup
  obtain ⟨pa, mp, gm, _, _, gz⟩ := result.pay
  refine ⟨fin, run, result.current, ArmCertValue.StepVCore.vholds_of_holds compat rfl result.regs gz, result.z, result.dit, result.events, ?_, result.choice⟩
  refine ArmCertValue.Physical.memV_of_writes bytePA regions x fin _ pa.toNat 1
    (fun q hq => by rw [gm, MemM1.MemWriteD1.wfold_get, if_neg hq]) (miss pa.toNat mp) (fun e he => ?_)
  rw [List.mem_singleton] at he; subst he
  refine ⟨fun e he => ?_, fun r h => by simp at h, fun r h => by simp at h⟩
  rw [List.mem_singleton] at he; subst he
  show (bytePA _ _).bind _ = _
  rw [lin pa.toNat mp, Option.bind_some, gm, MemM1.MemWriteD1.wfold_get, if_pos (by omega), Nat.sub_self,
    MemClass.StrbU.stByte]
  rfl
#print axioms routePhysical
end ReleaseProfile.DefaultStrbU
