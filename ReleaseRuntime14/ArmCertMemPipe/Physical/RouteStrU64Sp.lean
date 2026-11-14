-- additive physical-byte route; original release route remains unchanged.
-- Memory (d200): the runtime14 STR (unsigned, 64-bit) StepV route over ChainInvG: mem_routeG + StrU64Sp.tailG + values.
import ArmCertMemPipe.RouteG
import ArmCertMemPipe.TailStrU64Sp
import ArmCertStepV.Core
import ArmCertValue.PhysicalMemory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertMemPipe.StrU64Sp
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

theorem addr_congr {f x : NativeState} (imm12 : BitVec 12) (h : f.regs.SP_EL0 = x.regs.SP_EL0) :
    MemClass.StrU64Sp.addr f imm12 = MemClass.StrU64Sp.addr x imm12 := by
  simp only [MemClass.StrU64Sp.addr, h]

/-- A runtime14 STR Xt, [Xn, #imm] step over ChainInvG: VHolds vus none (vus compatible with []) and
MemVHolds [.store (x Rt) r w], given the access facts, the word's linear VAs and the ByteFree miss. -/
theorem routePhysical (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rt : BitVec 5) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 0#2 3#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (facts : Facts spec mapping m D imm12 x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.StrU64Sp.addr x imm12) = some pa → ∀ j : Nat, j < 8 →
      bytePA r (8 * w + j) = some (pa + j))
    (miss : ∀ pa : Nat, mapping (MemClass.StrU64Sp.addr x imm12) = some pa →
      ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words →
        ArmCertValue.Physical.ByteFree [.store (.x (RegBind.rk Rt)) r w] r' j' → ∀ q,
        bytePA r' j' = some q → ¬ (pa ≤ q ∧ q < pa + 8))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus []) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds vus none x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions [.store (.x (RegBind.rk Rt)) r w] x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec mapping m D imm12 f := by
    intro f hg hs _
    rw [Facts, addr_congr imm12 hs, hs]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping imm12 Rt f g → Pay mapping imm12 Rt x g := by
    intro f g hg hs hm hz ⟨pa, mp, gm, gg, gs, gz⟩
    refine ⟨pa, by rw [← addr_congr imm12 hs]; exact mp, ?_, by rw [gg, hg], by rw [gs, hs], by rw [gz, hz]⟩
    rw [gm, hm]; simp only [MemClass.StrU64Sp.stData, hg]
  obtain ⟨fin, run, holds, _, ⟨pa, mp, gm, _, _, gz⟩⟩ :=
    mem_routeG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [] (fun s => s.regs._PC + 4#64)
      (Facts spec mapping m D imm12) D (Pay mapping imm12 Rt) codeD
      x inv xferX xferPay (tailG real spec config rows mapping m sel K hK imm12 Rt hRt dispatch noEret D x)
      nextPlaced obligations
  refine ⟨fin, run, ArmCertValue.StepVCore.vholds_of_holds compat rfl holds gz, ?_⟩
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
end ArmCertMemPipe.StrU64Sp
