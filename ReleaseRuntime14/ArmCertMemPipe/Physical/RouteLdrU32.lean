-- additive physical-byte route; original release route remains unchanged.
-- Memory (d200): the runtime14 LDR (unsigned, 64-bit) StepV route over ChainInvG: mem_routeG + LdrU32.tailG + values.
import ArmCertMemPipe.RouteG
import ArmCertMemPipe.TailLdrU32
import ArmCertStepV.Core
import ArmCertValue.PhysicalMemory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertMemPipe.LdrU32
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

theorem addr_congr {f x : NativeState} (Rn : BitVec 5) (imm12 : BitVec 12) (h : f.regs.gpr = x.regs.gpr) :
    MemClass.LdrU32.addr f Rn imm12 = MemClass.LdrU32.addr x Rn imm12 := by
  simp only [MemClass.LdrU32.addr, h]

/-- A runtime14 LDR Xt, [Xn, #imm] step over ChainInvG: the step runs, VHolds vus none (vus compatible with
[(x Rt, drop)], e.g. [(x Rt, none)]) and MemVHolds [.load (x Rt) r w], given the access facts at x and the region
word's linear VAs onto the access PA. -/
theorem routePhysical (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (dispatch : DispatchAt real sel
      (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (facts : Facts spec config rows mapping m imm12 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (bytePA : ArmCertValue.Physical.BytePA) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (j : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.LdrU32.addr x Rn imm12) = some pa → ∀ t : Nat, t < 4 →
      bytePA r (j + t) = some (pa + t))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.x (RegBind.rk Rt), .drop)]) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds vus none x fin ∧
      ArmCertValue.Physical.MemVHolds bytePA regions [.load32 (.x (RegBind.rk Rt)) r j] x fin := by
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
  obtain ⟨fin, run, holds, _, ⟨pa, data, mp, by8, gg, _, gm, gz⟩⟩ :=
    mem_routeG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [(.x (RegBind.rk Rt), .drop)] (fun s => s.regs._PC + 4#64)
      (Facts spec config rows mapping m imm12 Rn) (fun _ => False) (Pay mapping imm12 Rn Rt) (fun _ _ _ _ h => h)
      x inv xferX xferPay (tailG real spec config rows mapping m sel K hK imm12 Rn Rt hRn hRt dispatch noEret _ x)
      nextPlaced obligations
  refine ⟨fin, run, ArmCertValue.StepVCore.vholds_of_holds compat rfl holds gz, ?_⟩
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
end ArmCertMemPipe.LdrU32
