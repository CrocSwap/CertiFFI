-- Memory (d200): the runtime14 LDP post-index StepV route over ChainInvG: mem_routeG + LdpPost.tailG + pair values.
import ArmCertMemPipe.RouteG
import ArmCertMemPipe.TailLdpPost
import ArmCertStepV.Core
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertMemPipe.LdpPost
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

/-- A runtime14 LDP Xt, Xt2, [sp], #imm step over ChainInvG: VHolds vus none (vus compatible with
[(x Rt, drop), (x Rt2, drop), (sp, set sp c)]) and MemVHolds [.load Rt r w, .load Rt2 r (w+1)]. -/
theorem routeV (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31) (hRtt : Rt ≠ Rt2)
    (c : Int) (hc : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 c)
    (dispatch : DispatchAt real sel
      (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt 31#5 Rt2 imm7 1#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (facts : Facts spec mapping m x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (pinv : Nat → Nat) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ pa : Nat, mapping x.regs.SP_EL0 = some pa → ∀ j : Nat, j < 16 →
      mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + 8 * (w : Int) + (j : Int))) = some (pa + j))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.x (RegBind.rk Rt), .drop), (.x (RegBind.rk Rt2), .drop), (.sp, .set .sp c)]) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds vus none x fin ∧
      ArmCertValue.MemVHolds mapping pinv regions
        [.load (.x (RegBind.rk Rt)) r w, .load (.x (RegBind.rk Rt2)) r (w + 1)] x fin := by
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec mapping m f := by
    intro f _ hs hm
    rw [Facts, hs, hm]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping Rt Rt2 imm7 f g → Pay mapping Rt Rt2 imm7 x g := by
    intro f g hg hs hm hz ⟨pa, data, mp, by16, gg, gs, gm, gz⟩
    refine ⟨pa, data, by rw [← hs]; exact mp, by rw [← hm]; exact by16, ?_, by rw [gs, hs], by rw [gm, hm], by rw [gz, hz]⟩
    rw [gg]; simp only [MemClass.LdpPost.ldpPost, MemClass.LdpPost.spWrite_eq, CryptoMem.MemCore.setGpr, hg]
  obtain ⟨fin, run, holds, _, ⟨pa, data, mp, by16, gg, _, gm, gz⟩⟩ :=
    mem_routeG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [(.x (RegBind.rk Rt), .drop), (.x (RegBind.rk Rt2), .drop), (.sp, .set .sp c)]
      (fun s => s.regs._PC + 4#64) (Facts spec mapping m) (fun _ => False) (Pay mapping Rt Rt2 imm7) (fun _ _ _ _ h => h)
      x inv xferX xferPay
      (tailG real spec config rows mapping m sel K hK imm7 Rt Rt2 hRt hRt2 hRtt c hc dispatch noEret _ x)
      nextPlaced obligations
  refine ⟨fin, run, ArmCertValue.StepVCore.vholds_of_holds compat rfl holds gz, ?_⟩
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
  refine ArmCertR14.Value.memV_loadPair mapping pinv regions x fin _ _ r w pa.toNat (fun j => data.extractLsb' (8 * j) 8) gm by16
    (fun j hj => ?_) (fun j hj => ?_) (lin pa.toNat mp)
  · show _ = ArmCertValue.MemRegion.byteOf (fin.regs.gpr[(RegBind.rk Rt).val]) j
    rw [vlo, MemClass.LdpPost.lo_byte data j hj]
  · show _ = ArmCertValue.MemRegion.byteOf (fin.regs.gpr[(RegBind.rk Rt2).val]) j
    rw [vhi, MemClass.LdpPost.hi_byte data j hj]

#print axioms routeV
end ArmCertMemPipe.LdpPost
