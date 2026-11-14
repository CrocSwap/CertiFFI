-- Memory (d200): the runtime14 STP pre-index StepV route over ChainInvG: mem_routeG + StpPre.tailG + pair store values.
import ArmCertMemPipe.RouteG
import ArmCertMemPipe.TailStpPre
import ArmCertStepV.Core
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertMemPipe.StpPre
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

/-- A runtime14 STP Xt, Xt2, [sp, #imm]! step over ChainInvG: VHolds vus none (vus compatible with [(sp, set sp c)])
and MemVHolds [.store Rt r w, .store Rt2 r (w+1)], given the access facts, linear VAs and the ByteFree miss. -/
theorem routeV (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (sel : BitVec 32) (K : Int) (hK : ((-1 : Int) <b K) = true)
    (imm7 : BitVec 7) (Rt Rt2 : BitVec 5) (hRt : Rt.toNat < 31) (hRt2 : Rt2.toNat < 31)
    (c : Int) (hc : BitVec.signExtend 64 imm7 <<< 3 = BitVec.ofInt 64 c)
    (dispatch : DispatchAt real sel
      (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt 31#5 Rt2 imm7 0#1 2#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (facts : Facts spec mapping m D imm7 x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (pinv : Nat → Nat) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.StpPre.ldpAddr x imm7) = some pa → ∀ j : Nat, j < 16 →
      mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + 8 * (w : Int) + (j : Int))) = some (pa + j))
    (miss : ∀ pa : Nat, mapping (MemClass.StpPre.ldpAddr x imm7) = some pa →
      ∀ r' ∈ regions, ∀ j', j' < 8 * r'.words →
        ArmCertR14.Value.ByteFree [.store (.x (RegBind.rk Rt)) r w, .store (.x (RegBind.rk Rt2)) r (w + 1)] r' j' → ∀ q,
        mapping (BitVec.ofInt 64 ((pinv r'.pin : Int) + r'.off + j')) = some q → ¬ (pa ≤ q ∧ q < pa + 16))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.sp, .set .sp c)]) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds vus none x fin ∧
      ArmCertValue.MemVHolds mapping pinv regions
        [.store (.x (RegBind.rk Rt)) r w, .store (.x (RegBind.rk Rt2)) r (w + 1)] x fin := by
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
  obtain ⟨fin, run, holds, _, ⟨pa, mp, gm, gg, _, gz⟩⟩ :=
    mem_routeG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [(.sp, .set .sp c)] (fun s => s.regs._PC + 4#64)
      (Facts spec mapping m D imm7) D (Pay mapping Rt Rt2 imm7) codeD
      x inv xferX xferPay (tailG real spec config rows mapping m sel K hK imm7 Rt Rt2 hRt hRt2 c hc dispatch noEret D x)
      nextPlaced obligations
  refine ⟨fin, run, ArmCertValue.StepVCore.vholds_of_holds compat rfl holds gz, ?_⟩
  exact ArmCertR14.Value.memV_storePair mapping pinv regions x fin _ _ r w pa.toNat _
    (fun j hj => by rw [gm, MemM1.MemWriteD1.wfold_get, if_pos (by omega), show pa.toNat + j - pa.toNat = j by omega])
    (fun q hq => by rw [gm, MemM1.MemWriteD1.wfold_get, if_neg hq])
    (fun j hj => MemClass.StpPre.stpByte_lo x Rt Rt2 j hj) (fun j hj => MemClass.StpPre.stpByte_hi x Rt Rt2 j hj)
    (lin pa.toNat mp) (miss pa.toNat mp)

#print axioms routeV
end ArmCertMemPipe.StpPre
