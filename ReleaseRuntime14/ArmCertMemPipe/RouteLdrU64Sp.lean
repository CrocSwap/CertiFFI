-- Memory (d200): the runtime14 LDR (unsigned, 64-bit) StepV route over ChainInvG: mem_routeG + LdrU64Sp.tailG + values.
import ArmCertMemPipe.RouteG
import ArmCertMemPipe.TailLdrU64Sp
import ArmCertStepV.Core
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertMemPipe.LdrU64Sp
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

theorem addr_congr {f x : NativeState} (imm12 : BitVec 12) (h : f.regs.SP_EL0 = x.regs.SP_EL0) :
    MemClass.LdrU64Sp.addr f imm12 = MemClass.LdrU64Sp.addr x imm12 := by
  simp only [MemClass.LdrU64Sp.addr, h]

/-- A runtime14 LDR Xt, [Xn, #imm] step over ChainInvG: the step runs, VHolds vus none (vus compatible with
[(x Rt, drop)], e.g. [(x Rt, none)]) and MemVHolds [.load (x Rt) r w], given the access facts at x and the region
word's linear VAs onto the access PA. -/
theorem routeV (real : Type) [Sail.SailReal real]
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
      (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt 31#5 imm12 1#2 3#2) K)
    (noEret : (Sail.BitVec.extractLsb sel 31 12 == 879088#20) = false)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (facts : Facts spec config rows mapping m imm12 x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping sel x)
    (pinv : Nat → Nat) (regions : List ArmCertValue.Region) (r : ArmCertValue.Region) (w : Nat)
    (lin : ∀ pa : Nat, mapping (MemClass.LdrU64Sp.addr x imm12) = some pa → ∀ j : Nat, j < 8 →
      mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + 8 * (w : Int) + (j : Int))) = some (pa + j))
    (vus : List (HeapV2StepCerts.RegBind.Reg × Option ArmCertValue.VUpd))
    (compat : ArmCertValue.StepVCore.Compat vus [(.x (RegBind.rk Rt), .drop)]) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds vus none x fin ∧
      ArmCertValue.MemVHolds mapping pinv regions [.load (.x (RegBind.rk Rt)) r w] x fin := by
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
  obtain ⟨fin, run, holds, _, ⟨pa, data, mp, by8, gg, _, gm, gz⟩⟩ :=
    mem_routeG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} K [(.x (RegBind.rk Rt), .drop)] (fun s => s.regs._PC + 4#64)
      (Facts spec config rows mapping m imm12) (fun _ => False) (Pay mapping imm12 Rt) (fun _ _ _ _ h => h)
      x inv xferX xferPay (tailG real spec config rows mapping m sel K hK imm12 Rt hRt dispatch noEret _ x)
      nextPlaced obligations
  refine ⟨fin, run, ArmCertValue.StepVCore.vholds_of_holds compat rfl holds gz, ?_⟩
  refine ArmCertR14.Value.memV_loads mapping pinv regions x fin _ gm (fun e he => ⟨_, r, w, List.mem_singleton.1 he, ?_⟩)
  have hb := ArmCertR14.Value.regionBytes_of_lin mapping pinv x r w pa.toNat data (lin pa.toNat mp) by8
  rw [ArmCertR14.Value.regionWord_of_bytes mapping pinv x r w data hb]
  show some data = some (fin.regs.gpr[(RegBind.rk Rt).val])
  rw [gg]
  show some data = some ((x.regs.gpr.set (GPRSummary.key Rt.toNat).val (MemClass.LdrU64Sp.val data) (GPRSummary.key Rt.toNat).isLt)[(GPRSummary.key Rt.toNat).val])
  rw [Vector.getElem_set_self, MemClass.LdrU64Sp.val_eq]

#print axioms routeV
end ArmCertMemPipe.LdrU64Sp
