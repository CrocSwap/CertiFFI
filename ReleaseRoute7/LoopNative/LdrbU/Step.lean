-- additive physical-byte route; original release route remains unchanged.
-- Memory (d200): the runtime14 LDR (unsigned, 64-bit) StepV route over ChainInvG: mem_routeG + LdrbU.tailG + values.
import LoopNative.Encoding
import ArmCertMemPipe.RouteG
import ArmCertMemPipe.TailLdrbU
import ArmCertStepV.Core
import ArmCertValue.PhysicalMemory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace LoopNative.LdrbU
open ArmCertMemPipe ArmCertMemPipe.LdrbU
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

theorem addr_congr {f x : NativeState} (Rn : BitVec 5) (imm12 : BitVec 12) (h : f.regs.gpr = x.regs.gpr) :
    MemClass.LdrbU.addr f Rn imm12 = MemClass.LdrbU.addr x Rn imm12 := by
  simp only [MemClass.LdrbU.addr, h]

/-- Actual unsigned-byte Sail step, with selected dispatch discharged internally.
Facts refer only to the current state; the byte has no alignment restriction. -/
theorem step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm12 : BitVec 12) (Rn Rt : BitVec 5) (hRn : Rn.toNat < 31) (hRt : Rt.toNat < 31)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (facts : Facts spec config rows mapping m imm12 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.LdrbUoff.selected Rt Rn imm12) x)
    : ∃ fin, modelStep real x = .ok () fin ∧ RegBind.Holds [ (.x (RegBind.rk Rt), .drop)] x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → (fun _ => False) a)) ∧
      Pay mapping imm12 Rn Rt x fin := by
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
  exact
    mem_routeG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} 633 [(.x (RegBind.rk Rt), .drop)] (fun s => s.regs._PC + 4#64)
      (Facts spec config rows mapping m imm12 Rn) (fun _ => False) (Pay mapping imm12 Rn Rt) (fun _ _ _ _ h => h)
      x inv xferX xferPay (tailG real spec config rows mapping m sel 633 (by decide) imm12 Rn Rt hRn hRt dispatch noEret _ x)
      nextPlaced obligations

#print axioms step
end LoopNative.LdrbU
