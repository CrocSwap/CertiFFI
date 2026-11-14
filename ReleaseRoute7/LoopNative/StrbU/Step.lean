-- additive physical-byte route; original release route remains unchanged.
-- Memory (d200): the runtime14 STR (unsigned, 64-bit) StepV route over ChainInvG: mem_routeG + StrbU.tailG + values.
import LoopNative.Encoding
import ArmCertMemPipe.RouteG
import ArmCertMemPipe.TailStrbU
import ArmCertStepV.Core
import ArmCertValue.PhysicalMemory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace LoopNative.StrbU
open ArmCertMemPipe ArmCertMemPipe.StrbU
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv HeapV2StepCerts

theorem addr_congr {f x : NativeState} (Rn : BitVec 5) (imm12 : BitVec 12) (h : f.regs.gpr = x.regs.gpr) :
    MemClass.StrbU.addr f Rn imm12 = MemClass.StrbU.addr x Rn imm12 := by
  simp only [MemClass.StrbU.addr, h]

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
    (D : Nat → Prop) (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (facts : Facts spec mapping m D imm12 Rn x)
    (nextPlaced : x.regs._PC + 4#64 = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping (NativeEntryBodyDispatch.StrbUoff.selected Rt Rn imm12) x)
    : ∃ fin, modelStep real x = .ok () fin ∧ RegBind.Holds [] x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)) ∧
      Pay mapping imm12 Rn Rt x fin := by
  let sel := NativeEntryBodyDispatch.StrbUoff.selected Rt Rn imm12
  have dispatch : DispatchAt real sel
      (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 0#2) 651 := by
    intro pc t see
    exact NativeEntryBodyDispatch.StrbUoff.dispatch_at real pc Rt Rn imm12 t (by simpa using see)
  have noEret := Encoding.StrbU_noEret Rt Rn imm12
  have xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Facts spec mapping m D imm12 Rn f := by
    intro f hg _ _
    rw [Facts, addr_congr Rn imm12 hg]; exact facts
  have xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay mapping imm12 Rn Rt f g → Pay mapping imm12 Rn Rt x g := by
    intro f g hg hs hm hz ⟨pa, mp, gm, gg, gs, gz⟩
    refine ⟨pa, by rw [← addr_congr Rn imm12 hg]; exact mp, ?_, by rw [gg, hg], by rw [gs, hs], by rw [gz, hz]⟩
    rw [gm, hm]; simp only [MemClass.StrbU.stData, hg]
  exact
    mem_routeG real spec config rows mapping m scope image loadBase separated base offset budget extra k room page
      aligned sel {} 651 [] (fun s => s.regs._PC + 4#64)
      (Facts spec mapping m D imm12 Rn) D (Pay mapping imm12 Rn Rt) codeD
      x inv xferX xferPay (tailG real spec config rows mapping m sel 651 (by decide) imm12 Rn Rt hRn hRt dispatch noEret D x)
      nextPlaced obligations

#print axioms step
end LoopNative.StrbU
