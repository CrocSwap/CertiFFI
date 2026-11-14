-- Memory (d200 P3): mem_nextG with extraNext given the step run (the shape ArmCertPipe.stepG supplies). Copy of NextG:
-- the generic MEMORY step preservation over ArmCertPipe.ChainInvG, k → k + 1.
-- entry_mem_nextG + the config-frame fields (as RtShim2.plan_shim_mem / plan_shim_class did for ShimInv); the program
-- part `extra (k + 1) fin` comes from the caller (extraR14 preservation), given the step's Holds and payload.
import ArmCertMemPipe.RouteG
import HeapV2StepCerts.RawFetch
import HeapV2StepCerts.MemConfigFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
namespace ArmCertMemPipe
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmBridge.CruxGenGuarded.ChainInvV3 HeapV2StepCerts
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
theorem mem_nextG2 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (extra : Nat → NativeState → Prop) (k : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (us : List (RegBind.Reg × RegBind.Upd))
    (next : NativeState → BitVec 64) (X : NativeState → Prop) (D : Nat → Prop)
    (Pay : NativeState → NativeState → Prop)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x)
    (xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem → X f)
    (xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay f g → Pay x g)
    (tail : MemTailGAt real spec config rows (GCtx spec config rows mapping m X) D w writes K x (next x) us Pay)
    (nextPlaced : next x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping w x)
    (extraNext : ∀ fin : NativeState, modelStep real x = .ok () fin → extra (k + 1) fin) :
    ∃ fin, modelStep real x = .ok () fin ∧
      ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra (k + 1) fin ∧
      RegBind.Holds us x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)) ∧
      Pay x fin ∧ SysEq2 x.regs fin.regs := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, holds,
      ⟨written, wo, sep, inD⟩, pay, _, sys⟩ :=
    entry_mem_nextG real spec config rows mapping w writes K x inv.v2.v1.pins (next x) (offset (k + 1)) us m X D Pay
      tail inv.v2.v1.gic inv.v2.v1.features inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page
      aligned nextPlaced inv.v2.v1.current inv.v2.closed scope image loadBase inv.v2.placed separated codeD
      inv.v2.branch inv.raw inv.noUpd xferX xferPay inv.post2 inv.mode inv.debug inv.feat inv.dcache
      obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio obligations.present
      obligations.perAcc obligations.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩,
    RawFetch.raw_writes inv.raw wo sep, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache, extraNext fin run⟩,
    holds, ⟨written, wo, sep, inD⟩, pay, sys⟩
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms mem_nextG2
end ArmCertMemPipe
