-- Event-bearing continuation, retaining the common current invariant.
import DefaultRuntimeEntryMem
import DefaultCurrent

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.ChainInvV3 ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCertMemPipe ReleaseProfile.DefaultMemTail HeapV2StepCerts
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000

namespace ReleaseProfile.DefaultRuntime

/-- The checked result of a decoded memory step, with the facts needed to
    advance the program's symbolic state and event trace together. -/
structure MemoryStep {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (cost : Nat)
    (us : List (RegBind.Reg × RegBind.Upd)) (D : Nat → Prop)
    (Pay : NativeState → NativeState → Prop)
    (records : List (Option ArmCertCTOrdered.OrderedEventV2.Record)) (x fin : NativeState) : Prop where
  current : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k + 1) catalogue fin
  regs : RegBind.Holds us x fin
  writes : ∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
    Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)
  pay : Pay x fin
  sys : SysEq2 x.regs fin.regs
  z : fin.regs._Z = x.regs._Z
  dit : fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT
  events : StepEvents.EvShape spec mapping records x fin
  choice : ∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ cost

#check "CURRENT_DECL mem_route"
theorem mem_route (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (cost : Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int) (us : List (RegBind.Reg × RegBind.Upd))
    (next : NativeState → BitVec 64) (X : NativeState → Prop) (D : Nat → Prop)
    (Pay : NativeState → NativeState → Prop)
    (dataOf : NativeState → List (Option ArmCertCTOrdered.OrderedEventV2.Record))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (codeD : ImageTableSeparated scope loadBase mapping D)
    (x : NativeState) (inv : DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget k catalogue x)
    (allowed : NativeMteTagCheck.TagStatusOK x)
    (xferData : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → dataOf f = dataOf x)
    (xferX : ∀ f : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem → X f)
    (xferPay : ∀ f g : NativeState, f.regs.gpr = x.regs.gpr → f.regs.SP_EL0 = x.regs.SP_EL0 → f.mem = x.mem →
      Flags.nzcv f.regs = Flags.nzcv x.regs → Pay f g → Pay x g)
    (tail : DefaultMemTail.MemTailAt real spec config rows (GCtxDefault spec config rows mapping m X catalogue) D w writes K x (next x) us (fun f g => Pay f g ∧ EvD spec (dataOf f) f g) cost)
    (nextPlaced : next x = base + offset (k + 1))
    (obligations : FetchObligations spec config rows mapping w x) (hv : writes.vector = false)
    (hd : writes.dit = false := by rfl) :
    ∃ fin, modelStep real x = .ok () fin ∧
      DefaultCurrent.CurrentInv spec config rows mapping m scope image loadBase base offset budget (k+1) catalogue fin ∧
      RegBind.Holds us x fin ∧
      (∃ written : Nat → Prop, WritesOnly written (fun a => x.mem[a]?) (fun a => fin.mem[a]?) ∧
        Separated (rowsFootprint spec.imageRows).byte written ∧ (∀ a, written a → D a)) ∧
      Pay x fin ∧ SysEq2 x.regs fin.regs ∧ fin.regs._Z = x.regs._Z ∧ fin.regs.PSTATE.DIT = x.regs.PSTATE.DIT ∧
      ArmBridge.CruxGenGuarded.StepEvents.EvShape spec mapping (dataOf x) x fin ∧
      (∃ draws, NativeMteTagCheck.ChoiceDelta x fin draws ∧ draws ≤ cost) := by
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  obtain ⟨fin, run, pins, quiet, cur, pc, debug, feat, gic, closed, placed,
      holds, ⟨written, wo, sep, inD⟩, pay, _, sys, br, tag, dit, _, z, ev, choice⟩ :=
    DefaultRuntimeEntryMem.entry_mem_next_choice real spec config rows mapping w writes K x inv.v1.pins
      (next x) (offset (k + 1)) us m X D Pay catalogue cost dataOf xferData nodup
      (GCtxDefault spec config rows mapping m X catalogue)
      (fun f ctx _ => ⟨ctx.closed, ctx.prog, ctx.raw, ctx.noUpd, ctx.post, ctx.current,
        ctx.controls, ctx.allowed, ctx.mode, ctx.debug, ctx.feat, ctx.dcache⟩)
      tail inv.v1.gic inv.v1.features inv.v1.debug (budget - (k + 1)) hq base (offset k) inv.v1.pc page
      aligned nextPlaced inv.v1.current inv.closed scope image loadBase inv.placed separated codeD
      inv.raw inv.noUpd xferX xferPay inv.post inv.mode inv.controls allowed inv.debug inv.feat inv.dcache
      obligations.queryOf obligations.rawOf obligations.vaOf obligations.mmio obligations.present
      obligations.perAcc obligations.code
  have branch := TranslateSpan.BranchMTE2.pins_step x fin inv.branch sys pins br
  refine ⟨fin, run, ⟨⟨pins, feat, debug, cur, quiet, gic, pc⟩, closed, placed, branch,
    RawFetch.raw_writes inv.raw wo sep, ?_, DefaultCurrent.postFrame sys inv.post,
    MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_, MemConfigFrame.dcache sys.sctlr inv.dcache,
    DefaultActionControls.controls_of_sys inv.controls sys tag⟩, holds, ⟨written, wo, sep, inD⟩, pay, sys, z hv, dit hd, ev, choice⟩
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms mem_route
end ReleaseProfile.DefaultRuntime
