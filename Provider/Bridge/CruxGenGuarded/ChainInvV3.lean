import Bridge.CruxGenGuarded.ChainInvV2
import Bridge.CruxGenGuarded.ClassNextV3
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.MemConfigFrame
import Bridge.CruxGenGuarded.E17Run
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.ChainInvV3
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
open ArmCert.HookQuiet.V0 (HookQuiet)
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! ChainInv v3 = v2 + the facts memory-class steps need at every state (Memory c/c3): the
register binding to the plan's symbolic pins, data-byte presence, the raw table image,
no-update rows for data-shaped descriptors, and the
static memory-access configuration. `plan_step3_class` preserves it across one actual
non-memory fixed-class step whose value-carrying tail updates registers per `upds k`. -/

structure ChainInv3 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins)
    (k : Nat) (x : NativeState) : Prop where
  v2 : ChainInv2 spec config rows mapping m scope image loadBase base offset budget k x
  regBind : HeapV2StepCerts.RegBind.RegBind p k x
  present : HeapV2StepCerts.C3.DataPresent p mapping x
  raw : RawImageAt spec.imageRows x.mem
  noUpd : ∀ (wr : Bool) (acc : AccessDescriptor), DataShape wr acc →
    NoUpdateRows {spec.params with haft := hostHAFT x.regs} acc spec.imageRows = true
  post2 : MemM1.MemReadD2.PostRegs2 x.regs
  mode : HostEL0ModeAt x.regs
  debug : ExistingE11DebugAt x.regs
  feat : x.regs.FeatureImpl[7] = true ∧ x.regs.FeatureImpl[3] = false ∧
    x.regs.FeatureImpl[227] = false ∧ x.regs.FeatureImpl[111] = true
  dcache : currentDCache x.regs = true

theorem hostHAFT_eq {r r' : Regs} (h : SysEq2 r r') : hostHAFT r' = hostHAFT r := by
  simp only [hostHAFT, hostHA, hostTCR2Enabled, h.feat, h.tcr, h.tcr2, h.scr]
  rfl

run_cmd do
  IO.eprintln "CURRENT_DECL ChainInvV3.plan_step3_class"
  (← IO.getStderr).flush

theorem plan_step3_class (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (next : NativeState → BitVec 64)
    (tail : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      HeapV2StepCerts.RegVal.ClassTailVAt real w writes K x (next x) (HeapV2StepCerts.RegBind.upds k))
    (nextPlaced : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      FetchObligations spec config rows mapping w x) :
    Uget.Chain.Step real (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)) := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v2.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp, holds, finMem, sys⟩ :=
    ClassNextV3.entry_class_next_v3 real spec config rows mapping w writes K x inv.v2.v1.pins (next x)
      (offset (k + 1)) (HeapV2StepCerts.RegBind.upds k) (tail x inv) inv.v2.v1.gic inv.v2.v1.features
      inv.v2.v1.debug (budget - (k + 1)) hq base (offset k) inv.v2.v1.pc page aligned (nextPlaced x inv)
      inv.v2.v1.current m inv.v2.closed scope image loadBase inv.v2.placed separated inv.v2.branch
      inv.raw inv.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩,
    HeapV2StepCerts.RegBind.carry_step hk holds inv.regBind, ?_, ?_, ?_,
    HeapV2StepCerts.MemConfigFrame.post2 sys.feat sys.el sys.nrw sys.scr sys.hcr sys.sctlr sys.spe inv.post2,
    HeapV2StepCerts.MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr inv.mode,
    HeapV2StepCerts.MemConfigFrame.debug sys.mdscr sys.hde inv.debug, ?_,
    HeapV2StepCerts.MemConfigFrame.dcache sys.sctlr inv.dcache⟩⟩
  · intro e he n hn i hi; rw [finMem]; exact inv.present e he n hn i hi
  · rw [finMem]; exact inv.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact inv.noUpd wr acc hs
  · rw [sys.feat]; exact inv.feat

#print axioms hostHAFT_eq
#print axioms plan_step3_class

run_cmd do
  IO.eprintln "CURRENT_DECL ChainInvV3.step3_of_cert"
  (← IO.getStderr).flush

/-- A ChainInv v2 step certificate plus a value-carrying tail for the same word lifts to a
ChainInv v3 step (fetch obligations and placement read through `ChainInv3.v2`). -/
theorem step3_of_cert (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (room : k < budget) (hk : k < 358)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (c : StepCert2 real spec config rows mapping m scope image loadBase base offset budget k)
    (tailV : ∀ x, ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k x →
      HeapV2StepCerts.RegVal.ClassTailVAt real c.word c.writes c.see x (c.next x)
        (HeapV2StepCerts.RegBind.upds k)) :
    Uget.Chain.Step real (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)) :=
  plan_step3_class real spec config rows mapping m scope image loadBase separated base offset budget p k
    room hk page aligned c.word c.writes c.see c.next tailV (fun x h => c.placedNext x h.v2)
    (fun x h => c.fetch x h.v2)

#print axioms step3_of_cert

run_cmd do
  IO.eprintln "CURRENT_DECL ChainInvV3.path_run3"
  (← IO.getStderr).flush

/-- Any family of ChainInv v3 steps composes on the ACTUAL model run: ChainInv3 and E17
TranslationAgrees hold at every reached state. -/
theorem path_run3 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap) (agrees : ConsumerMapAgrees spec mapping m)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (len : Nat)
    (steps : ∀ k, k < len → Uget.Chain.Step real
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k)
      (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p (k + 1)))
    (entry : NativeState)
    (initial : ChainInv3 spec config rows mapping m scope image loadBase base offset budget p 0 entry) :
    ∀ k, k ≤ len →
      ChainInv3 spec config rows mapping m scope image loadBase base offset budget p k (stateAt real entry k) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees m (stateAt real entry k) := by
  have inv := invariant_prefixes real
    (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p) len steps entry initial
  have e17 := E17Run.e17_along_steps real spec config rows mapping m agrees
    (ChainInv3 spec config rows mapping m scope image loadBase base offset budget p) len entry steps initial
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.v2.v1.pins, h.v2.v1.features, h.v2.v1.debug,
      h.v2.v1.current⟩)
    (fun k x h => ChainInvV2.closed_of_before_fetch x h.v2.closed)
  exact fun k hk => ⟨inv k hk, e17 k hk⟩

#print axioms path_run3
end ArmBridge.CruxGenGuarded.ChainInvV3
