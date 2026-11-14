import Bridge.CruxGenGuarded.ClassNextV2
import Bridge.CruxGenGuarded.ChainInv
import Bridge.CruxGenGuarded.E17Run
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.ChainInvV2
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ClosedChain
open CertiFFI.Prog.Generic.ModelRunView
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! ChainInv v2 = v1 + the three facts the plan composition needs per state
(Memory 831b103f/carry): closed query membership for the plan's consumer map at
beforeFetchState x, code-image placement (ImageOn over the code scope), and the
PA-free branch platform profile. `plan_step2` preserves it across one
actual fixed-class step; `path_run2` composes certified steps into ChainInv v2 and
E17 at every reached state. -/

structure ChainInv2 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat) (x : NativeState) : Prop where
  v1 : ChainInv spec config rows base offset budget k x
  closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState x)
  placed : MemReloc.ImageOn scope image x loadBase mapping
  branch : Crypto.BranchV2.BranchPinsV2PA x

/-- Closed membership reads only translation registers, which beforeFetchState does not touch. -/
theorem closed_of_before_fetch {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap} (x : NativeState)
    (h : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState x)) :
    ClosedMembershipAt spec config rows mapping m x := by
  refine closed_of_fields h ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (disch := decide) only [ArmBridge.CruxGenGuarded.beforeFetchState, RegMap.set_ne]

run_cmd do
  IO.eprintln "CURRENT_DECL ChainInvV2.plan_step2"
  (← IO.getStderr).flush

theorem plan_step2 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (room : k < budget)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (next : NativeState → BitVec 64)
    (tail : ∀ x, ChainInv2 spec config rows mapping m scope image loadBase base offset budget k x →
      ClassTailAt real w writes K x (next x))
    (nextPlaced : ∀ x, ChainInv2 spec config rows mapping m scope image loadBase base offset budget k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv2 spec config rows mapping m scope image loadBase base offset budget k x →
      FetchObligations spec config rows mapping w x) :
    Uget.Chain.Step real (ChainInv2 spec config rows mapping m scope image loadBase base offset budget k)
      (ChainInv2 spec config rows mapping m scope image loadBase base offset budget (k + 1)) := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed, bp⟩ :=
    ClassNextV2.entry_class_next_v2 real spec config rows mapping w writes K x inv.v1.pins (next x)
      (offset (k + 1)) (tail x inv) inv.v1.gic inv.v1.features inv.v1.debug (budget - (k + 1)) hq base
      (offset k) inv.v1.pc page aligned (nextPlaced x inv) inv.v1.current m inv.closed scope image loadBase
      inv.placed separated inv.branch ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  exact ⟨fin, run, ⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp⟩⟩

/-- One certified plan step for ChainInv v2. -/
structure StepCert2 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) : Type where
  word : BitVec 32
  writes : NativeEntry.Effects.Writes
  see : Int
  next : NativeState → BitVec 64
  tail : ∀ x, ChainInv2 spec config rows mapping m scope image loadBase base offset budget k x →
    ClassTailAt real word writes see x (next x)
  placedNext : ∀ x, ChainInv2 spec config rows mapping m scope image loadBase base offset budget k x →
    next x = base + offset (k + 1)
  fetch : ∀ x, ChainInv2 spec config rows mapping m scope image loadBase base offset budget k x →
    FetchObligations spec config rows mapping word x

run_cmd do
  IO.eprintln "CURRENT_DECL ChainInvV2.path_run2"
  (← IO.getStderr).flush

theorem path_run2 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (agrees : ConsumerMapAgrees spec mapping m)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget len : Nat) (room : len ≤ budget)
    (page : base.toNat % 4096 = 0) (aligned : ∀ k, k < len → (offset k).toNat % 4 = 0)
    (certs : ∀ k, k < len →
      StepCert2 real spec config rows mapping m scope image loadBase base offset budget k)
    (entry : NativeState)
    (initial : ChainInv2 spec config rows mapping m scope image loadBase base offset budget 0 entry) :
    ∀ k, k ≤ len →
      ChainInv2 spec config rows mapping m scope image loadBase base offset budget k (stateAt real entry k) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees m (stateAt real entry k) := by
  have steps : ∀ k, k < len → Uget.Chain.Step real
      (ChainInv2 spec config rows mapping m scope image loadBase base offset budget k)
      (ChainInv2 spec config rows mapping m scope image loadBase base offset budget (k + 1)) := by
    intro k hk
    let c := certs k hk
    exact plan_step2 real spec config rows mapping m scope image loadBase separated base offset budget k
      (by omega) page (aligned k hk) c.word c.writes c.see c.next c.tail c.placedNext c.fetch
  have inv := invariant_prefixes real
    (ChainInv2 spec config rows mapping m scope image loadBase base offset budget) len steps entry initial
  have e17 := E17Run.e17_along_steps real spec config rows mapping m agrees
    (ChainInv2 spec config rows mapping m scope image loadBase base offset budget) len entry steps initial
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.v1.pins, h.v1.features, h.v1.debug, h.v1.current⟩)
    (fun k x h => closed_of_before_fetch x h.closed)
  exact fun k hk => ⟨inv k hk, e17 k hk⟩

#print axioms closed_of_before_fetch
#print axioms plan_step2
#print axioms path_run2
end ArmBridge.CruxGenGuarded.ChainInvV2
