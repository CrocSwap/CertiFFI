import Bridge.CruxGenGuarded.EntryClassNext
import Uget.Chain
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.ChainInv
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false

/-! Plan-indexed run invariant for the post-entry chain. At plan index k the
state carries StepPins, F6/VHE features, E11 MDE/HDE, the canonical invariant at
its beforeFetchState, HookQuiet with budget `budget - k`, no pending GIC and the
placed PC `base + offset k`. `plan_step` turns one plan step (the class word,
its ClassTailAt for EVERY state satisfying the invariant, and the per-state
fetch obligations) into a `Uget.Chain.Step`, so `ModelRunView.invariant_prefixes`
and `E17Run.e17_along_steps` apply directly. -/

structure ChainInv {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (k : Nat) (x : NativeState) : Prop where
  pins : StepPins x
  features : EntryFeatures x.regs
  debug : E11Debug.E11CheckDebug x.regs
  current : CurrentS1At spec config rows (ArmBridge.CruxGenGuarded.beforeFetchState x)
  quiet : HookQuiet (budget - k) x
  gic : x.regs.bank_Option_InterruptID .__GIC_Pending = none
  pc : x.regs._PC = base + offset k

/-- Per-state fetch obligations of plan step k (stated for EVERY state that
satisfies the invariant; discharged by the plan producer from checks,
C9 placement and loader facts, never by the public caller). -/
structure FetchObligations {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (w : BitVec 32) (x : NativeState) : Type where
  queryOf : AccessDescriptor → AccessQuery
  rawOf : ∀ acc, (queryOf acc).request.raw = acc
  vaOf : ∀ acc, (queryOf acc).va = x.regs._PC
  mmio : MappedNotMMIO mapping x.regs._PC
  present : MappedBytesPresent mapping x.regs._PC x.mem
  perAcc : ∀ acc, ActualIFetchAcc (ArmBridge.CruxGenGuarded.beforeFetchState x) acc →
    domain (queryOf acc) ∧ ∃ data : S1AccessData spec config rows (queryOf acc),
      CurrentS1AccessAt spec config rows mapping (queryOf acc) data
        (ArmBridge.CruxGenGuarded.beforeFetchState x)
  code : ∀ acc leafLevel view faultOut (address : AddressDescriptor) translated (w' : BitVec 32),
    CleanTranslateResultFields spec config rows mapping (queryOf acc) leafLevel view
      (fetchPre (ArmBridge.CruxGenGuarded.beforeFetchState x)) (faultOut, address) translated →
    (∀ i < 4, translated.mem[address.paddress.address.toNat + i]? = some (w'.extractLsb' (8 * i) 8)) →
    w' = w

run_cmd do
  IO.eprintln "CURRENT_DECL ChainInv.plan_step"
  (← IO.getStderr).flush

theorem plan_step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (room : k < budget)
    (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (next : NativeState → BitVec 64)
    (tail : ∀ x, ChainInv spec config rows base offset budget k x →
      ClassTailAt real w writes K x (next x))
    (nextPlaced : ∀ x, ChainInv spec config rows base offset budget k x →
      next x = base + offset (k + 1))
    (obligations : ∀ x, ChainInv spec config rows base offset budget k x →
      FetchObligations spec config rows mapping w x) :
    Uget.Chain.Step real (ChainInv spec config rows base offset budget k)
      (ChainInv spec config rows base offset budget (k + 1)) := by
  intro x inv
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic⟩ :=
    entry_class_next_at real spec config rows mapping w writes K x inv.pins (next x) (offset (k + 1))
      (tail x inv) inv.gic inv.features inv.debug (budget - (k + 1)) hq base (offset k) inv.pc page aligned
      (nextPlaced x inv) inv.current ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  exact ⟨fin, run, pins, features, debug, current, quiet, gic, pc⟩

#print axioms plan_step
end ArmBridge.CruxGenGuarded.ChainInv
