import Bridge.CruxGenGuarded.ChainInv
import Bridge.CruxGenGuarded.E17Run
import ArmCertTranslateModel.HeapV2Plan
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
namespace ArmBridge.CruxGenGuarded.HeapV2Compose
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/-! Relocation composition SKELETON for the heap-v2 image placed at load base `base`.
A path is a list of plan steps; step k is certified by the class tail of its word
for EVERY state satisfying the plan invariant, placement of its successor, and its
fetch obligations. From per-step certificates the whole path is a chain: the plan
invariant (hence StepPins/E11/CurrentS1At at every reached state) and E17
TranslationAgrees hold at every reached state of the ACTUAL model run. Instances:
non-branch classes via ClassTail.at; branches by their path outcome; BL via the
caller route; memory classes via the memory ClassTail (pending). -/

/-- One certified plan step (Type: fetch obligations carry the query map). -/
structure StepCert (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) : Type where
  word : BitVec 32
  writes : NativeEntry.Effects.Writes
  see : Int
  next : NativeState → BitVec 64
  tail : ∀ x, ChainInv spec config rows base offset budget k x →
    ClassTailAt real word writes see x (next x)
  placed : ∀ x, ChainInv spec config rows base offset budget k x → next x = base + offset (k + 1)
  fetch : ∀ x, ChainInv spec config rows base offset budget k x →
    FetchObligations spec config rows mapping word x

run_cmd do
  IO.eprintln "CURRENT_DECL HeapV2Compose.path_run"
  (← IO.getStderr).flush

/-- A certified path runs on the actual model: the plan invariant and E17 hold at
every reached state. -/
theorem path_run (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (agrees : ConsumerMapAgrees spec mapping m)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget len : Nat) (room : len ≤ budget)
    (page : base.toNat % 4096 = 0) (aligned : ∀ k, k < len → (offset k).toNat % 4 = 0)
    (certs : ∀ k, k < len → StepCert real spec config rows mapping base offset budget k)
    (entry : NativeState) (initial : ChainInv spec config rows base offset budget 0 entry)
    (closed : ∀ k x, ChainInv spec config rows base offset budget k x →
      ClosedMembershipAt spec config rows mapping m x) :
    ∀ k, k ≤ len →
      ChainInv spec config rows base offset budget k (stateAt real entry k) ∧
      ArmCert.Premises.TranslationAgreesV1.TranslationAgrees m (stateAt real entry k) := by
  have steps : ∀ k, k < len → Uget.Chain.Step real (ChainInv spec config rows base offset budget k)
      (ChainInv spec config rows base offset budget (k + 1)) := by
    intro k hk
    let c := certs k hk
    exact plan_step real spec config rows mapping base offset budget k (by omega) page (aligned k hk)
      c.word c.writes c.see c.next c.tail c.placed c.fetch
  have inv := invariant_prefixes real (ChainInv spec config rows base offset budget) len steps entry initial
  have e17 := E17Run.e17_along_steps real spec config rows mapping m agrees
    (ChainInv spec config rows base offset budget) len entry steps initial
    (fun k x h => ⟨NativeEntryTail.EntryPins.of_scalar x h.pins, h.features, h.debug, h.current⟩)
    closed
  exact fun k hk => ⟨inv k hk, e17 k hk⟩

/-! Heap-v2 binding to generated plan (HeapV2Plan.steps: (path, k, off, word)). -/

def normalSteps : List (Nat × Nat × Nat × Nat) := HeapV2Plan.steps.filter (·.1 = 0)

/-- Entry-relative code offset of normal-path step k (code at load base + 0x10278 + off). -/
def offsetOf (k : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (0x10278 + ((normalSteps.find? (·.2.1 = k)).map (·.2.2.1)).getD 0)

theorem normal_length : normalSteps.length = 358 := by decide +kernel

theorem normal_aligned : normalSteps.all (fun s => (0x10278 + s.2.2.1) % 4 == 0) = true := by
  decide +kernel

#print axioms path_run
#print axioms normal_length
#print axioms normal_aligned
end ArmBridge.CruxGenGuarded.HeapV2Compose
