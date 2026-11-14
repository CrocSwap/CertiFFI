-- Memory: straight-line StepCert2 over Core's ChainInv v2 (closed / placed are
-- now invariant fields), with scope := codeScope, image := HeapV2.image base, loadBase := base,
-- m := consumerMap pins base.toNat mapping table. Only the 4 static CodeStatic facts remain.
import HeapV2StepCerts.Carry
import Bridge.CruxGenGuarded.ChainInvV2
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace HeapV2StepCerts
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.HeapV2Compose ArmBridge.CruxGenGuarded.ChainInvV2

/-- The ChainInv v2 instance of the heap-v2 plan. -/
abbrev Inv2 {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (pins : HeapV2E17.Pins) (table : Nat → Prop) (base : BitVec 64) (budget k : Nat) (x : NativeState) : Prop :=
  ChainInv2 spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope
    (HeapV2.image base) base base offsetOf budget k x

def straight2 (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget k : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (off wordNat : Nat) (member : (off, wordNat) ∈ HeapV2Plan.codeWords)
    (here : offsetOf k = BitVec.ofNat 64 (0x10278 + off))
    (succ : offsetOf (k + 1) = BitVec.ofNat 64 (0x10278 + off + 4))
    (w : BitVec 32) (wordEq : w = BitVec.ofNat 32 wordNat)
    (writes : NativeEntry.Effects.Writes) (K : Int) (tail : ∀ x, ClassTail real w writes K x) :
    StepCert2 real spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table) codeScope
      (HeapV2.image base) base base offsetOf budget k where
  word := w
  writes := writes
  see := K
  next := fun x => x.regs._PC + 4#64
  tail := fun x _ => (tail x).at
  placedNext := fun x inv => by
    rw [inv.v1.pc, here, succ, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  fetch := fun x inv =>
    have pcImage : x.regs._PC = MemReloc.imageAddress base (HeapV2.entryOffset + off) := by
      rw [inv.v1.pc, here]; rfl
    have pcCode : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs._PC =
        HeapV2E17.codeVA base.toNat (off, wordNat).1 := by
      show x.regs._PC = _
      rw [pcImage, MemReloc.imageAddress, add_ofNat]
      simp only [HeapV2E17.codeVA, Nat.add_assoc]
    have facts := ArmBridge.CruxGenGuarded.EntryActualFetch.before_fetch_facts x
      (NativeEntryTail.EntryPins.of_scalar x inv.v1.pins) inv.v1.features inv.v1.debug
    have el := facts.2.1
    have mode := facts.2.2.2.2.2.2.1
    have ep := NativeEntryTail.EntryPins.of_scalar x inv.v1.pins
    have rme : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.FeatureImpl[232] = false := by
      show x.regs.FeatureImpl[232] = false; simpa using ep.rme
    have nrw : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.PSTATE.nRW = 0#1 := by
      show x.regs.PSTATE.nRW = 0#1; simpa using ep.nrw
    { queryOf := fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩
      rawOf := fun _ => rfl
      vaOf := fun _ => rfl
      mmio := by rw [pcImage]; exact static.notMMIO _ member
      present := mapped_bytes_present_of_image_on inv.placed pcImage
        (static.inside _ member) (static.contiguous _ member)
      perAcc := HeapV2E17.fetch_per_acc_el0 spec config rows mapping pins base.toNat table
        member pcCode inv.closed rme nrw inv.v1.features.b3 inv.v1.features.a3 el mode.ns
      code := by
        intro acc leafLevel view faultOut address translated w' clean bytes
        rw [wordEq]
        exact HeapV2E17.fetch_code spec config rows mapping (pre := ArmBridge.CruxGenGuarded.beforeFetchState x)
          member (fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩) (fun _ => rfl) inv.placed static.separated
          pcImage (static.inside _ member) (static.contiguous _ member) acc leafLevel view faultOut address
          translated w' clean bytes }

end HeapV2StepCerts
