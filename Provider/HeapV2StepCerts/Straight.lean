-- Memory: generic straight-line StepCert for the heap-v2 normal
-- path. A non-branch step k whose class tail holds for EVERY source state (all body/flag
-- Profiles on the normal path are empty) becomes a HeapV2Compose.StepCert from:
--   * plan facts decided per step (word in codeWords, offsetOf k / k+1 consecutive),
--   * ChainInv k x (pc, StepPins, EntryFeatures, E11, current) via Core's before_fetch_facts,
--   * the static/per-state placement facts ChainInv v1 does NOT carry, bundled in `CodeHyps`.
import Bridge.CruxGenGuarded.HeapV2Compose
import Bridge.CruxGenGuarded.EntryBodyTails
import Bridge.CruxGenGuarded.EntryFlagTails
import Bridge.CruxGenGuarded.EntryUmulhTails
import Bridge.CruxGenGuarded.EntrySbcsTails
import ArmCertTranslateModel.HeapV2FetchEl0
import ArmCertTranslateModel.C9Checks
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace HeapV2StepCerts
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.HeapV2Compose

/-- Facts ChainInv v1 cannot supply (candidates for ChainInv v2 / the plan producer).
Static: image/table separation, code scope, per-word mapping contiguity and not-MMIO.
Per-state: C9 placement of the image and closed membership at the before-fetch state. -/
structure CodeHyps {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget : Nat) : Type where
  scope : Nat → Prop
  pins : HeapV2E17.Pins
  table : Nat → Prop
  separated : ImageTableSeparated scope base mapping (rowsFootprint spec.imageRows).byte
  inside : ∀ code ∈ HeapV2Plan.codeWords, ∀ i < 4, scope (HeapV2.entryOffset + code.1 + i)
  contiguous : ∀ code ∈ HeapV2Plan.codeWords, ImageWordContiguous mapping base (HeapV2.entryOffset + code.1)
  notMMIO : ∀ code ∈ HeapV2Plan.codeWords,
    MappedNotMMIO mapping (MemReloc.imageAddress base (HeapV2.entryOffset + code.1))
  placed : ∀ k x, ChainInv spec config rows base offsetOf budget k x →
    MemReloc.ImageOn scope (HeapV2.image base) x base mapping
  closed : ∀ k x, ChainInv spec config rows base offsetOf budget k x →
    ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMap pins base.toNat mapping table)
      (ArmBridge.CruxGenGuarded.beforeFetchState x)

theorem add_ofNat (base : BitVec 64) (n : Nat) : base + BitVec.ofNat 64 n = BitVec.ofNat 64 (base.toNat + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Generic straight-line certificate. -/
def straight (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget k : Nat) (hyps : CodeHyps spec config rows mapping base budget)
    (off wordNat : Nat) (member : (off, wordNat) ∈ HeapV2Plan.codeWords)
    (here : offsetOf k = BitVec.ofNat 64 (0x10278 + off))
    (succ : offsetOf (k + 1) = BitVec.ofNat 64 (0x10278 + off + 4))
    (w : BitVec 32) (wordEq : w = BitVec.ofNat 32 wordNat)
    (writes : NativeEntry.Effects.Writes) (K : Int) (tail : ∀ x, ClassTail real w writes K x) :
    StepCert real spec config rows mapping base offsetOf budget k where
  word := w
  writes := writes
  see := K
  next := fun x => x.regs._PC + 4#64
  tail := fun x _ => (tail x).at
  placed := fun x inv => by
    rw [inv.pc, here, succ, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  fetch := fun x inv =>
    have pcImage : x.regs._PC = MemReloc.imageAddress base (HeapV2.entryOffset + off) := by
      rw [inv.pc, here]; rfl
    have pcCode : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs._PC =
        HeapV2E17.codeVA base.toNat (off, wordNat).1 := by
      show x.regs._PC = _
      rw [pcImage, MemReloc.imageAddress, add_ofNat]
      simp only [HeapV2E17.codeVA, Nat.add_assoc]
    have facts := ArmBridge.CruxGenGuarded.EntryActualFetch.before_fetch_facts x
      (NativeEntryTail.EntryPins.of_scalar x inv.pins) inv.features inv.debug
    have el := facts.2.1
    have mode := facts.2.2.2.2.2.2.1
    have ep := NativeEntryTail.EntryPins.of_scalar x inv.pins
    have rme : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.FeatureImpl[232] = false := by
      show x.regs.FeatureImpl[232] = false; simpa using ep.rme
    have nrw : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.PSTATE.nRW = 0#1 := by
      show x.regs.PSTATE.nRW = 0#1; simpa using ep.nrw
    { queryOf := fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩
      rawOf := fun _ => rfl
      vaOf := fun _ => rfl
      mmio := by rw [pcImage]; exact hyps.notMMIO _ member
      present := mapped_bytes_present_of_image_on (hyps.placed k x inv) pcImage
        (hyps.inside _ member) (hyps.contiguous _ member)
      perAcc := HeapV2E17.fetch_per_acc_el0 spec config rows mapping hyps.pins base.toNat hyps.table
        member pcCode (hyps.closed k x inv) rme nrw inv.features.b3 inv.features.a3 el mode.ns
      code := by
        intro acc leafLevel view faultOut address translated w' clean bytes
        rw [wordEq]
        exact HeapV2E17.fetch_code spec config rows mapping (pre := ArmBridge.CruxGenGuarded.beforeFetchState x)
          member (fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩) (fun _ => rfl) (hyps.placed k x inv) hyps.separated
          pcImage (hyps.inside _ member) (hyps.contiguous _ member) acc leafLevel view faultOut address
          translated w' clean bytes }

end HeapV2StepCerts
