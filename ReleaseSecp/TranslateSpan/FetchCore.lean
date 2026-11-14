-- Actual fetch obligations from the three branch-independent fields.
import Bridge.CruxGenGuarded.ChainInvV2
import ArmCertTranslateModel.C9FetchBinding
import ArmCertWalk.IFetchElSs
import ArmCertWalk.AccessTransfer
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace TranslateSpan.CurrentMTE2

def fetchG {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget k : Nat) (x : NativeState)
    (inv : ChainInv spec config rows base offset budget k x)
    (closed : ClosedMembershipAt spec config rows mapping m (ArmBridge.CruxGenGuarded.beforeFetchState x))
    (placed : MemReloc.ImageOn scope image x loadBase mapping)
    (off : Nat) (w : BitVec 32)
    (pcImage : x.regs._PC = MemReloc.imageAddress loadBase off)
    (inside : ∀ i < 4, scope (off + i)) (contiguous : ImageWordContiguous mapping loadBase off)
    (mmio : MappedNotMMIO mapping (MemReloc.imageAddress loadBase off))
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (imageWord : ∀ i < 4, image (off + i) = some (w.extractLsb' (8 * i) 8))
    (permit : ∀ acc, FetchShape acc → m.permitted x.regs._PC acc true 4) :
    FetchObligations spec config rows mapping w x :=
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
    mmio := by rw [pcImage]; exact mmio
    present := mapped_bytes_present_of_image_on placed pcImage inside contiguous
    perAcc := by
      intro acc actual
      obtain ⟨acctype, read, write, tagaccess, transactional, nonfault, contiguous', firstfault, first, ls64⟩ :=
        actual_ifetch_flags actual
      obtain ⟨hel, hss⟩ := actual_ifetch_el_ss actual rme nrw inv.features.b3 inv.features.a3 el mode.ns
      have permitted : m.permitted (ArmBridge.CruxGenGuarded.beforeFetchState x).regs._PC acc true 4 :=
        permit acc ⟨acctype, hel, hss, read, write, tagaccess, transactional, nonfault, contiguous', firstfault,
          first, ls64⟩
      obtain ⟨⟨va, ⟨raw, aligned⟩, size⟩, hva, hraw, haligned, hsize, inDomain, data, current⟩ :=
        closed _ acc true 4 permitted
      simp only at hva hraw haligned hsize
      subst hva hraw haligned hsize
      exact ⟨inDomain, data, current⟩
    code := c9_fetch_code spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState x) _ (fun _ => rfl)
      placed separated pcImage inside contiguous w imageWord }

#print axioms fetchG
end TranslateSpan.CurrentMTE2
