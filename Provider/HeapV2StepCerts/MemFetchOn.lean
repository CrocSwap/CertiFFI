-- Memory: memFetch over certiffi's path-restricted consumer map consumerMapOn S
-- (code fetches stay permitted for every S, so the proof is memFetch's with the code disjunct of PermittedOn).
import HeapV2StepCerts.MemStepV3
import Bridge.CruxGenGuarded.ConsumerMapOn
import ArmCertTranslateModel.HeapV2FetchEl0
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.HeapV2Compose ArmBridge.CruxGenGuarded.ChainInvV2
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace HeapV2StepCerts.MemNext

/-- The fetch's per-descriptor access data from closed membership of a path-restricted map (code disjunct). -/
theorem fetch_per_acc_on {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (S : Nat × Nat × Int × Nat × Bool → Prop) (p : HeapV2E17.Pins) (base : Nat) (table : Nat → Prop)
    {pre : ArmCertWalk.State} {code : Nat × Nat}
    (member : code ∈ HeapV2Plan.codeWords) (pcAt : pre.regs._PC = HeapV2E17.codeVA base code.1)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMapOn S p base mapping table) pre)
    (shape : ∀ acc, ActualIFetchAcc pre acc → acc.el = EL0 ∧ acc.ss = .SS_NonSecure) :
    ∀ acc, ActualIFetchAcc pre acc →
      domain ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩ ∧
      ∃ data : S1AccessData spec config rows ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩,
        CurrentS1AccessAt spec config rows mapping ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩ data pre := by
  intro acc actual
  obtain ⟨acctype, read, write, tagaccess, transactional, nonfault, contiguous, firstfault, first, ls64⟩ :=
    actual_ifetch_flags actual
  obtain ⟨el, ss⟩ := shape acc actual
  have permitted : HeapV2E17.PermittedOn S p base pre.regs._PC acc 4 :=
    Or.inr ⟨code, member, pcAt, rfl, ⟨acctype, el, ss, read, write, tagaccess, transactional, nonfault,
      contiguous, firstfault, first, ls64⟩⟩
  obtain ⟨⟨va, ⟨raw, aligned⟩, size⟩, hva, hraw, haligned, hsize, inDomain, data, current⟩ :=
    closed pre.regs._PC acc true 4 permitted
  simp only at hva hraw haligned hsize
  subst hva hraw haligned hsize
  exact ⟨inDomain, data, current⟩

def memFetchOn (S : Nat × Nat × Int × Nat × Bool → Prop)
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (budget k : Nat) (pins : HeapV2E17.Pins) (table : Nat → Prop)
    (static : CodeStatic mapping base (rowsFootprint spec.imageRows).byte)
    (off wordNat : Nat) (member : (off, wordNat) ∈ HeapV2Plan.codeWords)
    (here : offsetOf k = BitVec.ofNat 64 (0x10278 + off))
    (w : BitVec 32) (wordEq : w = BitVec.ofNat 32 wordNat) (x : NativeState)
    (inv : ChainInv2 spec config rows mapping (HeapV2E17.consumerMapOn S pins base.toNat mapping table) codeScope
      (HeapV2.image base) base base offsetOf budget k x) : FetchObligations spec config rows mapping w x :=
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
    perAcc := fetch_per_acc_on spec config rows mapping S pins base.toNat table member pcCode inv.closed
      (fun _ actual => ArmCertWalk.actual_ifetch_el_ss actual rme nrw inv.v1.features.b3 inv.v1.features.a3 el mode.ns)
    code := by
      intro acc leafLevel view faultOut address translated w' clean bytes
      rw [wordEq]
      exact HeapV2E17.fetch_code spec config rows mapping (pre := ArmBridge.CruxGenGuarded.beforeFetchState x)
        member (fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩) (fun _ => rfl) inv.placed static.separated
        pcImage (static.inside _ member) (static.contiguous _ member) acc leafLevel view faultOut address
        translated w' clean bytes }


#print axioms fetch_per_acc_on
#print axioms memFetchOn
end HeapV2StepCerts.MemNext
