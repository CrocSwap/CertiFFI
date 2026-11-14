-- (via cfab): from handoff draft ShimFetch.lean.draft, compiled as TranslateShim.ShimFetch.
-- the shim's fetch obligations (Core FetchObligations at every shim
-- state), mirroring Memory's memFetch for the body: perAcc from closed membership for consumerMapShim's code
-- disjunct, code from HeapV2ShimImage.shim_image via c9_fetch_code, present /
-- mmio from C9 placement and the shim's static code facts (ShimCodeStatic, the shim analogue of CodeStatic).
import HeapV2StepCerts.MemStepV3
import ArmCertTranslateModel.HeapV2ShimImage
import ArmCertWalk.IFetchElSs
import RtShim2.ShimInv
import Bridge.CruxGenGuarded.ConsumerMapShim
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmBridge.CruxGenGuarded.HeapV2Compose ArmBridge.CruxGenGuarded.ChainInvV2
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
namespace RtDit.ShimFetch
open HeapV2StepCerts HeapV2StepCerts.MemNext

/-- Static code facts of the shim's 11 words at load base `base` (deployment checks). -/
structure ShimCodeStatic (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (scope : Nat → Prop)
    (table : Nat → Prop) : Prop where
  separated : ImageTableSeparated scope base mapping table
  inside : ∀ code ∈ HeapV2ShimPlan.codeWords, ∀ i < 4, scope (HeapV2ShimPlan.shimOffset + code.1 + i)
  contiguous : ∀ code ∈ HeapV2ShimPlan.codeWords, ImageWordContiguous mapping base (HeapV2ShimPlan.shimOffset + code.1)
  notMMIO : ∀ code ∈ HeapV2ShimPlan.codeWords,
    MappedNotMMIO mapping (MemReloc.imageAddress base (HeapV2ShimPlan.shimOffset + code.1))

theorem shim_fetch_per_acc {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (S : Nat × Nat × Int × Nat × Bool → Prop) (p : HeapV2E17.Pins) (base : Nat) (table : Nat → Prop)
    {pre : ArmCertWalk.State} {code : Nat × Nat}
    (member : code ∈ HeapV2ShimPlan.codeWords) (pcAt : pre.regs._PC = HeapV2E17.shimCodeVA base code.1)
    (closed : ClosedMembershipAt spec config rows mapping (HeapV2E17.consumerMapShim S p base mapping table) pre)
    (shape : ∀ acc, ActualIFetchAcc pre acc → acc.el = EL0 ∧ acc.ss = .SS_NonSecure) :
    ∀ acc, ActualIFetchAcc pre acc →
      domain ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩ ∧
      ∃ data : S1AccessData spec config rows ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩,
        CurrentS1AccessAt spec config rows mapping ⟨pre.regs._PC, ⟨acc, true⟩, 4⟩ data pre := by
  intro acc actual
  obtain ⟨acctype, read, write, tagaccess, transactional, nonfault, contiguous, firstfault, first, ls64⟩ :=
    actual_ifetch_flags actual
  obtain ⟨el, ss⟩ := shape acc actual
  have permitted : HeapV2E17.PermittedShim S p base pre.regs._PC acc 4 :=
    Or.inr (Or.inl ⟨code, member, pcAt, rfl, ⟨acctype, el, ss, read, write, tagaccess, transactional, nonfault,
      contiguous, firstfault, first, ls64⟩⟩)
  obtain ⟨⟨va, ⟨raw, aligned⟩, size⟩, hva, hraw, haligned, hsize, inDomain, data, current⟩ :=
    closed pre.regs._PC acc true 4 permitted
  simp only at hva hraw haligned hsize
  subst hva hraw haligned hsize
  exact ⟨inDomain, data, current⟩


/-- The fetch obligations at a shim state whose PC is the shim word at shim offset `off`. -/
def shimFetch {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (S : Nat × Nat × Int × Nat × Bool → Prop) (p : HeapV2E17.Pins) (table : Nat → Prop)
    (base : BitVec 64) (scope : Nat → Prop)
    (static : ShimCodeStatic mapping base scope (rowsFootprint spec.imageRows).byte)
    (offS : Nat → BitVec 64) (budget k : Nat)
    (off wordNat : Nat) (member : (off, wordNat) ∈ HeapV2ShimPlan.codeWords)
    (here : offS k = BitVec.ofNat 64 (0x10548 + off))
    (w : BitVec 32) (wordEq : w = BitVec.ofNat 32 wordNat) (x : NativeState)
    (inv : RtShim2.ShimInv spec config rows mapping (HeapV2E17.consumerMapShim S p base.toNat mapping table)
      scope (HeapV2.image base) base base offS budget k x) : FetchObligations spec config rows mapping w x :=
  have pcImage : x.regs._PC = MemReloc.imageAddress base (HeapV2ShimPlan.shimOffset + off) := by
    rw [inv.v2.v1.pc, here]; rfl
  have pcCode : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs._PC =
      HeapV2E17.shimCodeVA base.toNat (off, wordNat).1 := by
    show x.regs._PC = _
    rw [pcImage, MemReloc.imageAddress, add_ofNat]
    simp only [HeapV2E17.shimCodeVA, Nat.add_assoc]
  have facts := ArmBridge.CruxGenGuarded.EntryActualFetch.before_fetch_facts x
    (NativeEntryTail.EntryPins.of_scalar x inv.v2.v1.pins) inv.v2.v1.features inv.v2.v1.debug
  have el := facts.2.1
  have mode := facts.2.2.2.2.2.2.1
  have ep := NativeEntryTail.EntryPins.of_scalar x inv.v2.v1.pins
  have rme : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.FeatureImpl[232] = false := by
    show x.regs.FeatureImpl[232] = false; simpa using ep.rme
  have nrw : (ArmBridge.CruxGenGuarded.beforeFetchState x).regs.PSTATE.nRW = 0#1 := by
    show x.regs.PSTATE.nRW = 0#1; simpa using ep.nrw
  { queryOf := fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩
    rawOf := fun _ => rfl
    vaOf := fun _ => rfl
    mmio := by rw [pcImage]; exact static.notMMIO _ member
    present := mapped_bytes_present_of_image_on inv.v2.placed pcImage
      (static.inside _ member) (static.contiguous _ member)
    perAcc := shim_fetch_per_acc spec config rows mapping S p base.toNat table member pcCode inv.v2.closed
      (fun _ actual => ArmCertWalk.actual_ifetch_el_ss actual rme nrw inv.v2.v1.features.b3 inv.v2.v1.features.a3 el
        mode.ns)
    code := by
      intro acc leafLevel view faultOut address translated w' clean bytes
      rw [wordEq]
      exact ArmCert.Translate.Model.c9_fetch_code spec config rows mapping (ArmBridge.CruxGenGuarded.beforeFetchState x)
        (fun acc => ⟨x.regs._PC, ⟨acc, true⟩, 4⟩) (fun _ => rfl) inv.v2.placed static.separated pcImage
        (static.inside _ member) (static.contiguous _ member) (BitVec.ofNat 32 wordNat)
        (HeapV2ShimPlan.shim_image base member) acc leafLevel view faultOut address translated w' clean bytes }

end RtDit.ShimFetch
#print axioms RtDit.ShimFetch.shim_fetch_per_acc
#print axioms RtDit.ShimFetch.shimFetch
