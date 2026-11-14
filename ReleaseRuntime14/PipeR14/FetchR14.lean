-- d199 pipeline P3 input: runtime14's fetch obligations at any plan step, from ArmCertPipe.fetchG. The image is
-- the loader's reference image (R14E17.case_code_image: Binds + CodeBinds), the scope is the RX segment, the consumer map
-- is the case's R14E17.consumerMap (code disjunct of Permitted). The per-word C9 placement facts (contiguous, not MMIO)
-- and the table separation are the deployment statics (CodeStaticR14).
import ArmCertPipe.FetchG
import R14E17.Fetch
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.CruxGenGuarded.ChainInvV2 ArmBridge.CruxGenGuarded.EntryClassNext ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PipeR14

/-- The whole RX PT_LOAD: the real deployment's code scope. A program instance takes its scope as a parameter `sc` with
    `ScopeCovers sc` (the fetched code words are inside); the synthetic instance uses the closure code ranges. -/
def scope : Nat → Prop := fun o => R14E17.rxLo ≤ o ∧ o < R14E17.rxHi

/-- The scope contains every byte of every code word the 14 plans fetch. -/
def ScopeCovers (sc : Nat → Prop) : Prop := ∀ c ∈ R14E17.codeVAs, ∀ i < 4, sc (c.1 + i)

/-- DEPLOYMENT statics of the code side (per code word of the 14 cases). -/
structure CodeStaticR14 (sc : Nat → Prop) (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (footprint : Nat → Prop) : Prop where
  covers : ScopeCovers sc
  separated : ImageTableSeparated sc base mapping footprint
  contiguous : ∀ c ∈ R14E17.codeVAs, ImageWordContiguous mapping base c.1
  notMMIO : ∀ c ∈ R14E17.codeVAs, MappedNotMMIO mapping (MemReloc.imageAddress base c.1)

theorem scope_covers : ScopeCovers scope := by
  intro c m
  have ok := List.all_eq_true.1 R14E17.codeVAs_ok c m
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
  intro i hi; exact ⟨by omega, by omega⟩

/-- The synthetic deployment's scope: the bytes of the closure code words (the 336 bytes of R14Plan.codeRanges; every one
    is a fetched code word byte). -/
def closureScope : Nat → Prop := fun o => ∃ c ∈ R14E17.codeVAs, ∃ i < 4, o = c.1 + i

theorem closure_covers : ScopeCovers closureScope := fun c m i hi => ⟨c, m, i, hi, rfl⟩

/-- On the closure scope, the reference loader image holds the ELF's code bytes (from Binds + CodeBinds; no ELF-wide
    evaluation). -/
theorem closure_image (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : MemReloc.Word) (ifunc : Nat → MemReloc.Word) {o : Nat} (h : closureScope o) :
    ∃ c ∈ R14E17.codeVAs, ∃ i < 4, o = c.1 + i ∧
      referenceImageI bytes base ifunc o = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) := by
  obtain ⟨c, m, i, hi, rfl⟩ := h
  exact ⟨c, m, i, hi, rfl, R14E17.code_image bytes b cb base ifunc m i hi⟩

theorem inside_of_mem {sc : Nat → Prop} (cov : ScopeCovers sc) {c : Nat × Nat} (m : c ∈ R14E17.codeVAs) :
    ∀ i < 4, sc (c.1 + i) := cov c m

/-- Fetch obligations at a runtime14 step: case n, the step's code word c (entry-relative), offset k = entry + c.1. -/
def fetchR14 {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat) (table : Nat → Prop) (sc : Nat → Prop)
    (bytes : Array Nat) (b : Binds bytes R14Scoped.slices) (cb : R14E17.CodeBinds bytes)
    (base : BitVec 64) (ifunc : Nat → MemReloc.Word) (p : R14E17.Pins)
    (cs : CodeStaticR14 sc mapping base (rowsFootprint spec.imageRows).byte)
    {n : Nat} {accs : List R14E17.Access} {cws : List (Nat × Nat)} {entry : Nat} (hn : n < 14)
    (hcase : R14E17.caseMap n = some (accs, cws, entry)) {c : Nat × Nat} (member : c ∈ cws)
    (offset : Nat → BitVec 64) (budget k : Nat) (hoff : offset k = BitVec.ofNat 64 (entry + c.1))
    (x : NativeState)
    (inv : ChainInv2 spec config rows mapping (R14E17.consumerMap accs cws entry p base.toNat mapping table) sc
      (referenceImageI bytes base ifunc) base base offset budget k x) :
    FetchObligations spec config rows mapping (BitVec.ofNat 32 c.2) x :=
  have mv := R14E17.mem_codeVAs hn hcase member
  have pcImage : x.regs._PC = MemReloc.imageAddress base (entry + c.1) := by
    rw [inv.v1.pc, hoff]; rfl
  ArmCertPipe.fetchG spec config rows mapping _ sc (referenceImageI bytes base ifunc) base base offset budget k x
    inv (entry + c.1) (BitVec.ofNat 32 c.2) pcImage (inside_of_mem cs.covers mv) (cs.contiguous _ mv) (cs.notMMIO _ mv)
    cs.separated (R14E17.case_code_image bytes b cb base ifunc hn hcase member)
    (fun acc shape => Or.inr ⟨c, member, by
      rw [pcImage]; apply BitVec.eq_of_toNat_eq
      simp only [MemReloc.imageAddress, R14E17.codeVA, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega, rfl, shape⟩)

#print axioms closure_image
#print axioms fetchR14
end PipeR14
