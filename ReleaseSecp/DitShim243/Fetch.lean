import DitShim243.Geometry
import DefaultCurrent
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ReleaseProfile
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace DitShim243.Fetch

/-- Static ELF/code and consumer bindings. All fields concern the deployed
image and declared accesses; none assumes an execution or a later fetch. -/
structure CodeFacts {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (base : BitVec 64)
    (start : Nat) (word : Nat → BitVec 32) : Prop where
  inside : ∀ j, j < 11 → ∀ i < 4, scope (start + 4 * j + i)
  contiguous : ∀ j, j < 11 → ImageWordContiguous mapping base (start + 4 * j)
  mmio : ∀ j, j < 11 → MappedNotMMIO mapping (MemReloc.imageAddress base (start + 4 * j))
  separated : ImageTableSeparated scope base mapping (rowsFootprint spec.imageRows).byte
  imageWord : ∀ j, j < 11 → ∀ i < 4, image (start + 4 * j + i) = some ((word j).extractLsb' (8 * i) 8)
  permit : ∀ j, j < 11 → ∀ acc, FetchShape acc →
    m.permitted (base + Geometry.shimPC start j) acc true 4

def fetch {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (base : BitVec 64)
    (start : Nat) (word : Nat → BitVec 32) (code : CodeFacts spec mapping m scope image base start word)
    (offset : Nat → BitVec 64) (budget k j : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue)
    (bound : j < 11) (placed : offset k = Geometry.shimPC start j)
    (x : NativeState) (inv : DefaultCurrent.CurrentInv spec config rows mapping m scope image base base offset budget k catalogue x) :
    FetchObligations spec config rows mapping (word j) x := by
  have pc : x.regs._PC = MemReloc.imageAddress base (start + 4 * j) := by
    rw [inv.v1.pc, placed]; rfl
  exact DefaultCurrent.fetchG spec config rows mapping m scope image base base offset budget k catalogue x inv
    (start + 4 * j) (word j) pc (code.inside j bound) (code.contiguous j bound)
    (code.mmio j bound) code.separated (code.imageWord j bound)
    (fun acc shape => by rw [inv.v1.pc, placed]; exact code.permit j bound acc shape)

#print axioms fetch
end DitShim243.Fetch
