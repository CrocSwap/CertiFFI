import TranslateSpan.SecpDefaultEntry
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
open ArmCert.Translate.Model.StaticPie ArmCertValue ArmCertPipe NativeAccess
open TranslateSpan TranslateSpan.SecpRawDeployment
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace DitShim243.RawFetch
def fetch {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (p : Plan) (raw : CheckedTopology.Raw)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) {catalogue : NativeMteTagCheck.ControlCatalogue} (budget : Nat)
    (table : spec.imageRows = raw.imageRows) (layout : LayoutFacts p raw mapping base entry)
    (image : MemReloc.Image)
    (imageWords : ∀ c ∈ p.code, ∀ i < 4, image (c.1 + i) =
      some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8))
    (k : Nat) (x : NativeState)
    (inv : DefaultMTE2.Core spec config rows mapping (consumer p raw mapping base entry)
      (· ∈ codeOffsets p) image base base (offset p) budget (profile entry) catalogue k x)
    (c : Nat × Nat) (member : c ∈ p.code)
    (pc : x.regs._PC = MemReloc.imageAddress base c.1) :
    FetchObligations spec config rows mapping (BitVec.ofNat 32 c.2) x := by
  have separated : ImageTableSeparated (· ∈ codeOffsets p) base mapping
      (rowsFootprint spec.imageRows).byte := by
    rw [table]
    intro o pa inside mapped inTable
    exact layout.separated o pa inside mapped (Or.inl inTable)
  refine CurrentMTE2.fetchG spec config rows mapping (consumer p raw mapping base entry)
    (· ∈ codeOffsets p) image base base (offset p) budget k x
    inv.v1 inv.closed inv.placed c.1 (BitVec.ofNat 32 c.2) pc ?_
    (layout.codeWords c member).1 (layout.codeWords c member).2 separated
    (imageWords c member) ?_
  · intro i bound
    change c.1 + i ∈ p.code.flatMap (fun w => (List.range 4).map (w.1 + ·))
    exact List.mem_flatMap.mpr ⟨c, member, List.mem_map.mpr ⟨i, List.mem_range.mpr bound, rfl⟩⟩
  · intro acc shape
    rw [pc]
    exact SelectedMap.fetch_member (sites p entry) (codeVAs p base) mapping
      (rowsFootprint raw.imageRows).byte _ acc
      (List.mem_map.mpr ⟨c, member, rfl⟩) shape

end DitShim243.RawFetch
