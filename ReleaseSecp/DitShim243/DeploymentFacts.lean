import DitShim243.Deployment
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded
open TranslateSpan TranslateSpan.SecpRawDeployment
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace DitShim243.DeploymentFacts
open Deployment

theorem raw_layout (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (start : Nat) (imm : BitVec 26)
    (layout : LayoutFacts (extend p start imm) raw mapping base entry) : LayoutFacts p raw mapping base entry := by
  refine ⟨layout.bounds,layout.aliases,?_,layout.injective,?_,layout.outputTable,?_⟩
  · intro c member
    exact layout.codeRange c (List.mem_append_left _ member)
  · intro o pa inside mapped bad
    apply layout.separated o pa ?_ mapped bad
    simpa only [codeOffsets,extend,List.flatMap_append] using
      (List.mem_append_left ((shimCode start imm).flatMap (fun c => (List.range 4).map (c.1 + ·))) inside)
  · intro c member
    exact layout.codeWords c (List.mem_append_left _ member)

def code_facts {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (entry : NativeState) (start : Nat) (imm : BitVec 26) (slot : BitVec 64)
    (image : MemReloc.Image) (table : spec.imageRows = raw.imageRows)
    (layout : LayoutFacts (extend p start imm) raw mapping base entry)
    (imageWord : ∀ j, j < 11 → ∀ i < 4, image (start + 4 * j + i) = some ((Fetches.word imm j).extractLsb' (8 * i) 8)) :
    Fetch.CodeFacts spec mapping (Deployment.consumer p raw mapping base entry start imm slot)
      (· ∈ codeOffsets (extend p start imm)) image base start (Fetches.word imm) := by
  refine ⟨?_,?_,?_,?_,imageWord,?_⟩
  · intro j hj i hi
    exact List.mem_flatMap.mpr ⟨(start+4 * j,(Fetches.word imm j).toNat),
      List.mem_append_right _ (shim_member start imm j hj),List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩⟩
  · intro j hj
    exact (layout.codeWords _ (List.mem_append_right _ (shim_member start imm j hj))).1
  · intro j hj
    exact (layout.codeWords _ (List.mem_append_right _ (shim_member start imm j hj))).2
  · intro o pa inside mapped inTable
    apply layout.separated o pa inside mapped
    exact Or.inl (table ▸ inTable)
  · intro j hj acc shape
    exact code_permitted p raw mapping base entry start imm slot j hj acc shape

#print axioms raw_layout
#print axioms code_facts
end DitShim243.DeploymentFacts
