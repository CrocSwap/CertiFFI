import DitShim243.Initial
import TranslateSpan.CurrentMemMTE2
open Sail ArmFull ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded TranslateSpan TranslateSpan.SecpRawDeployment ArmCertValue ArmCertPipe
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace DitShim243.BodyFootprints

theorem output_member (p : Plan) (mapping : BitVec 64 → Option Nat) (s : NativeState) (pa : Nat)
    (member : pa ∈ outputBytes p mapping s) :
    ∃ r n, (r,n) ∈ p.outputs ∧ ∃ j, j < n ∧ view p mapping s r j = some pa := by
  obtain ⟨⟨r,n⟩,row,inside⟩ := List.mem_flatMap.mp member
  obtain ⟨j,hj,mapped⟩ := List.mem_filterMap.mp inside
  exact ⟨r,n,row,j,List.mem_range.mp hj,mapped⟩

theorem outside_table (p : Plan) (raw : CheckedTopology.Raw) (mapping : BitVec 64 → Option Nat)
    (base : BitVec 64) (s : NativeState) (layout : LayoutFacts p raw mapping base s)
    (pa : Nat) (table : (rowsFootprint raw.imageRows).byte pa) : pa ∉ outputBytes p mapping s := by
  intro member
  obtain ⟨r,n,row,j,bound,mapped⟩ := output_member p mapping s pa member
  exact layout.outputTable r n row j bound pa mapped table

theorem outside_slot (p : Plan) (mapping : BitVec 64 → Option Nat) (s : NativeState)
    (pins : HeapV2E17.Pins)
    (sep : ∀ r n, (r,n) ∈ p.buffers ++ p.outputs → ∀ i < n, ∀ pa,
      view p mapping s r i = some pa → ¬ RtShim2.ShimMem.slotBytes pins mapping pa)
    (pa : Nat) (slot : RtShim2.ShimMem.slotBytes pins mapping pa) : pa ∉ outputBytes p mapping s := by
  intro member
  obtain ⟨r,n,row,j,bound,mapped⟩ := output_member p mapping s pa member
  exact sep r n (List.mem_append_right _ row) j bound pa mapped slot

#print axioms output_member
#print axioms outside_table
#print axioms outside_slot
end DitShim243.BodyFootprints
