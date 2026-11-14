import ReleaseProfile.GB10.Producers
import DefaultHeapCards

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048

/-! Heap-card-specific checked config-freedom lemmas (consumers that read neither params nor
controls). The generic source-owned spec context lives in ReleaseProfile.GB10.SourceSpec. -/

namespace ReleaseProfile.GB10.Heap

open ReleaseProfile.MachineSource ReleaseProfile.GB10

/-- Spec-level consumers read neither params nor controls: both may be replaced arbitrarily. -/
theorem shimMap_config_free {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain) (q : ArmFull.S1TTWParams)
    (c : S1LogicalReference.Controls) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : ArmCert.Translate.Model.HeapV2E17.Pins) :
    ArmBridge.CruxGenGuarded.Release.shimMap spec mapping base pins =
      ArmBridge.CruxGenGuarded.Release.shimMap { spec with params := q, controls := c } mapping base pins := rfl

theorem consumerMapAgrees_config_free {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain) (q : ArmFull.S1TTWParams)
    (c : S1LogicalReference.Controls) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : ArmCert.Translate.Model.HeapV2E17.Pins) :
    ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (ArmBridge.CruxGenGuarded.Release.shimMap spec mapping base pins) ↔
      ArmCert.Translate.Model.ConsumerMapAgrees { spec with params := q, controls := c } mapping
        (ArmBridge.CruxGenGuarded.Release.shimMap { spec with params := q, controls := c } mapping base pins) :=
  ⟨fun ⟨pa, tables⟩ => ⟨pa, tables⟩, fun ⟨pa, tables⟩ => ⟨pa, tables⟩⟩

theorem bodyStatic_config_free {domain : ArmCert.Translate.Model.QueryDomain}
    (spec : ArmCert.Translate.Model.TopologyImageSpec domain) (q : ArmFull.S1TTWParams)
    (c : S1LogicalReference.Controls) (mapping : BitVec 64 → Option Nat) (base : BitVec 64)
    (pins : ArmCert.Translate.Model.HeapV2E17.Pins) :
    NativeBodyDeploy.BodyStatic spec mapping base pins ↔
      NativeBodyDeploy.BodyStatic { spec with params := q, controls := c } mapping base pins :=
  ⟨fun ⟨s1, s2, s3, s4, s5, s6, s7, s8, ⟨a1, a2⟩, s10⟩ => ⟨s1, s2, s3, s4, s5, s6, s7, s8, ⟨a1, a2⟩, s10⟩,
   fun ⟨s1, s2, s3, s4, s5, s6, s7, s8, ⟨a1, a2⟩, s10⟩ => ⟨s1, s2, s3, s4, s5, s6, s7, s8, ⟨a1, a2⟩, s10⟩⟩

#check "CURRENT_DECL GB10.Heap.ImageLoadedAsReviewed"
/-- The executed code bytes at the actual entry are the reviewed Heap image at the declared load mapping.
Exactly the two original card atoms (ImageOn, image binding); `epoch` indexes the acquisition/mapping epoch
for ObservedEntryBinding and is not interpreted by the model. -/
def ImageLoadedAsReviewed (e : ArmBridge.Draft.NativeState) (scope : Nat → Prop) (image : MemReloc.Image)
    (loadBase : MemReloc.Word) (base : BitVec 64) (mapping : BitVec 64 → Option Nat) (_epoch : Nat) : Prop :=
  MemReloc.ImageOn scope image e loadBase mapping ∧ image = ArmCert.Translate.Model.HeapV2.image base

#check "CURRENT_DECL GB10.Heap.spec_eq_update"
/-- Two specs with the same physical configuration and tables differ only in params/controls. -/
theorem spec_eq_update {domain : ArmCert.Translate.Model.QueryDomain}
    (spec base : ArmCert.Translate.Model.TopologyImageSpec domain)
    (physical : spec.physicalConfig = base.physicalConfig) (layout : spec.layout = base.layout)
    (logical : spec.logicalRows = base.logicalRows) (image : spec.imageRows = base.imageRows) :
    spec = { base with params := spec.params, controls := spec.controls } := by
  cases spec
  cases base
  simp only at physical layout logical image
  subst physical layout logical image
  rfl

#check "CURRENT_DECL GB10.Heap.consumerMapAgrees_transfer"
/-- Consumer-map agreement depends only on the tables and physical configuration. -/
theorem consumerMapAgrees_transfer {domain : ArmCert.Translate.Model.QueryDomain}
    (spec base : ArmCert.Translate.Model.TopologyImageSpec domain)
    (physical : spec.physicalConfig = base.physicalConfig) (layout : spec.layout = base.layout)
    (logical : spec.logicalRows = base.logicalRows) (image : spec.imageRows = base.imageRows)
    (mapping : BitVec 64 → Option Nat) (b : BitVec 64) (pins : ArmCert.Translate.Model.HeapV2E17.Pins)
    (agrees : ArmCert.Translate.Model.ConsumerMapAgrees base mapping (ArmBridge.CruxGenGuarded.Release.shimMap base mapping b pins)) :
    ArmCert.Translate.Model.ConsumerMapAgrees spec mapping (ArmBridge.CruxGenGuarded.Release.shimMap spec mapping b pins) := by
  rw [spec_eq_update spec base physical layout logical image]
  exact (consumerMapAgrees_config_free base spec.params spec.controls mapping b pins).mp agrees

end ReleaseProfile.GB10.Heap

#print axioms ReleaseProfile.GB10.Heap.shimMap_config_free
#print axioms ReleaseProfile.GB10.Heap.consumerMapAgrees_config_free
#print axioms ReleaseProfile.GB10.Heap.bodyStatic_config_free
#print axioms ReleaseProfile.GB10.Heap.consumerMapAgrees_transfer
