import ArmCertWalk.LeafOutputData
import ArmCertTranslateModel.WalkAccess

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Current static output/map data. Mapping absence is retained; Some 0 is a
    valid declared PA. The canonical output includes the contiguous offset.
    No source call or future-success answer occurs in this predicate. -/
structure LeafMapAt (mapping : BitVec 64 → Option Nat) (config : PhysicalConfig)
    (regs : Regs) (query : AccessQuery) (level : Nat) (view : S1DescriptorPIE.View 64) : Prop where
  mapped : mapping query.va = some (leafOutputAddress query.va level view.stable).address.toNat
  admissible : LeafSuffixAdmissible config regs query.va level view

def checkLeafMap (mapping : BitVec 64 → Option Nat) (config : PhysicalConfig)
    (regs : Regs) (query : AccessQuery) (level : Nat) (view : S1DescriptorPIE.View 64) : Bool :=
  decide (mapping query.va = some (leafOutputAddress query.va level view.stable).address.toNat) &&
  decide (level < 3 → blockFaultValue regs view.stable = false) &&
  decide ((leafOutputAddress query.va level view.stable).address.toNat < 2 ^ (effectiveBits config).toNat)

theorem check_leaf_map_sound (mapping : BitVec 64 → Option Nat) (config : PhysicalConfig)
    (regs : Regs) (query : AccessQuery) (level : Nat) (view : S1DescriptorPIE.View 64)
    (checked : checkLeafMap mapping config regs query level view = true) :
    LeafMapAt mapping config regs query level view := by
  simp only [checkLeafMap, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨checked.1.1, checked.1.2, checked.2⟩

/-- Only the source-inspected BBM primitive fields matter to this current
    block guard. Their VALUES are not fixed; page leaves do not use the guard. -/
theorem LeafMapAt.registers {mapping : BitVec 64 → Option Nat} {config : PhysicalConfig}
    {before after : Regs} {query : AccessQuery} {level : Nat} {view : S1DescriptorPIE.View 64}
    (current : LeafMapAt mapping config before query level view)
    (feature : level < 3 → after.FeatureImpl[101] = before.FeatureImpl[101])
    (support : level < 3 → before.FeatureImpl[101] = true →
      after.bank_Int .__block_bbm_implemented = before.bank_Int .__block_bbm_implemented) :
    LeafMapAt mapping config after query level view := by
  refine ⟨current.mapped, ?_, current.admissible.2⟩
  intro block
  have equal : blockFaultValue after view.stable = blockFaultValue before view.stable := by
    cases active : before.FeatureImpl[101] with
    | false => simp only [blockFaultValue, feature block, active, Bool.false_eq_true, ↓reduceIte]
    | true => simp only [blockFaultValue, feature block, active, support block active]
  exact equal.trans (current.admissible.1 block)

theorem LeafMapAt.guarded_page {mapping : BitVec 64 → Option Nat} {config : PhysicalConfig}
    {regs : Regs} {query : AccessQuery} {level : Nat} {view : S1DescriptorPIE.View 64}
    (current : LeafMapAt mapping config regs query level view) (guarded : Bool) :
    LeafMapAt mapping config (gpRegs regs guarded) query level view :=
  current.registers (fun _ => rfl) (fun _ _ => rfl)

theorem leaf_output_view_congr (va : BitVec 64) (level : Nat) (pie ha hd : Bool)
    (descriptor : BitVec 64) (view : S1DescriptorPIE.View 64)
    (rawView : S1DescriptorPIE.view pie ha hd descriptor = view) :
    leafOutputAddress va level descriptor = leafOutputAddress va level view.stable := by
  have stable : S1Descriptor.stable descriptor = view.stable := congrArg S1DescriptorPIE.View.stable rawView
  have equal : S1Descriptor.stable descriptor = S1Descriptor.stable view.stable := by
    rw [← stable, S1ReferenceKind.stable_idempotent]
  exact leaf_output_stable_congr va level descriptor view.stable equal

/-- Derive the actual held descriptor's readiness and all pure suffix inputs
    from the current role image and finite static map check. This consumes
    THAT actual endpoint and never reruns the native leaf call. -/
theorem walk_endpoint_output_inputs {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (mapping : BitVec 64 → Option Nat) (state : State)
    (query : AccessQuery) (level : Nat) (physical : FullAddress) (view : S1DescriptorPIE.View 64)
    (prior : S1LogicalReference.TablePermissions) (out : WalkVars) (overlay : Bool)
    (endpoint : WalkLeafEndpoint spec.params config spec.controls overlay level physical view prior out state)
    (image : TopologyImageAt spec state) (used : rowsObserve spec.imageRows physical.address.toNat true view)
    (map : LeafMapAt mapping spec.physicalConfig state.regs query level view) :
    mapping query.va = some (S1LogicalReference.outputAddress query.va level
      (walkCurrent out).baseaddress ((walkCurrent out).contiguous == 1#1)).address.toNat ∧
    (walkCurrent out).level = (level : Int) ∧
    (walkCurrent out).baseaddress.paspace = .PAS_NonSecure ∧
    AFReady spec.params .leaf (walkDescriptor out) ∧
    ((walkCurrent out).level < 3 → blockFaultValue state.regs (walkDescriptor out) = false) ∧
    (S1LogicalReference.outputAddress query.va level (walkCurrent out).baseaddress
      ((walkCurrent out).contiguous == 1#1)).address.toNat < 2 ^ (effectiveBits spec.physicalConfig).toNat := by
  obtain ⟨current, descriptor, currentLevel, disch, actualPrior, rawView, present,
    descriptorEq, slotEq, stop, noFault, meaning⟩ := endpoint
  have data := leaf_suffix_data_actual spec.physicalConfig state.regs query.va level view
    (spec.params.pie == 1#1) (spec.params.ha == 1#1) (spec.params.hd == 1#1) descriptor rawView map.admissible
  have output := leaf_meaning_output config spec.controls spec.params overlay current (walkCurrent out)
    level descriptor query.va meaning disch
  have stableOutput := leaf_output_view_congr query.va level _ _ _ descriptor view rawView
  obtain ⟨imageWord, imageBytes, imageView, ready⟩ := image _ true view used
  have equal := S1ByteMemory.descriptor_unique state.mem physical.address.toNat imageWord descriptor imageBytes present
  subst imageWord
  refine ⟨?_, meaning.level_eq, meaning.nonsecure, ?_, ?_, ?_⟩
  · rw [output, stableOutput]
    exact map.mapped
  · rw [descriptorEq]
    exact (afReady_iff spec.params .leaf descriptor).mpr ready
  · intro block
    rw [descriptorEq]
    exact data.1 (by have := meaning.level_eq; omega)
  · rw [output]
    exact data.2

#print axioms check_leaf_map_sound
#print axioms LeafMapAt.registers
#print axioms LeafMapAt.guarded_page
#print axioms leaf_output_view_congr
#print axioms walk_endpoint_output_inputs
end ArmCert.Translate.Model
