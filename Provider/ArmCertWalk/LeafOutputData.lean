import ArmCertWalk.WalkGuardFacts
import ArmCertWalk.LeafNextTotal

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Canonical current-data output for the supported source format. Initial
DisCH=0 is derived by the actual getter/initializer and each table step. -/
def leafOutputAddress (va : BitVec 64) (level : Nat) (descriptor : BitVec 64) : FullAddress :=
  S1LogicalReference.outputAddress va level
    {paspace := .PAS_NonSecure, address := S1LogicalReference.leafBase level descriptor}
    (descriptor.getLsbD 52)

theorem leaf_base_stable_congr (level : Nat) (first second : BitVec 64)
    (stable : S1Descriptor.stable first = S1Descriptor.stable second) :
    S1LogicalReference.leafBase level first = S1LogicalReference.leafBase level second := by
  have base := S1StablePath.table_base_eq first second stable
  change sourceTableBase first = sourceTableBase second at base
  rw [source_table_base_eq, source_table_base_eq] at base
  simp only [S1LogicalReference.leafBase, base]

theorem leaf_output_stable_congr (va : BitVec 64) (level : Nat) (first second : BitVec 64)
    (stable : S1Descriptor.stable first = S1Descriptor.stable second) :
    leafOutputAddress va level first = leafOutputAddress va level second := by
  have bit := S1StablePath.bit_eq first second stable 52 (by decide) (by decide) (by decide)
  simp only [leafOutputAddress, leaf_base_stable_congr level first second stable, bit]

theorem leaf_meaning_output (config : AttributeConfig) (controls : S1LogicalReference.Controls)
    (params : S1TTWParams) (overlay : Bool) (current next : TTWState) (level : Nat)
    (descriptor va : BitVec 64) (meaning : LeafMeaning config controls params overlay current level descriptor next)
    (disch : current.disch = 0#1) :
    S1LogicalReference.outputAddress va level next.baseaddress (next.contiguous == 1#1) =
      leafOutputAddress va level descriptor := by
  have contiguous : (next.contiguous == 1#1) = descriptor.getLsbD 52 := by
    rw [meaning.contiguous, disch]
    cases bit : descriptor.getLsbD 52 <;> rfl
  have base : next.baseaddress =
      {paspace := .PAS_NonSecure, address := S1LogicalReference.leafBase level descriptor} := by
    have address := meaning.base
    have space := meaning.nonsecure
    cases selected : next.baseaddress with
    | mk pas addressWord =>
      simp only [selected] at address space
      simp only [selected, address, space]
  simp only [contiguous, base, leafOutputAddress]

/-- Pure per-query leaf data, checked by the finite image/declared-map layer.
AF readiness remains a property of the CURRENT role-specific raw descriptor. -/
def LeafSuffixAdmissible (config : PhysicalConfig) (regs : Regs) (va : BitVec 64)
    (level : Nat) (view : S1DescriptorPIE.View 64) : Prop :=
  (level < 3 → blockFaultValue regs view.stable = false) ∧
    (leafOutputAddress va level view.stable).address.toNat < 2 ^ (effectiveBits config).toNat

theorem leaf_suffix_data_actual (config : PhysicalConfig) (regs : Regs) (va : BitVec 64)
    (level : Nat) (view : S1DescriptorPIE.View 64) (pie ha hd : Bool) (descriptor : BitVec 64)
    (rawView : S1DescriptorPIE.view pie ha hd descriptor = view)
    (admissible : LeafSuffixAdmissible config regs va level view) :
    (level < 3 → blockFaultValue regs descriptor = false) ∧
      (leafOutputAddress va level descriptor).address.toNat < 2 ^ (effectiveBits config).toNat := by
  have stable : S1Descriptor.stable descriptor = view.stable := congrArg S1DescriptorPIE.View.stable rawView
  have same : S1Descriptor.stable descriptor = S1Descriptor.stable view.stable := by
    rw [← stable, S1ReferenceKind.stable_idempotent]
  have bit := S1StablePath.bit_eq descriptor view.stable same 16 (by decide) (by decide) (by decide)
  have block : blockFaultValue regs descriptor = blockFaultValue regs view.stable := by
    simp only [blockFaultValue, bit]
  exact ⟨by intro small; rw [block]; exact admissible.1 small,
    by rw [leaf_output_stable_congr va level descriptor view.stable same]; exact admissible.2⟩

#print axioms leaf_output_stable_congr
#print axioms leaf_meaning_output
#print axioms leaf_suffix_data_actual
end ArmCertWalk
