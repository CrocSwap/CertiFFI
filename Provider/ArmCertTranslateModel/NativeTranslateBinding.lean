import ArmCertWalk.NativeTranslateTotal
import ArmCertTranslateModel.NormalizedControlTransport
import ArmCertTranslateModel.StoreDomain

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Consume the result DERIVED by the actual complete S1Translate theorem.
    Restore the static image parameterization, expose the projected register
    and table-byte frames, and retain native byte availability on the SAME
    final memory. This is a past-call result projection, never an Entry premise.
    Full outer TranslateAddress and certified-run composition remain separate. -/
theorem clean_translate_image_frame {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {leafLevel : Nat} {view : S1DescriptorPIE.View 64}
    {initial other : State} {result : FaultRecord × AddressDescriptor}
    (clean : CleanTranslateResult spec config rows mapping query leafLevel view initial result other) :
    CurrentImagesAt spec config rows other ∧
      ArmCert.Premises.TranslationAgreesV1.ProjRegsEq initial.regs other.regs ∧
      WritesOnly (rowsFootprint spec.imageRows).byte (fun a => initial.mem[a]?) (fun a => other.mem[a]?) ∧
      (∀ address : Nat, (other.mem[address]?).isSome = (initial.mem[address]?).isSome) := by
  obtain ⟨params, out, operations, active, faultEq, faultNone, mapResult, va, normal, pa,
    registers, history, images, held⟩ := clean
  have staticImages : CurrentImagesAt spec config rows other :=
    images.reparam spec.params active.ha.symm active.hd.symm active.pie.symm active.wxn.symm
  refine ⟨staticImages, ?_, history.frame rfl, history.byte_presence⟩
  rw [registers]
  unfold fetchGuardRegs
  split
  · exact gp_projected_frame initial.regs _
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Actual code/data reads can recover PRESENT bytes after this translation,
    even when their addresses alias the descriptors or changed flag bytes.
    The byte VALUE used by a read must still come from other.mem. -/
theorem clean_translate_some_after {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {leafLevel : Nat} {view : S1DescriptorPIE.View 64}
    {initial other : State} {result : FaultRecord × AddressDescriptor}
    (clean : CleanTranslateResult spec config rows mapping query leafLevel view initial result other)
    (address : Nat) (value : BitVec 8) (present : initial.mem[address]? = some value) :
    ∃ current : BitVec 8, other.mem[address]? = some current := by
  obtain ⟨params, out, operations, active, faultEq, faultNone, mapResult, va, normal, pa,
    registers, history, images, held⟩ := clean
  exact history.some_after address value present

#print axioms clean_translate_image_frame
#print axioms clean_translate_some_after
end ArmCert.Translate.Model
