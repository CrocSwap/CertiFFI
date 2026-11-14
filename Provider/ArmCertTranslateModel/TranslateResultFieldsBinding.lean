import ArmCertTranslateModel.TranslationInvariant
import ArmCertWalk.NativeTranslateTotalFields

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCert.Translate.Model

/-- Forget additional OUTPUT fields of the same actual result. This does not
    invoke the source a second time or identify two choice occurrence states. -/
theorem clean_translate_fields_to_clean {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {leafLevel : Nat} {view : S1DescriptorPIE.View 64}
    {initial other : State} {result : FaultRecord × AddressDescriptor}
    (clean : CleanTranslateResultFields spec config rows mapping query leafLevel view initial result other) :
    CleanTranslateResult spec config rows mapping query leafLevel view initial result other := by
  obtain ⟨params, out, operations, active, format, faultEq, faultNone, mapResult, va, normal,
    addressFault, nonsecure, pa, registers, history, images, held⟩ := clean
  exact ⟨params, out, operations, active, faultEq, faultNone, mapResult, va, normal, pa,
    registers, history, images, held⟩

/-- The actual effective getter format supplies EE0. The narrower memory VALUE
    frame follows the SAME actual ordered history; native traffic still writes
    eight bytes per store and is not identified with these two flag bytes. -/
theorem clean_translate_fields_flag_frame {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {config : AttributeConfig} {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat}
    {query : AccessQuery} {leafLevel : Nat} {view : S1DescriptorPIE.View 64}
    {initial other : State} {result : FaultRecord × AddressDescriptor}
    (clean : CleanTranslateResultFields spec config rows mapping query leafLevel view initial result other) :
    ∃ (params : S1TTWParams) (operations : List TableUpdate),
      WalkFormat params spec.physicalConfig spec.controls ∧
      StoreHistory params (rowsFootprint spec.imageRows) initial.mem operations other.mem ∧
      WritesOnly (historyFlagBytes operations) (fun a => initial.mem[a]?) (fun a => other.mem[a]?) := by
  obtain ⟨params, out, operations, active, format, faultEq, faultNone, mapResult, va, normal,
    addressFault, nonsecure, pa, registers, history, images, held⟩ := clean
  exact ⟨params, operations, format, history, history.flag_value_frame format.endian⟩

/-- Current structural inputs derive ONE actual complete S1Translate result,
    retaining actual address fault/PAS and effective format as well as the
    preserved invariant and native-memory frames. No raw=normalized condition
    or new input is required by the stronger result. -/
theorem current_s1_translate_fields_total {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (member : domain query) (data : S1AccessData spec config rows query)
    (fault : FaultRecord) (initial : State) (current : CurrentS1At spec config rows initial)
    (access : CurrentS1AccessAt spec config rows mapping query data initial)
    (noFault : fault.statuscode = .Fault_None) :
    ∃ result other,
      AArch64_S1Translate fault .Regime_EL20 query.va query.request.aligned query.request.raw initial =
        .ok result other ∧
      CleanTranslateResultFields spec config rows mapping query data.leafLevel data.view initial result other ∧
      CurrentS1At spec config rows other ∧ CurrentS1AccessAt spec config rows mapping query data other ∧
      ArmCert.Premises.TranslationAgreesV1.ProjRegsEq initial.regs other.regs ∧
      WritesOnly (rowsFootprint spec.imageRows).byte (fun a => initial.mem[a]?) (fun a => other.mem[a]?) ∧
      (∀ address : Nat, (other.mem[address]?).isSome = (initial.mem[address]?).isSome) := by
  obtain ⟨result, other, call, fields⟩ :=
    native_translate_fields_total spec config rows mapping query member query.request.aligned data.leafLevel
      data.logical data.physical data.view data.path data.permissions fault initial data.lower current.host
      current.core current.geometry access.layout current.images current.guards access.checks current.rawFault
      current.enabled data.accessEL data.nonsecure noFault current.cache access.epd access.map access.outputPolicy
  have clean := clean_translate_fields_to_clean fields
  have preserved := current_s1_after data current access clean
  have frames := clean_translate_image_frame clean
  exact ⟨result, other, call, fields, preserved.1, preserved.2, frames.2⟩

#print axioms clean_translate_fields_to_clean
#print axioms clean_translate_fields_flag_frame
#print axioms current_s1_translate_fields_total
end ArmCert.Translate.Model
