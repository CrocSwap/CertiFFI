import ArmCertWalk.TranslateResultFrames
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk
/-- Register/memory framing is sufficient for the completed translation data.
This intentionally retains arbitrary actual events from surrounding source
hooks; no event equality or trace preservation is assumed here. -/
theorem clean_translate_result_memory_frames {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (leafLevel : Nat) (view : S1DescriptorPIE.View 64)
    (before initial final after : State) (result : FaultRecord × AddressDescriptor)
    (prefixRegs : initial.regs = before.regs) (prefixMem : initial.mem = before.mem)
    (suffixRegs : after.regs = final.regs) (suffixMem : after.mem = final.mem)
    (completed : CleanTranslateResultFields spec config rows mapping query leafLevel view initial result final) :
    CleanTranslateResultFields spec config rows mapping query leafLevel view before result after := by
  obtain ⟨params, out, operations, active, format, resultFault, noFault, map, va, normal,
    addressFault, nonsecure, addressPA, registers, history, images, held⟩ := completed
  refine ⟨params, out, operations, active, format, resultFault, noFault, map, va, normal,
    addressFault, nonsecure, addressPA, ?_, ?_, images.frame suffixRegs suffixMem, ?_⟩
  · rw [suffixRegs, registers, prefixRegs]
  · simpa only [prefixMem, suffixMem] using history
  · simpa only [prefixRegs] using held

/-- The original source hooks append the exact translation events. -/
theorem start_translation_eq (info : TranslationStartInfo) (state : State) :
    start_translation info state = .ok () {state with events := state.events.push (.translationStart info)} := rfl

theorem end_translation_eq (address : AddressDescriptor) (state : State) :
    end_translation address state = .ok () {state with events := state.events.push (.translationEnd address)} := rfl
#print axioms clean_translate_result_memory_frames
#print axioms start_translation_eq
#print axioms end_translation_eq
end ArmCertWalk
