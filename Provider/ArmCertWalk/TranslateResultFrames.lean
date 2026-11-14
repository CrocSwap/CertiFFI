import ArmCertWalk.NativeTranslateTotalFields
import ArmCertWalk.OuterModeFacts
import ArmCertTranslateModel.TranslateLoopBinding
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

theorem HostEL0ModeAt.guarded_page (regs : Regs) (mode : HostEL0ModeAt regs) (guarded : Bool) :
    HostEL0ModeAt (gpRegs regs guarded) :=
  ⟨mode.noEL2A32, mode.el2A64, mode.vhe, mode.el, mode.ns, mode.tge⟩

/-- Compose actual past register/memory frames around a completed translation.
Occurrence state is retained, not equated to either endpoint. -/
theorem clean_translate_result_frames {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (query : AccessQuery) (leafLevel : Nat) (view : S1DescriptorPIE.View 64)
    (before initial final after : State) (result : FaultRecord × AddressDescriptor)
    (prefixFrame : S1Normality.Frame before initial) (suffixFrame : S1Normality.Frame final after)
    (completed : CleanTranslateResultFields spec config rows mapping query leafLevel view initial result final) :
    CleanTranslateResultFields spec config rows mapping query leafLevel view before result after := by
  obtain ⟨params, out, operations, active, format, resultFault, noFault, map, va, normal,
    addressFault, nonsecure, addressPA, registers, history, images, held⟩ := completed
  refine ⟨params, out, operations, active, format, resultFault, noFault, map, va, normal,
    addressFault, nonsecure, addressPA, ?_, ?_, images.frame suffixFrame.1 suffixFrame.2.1, ?_⟩
  · rw [suffixFrame.1, registers, prefixFrame.1]
  · simpa only [prefixFrame.2.1, suffixFrame.2.1] using history
  · simpa only [prefixFrame.1] using held

/-- The actual source's fetch-guard register equation preserves the declared
current host mode, including BOTH guarded-page results. -/
theorem translate_current_host_mode (config : AttributeConfig) (controls : S1LogicalReference.Controls)
    (physical : PhysicalConfig) (query : AccessDescriptor) (next : TTWState) (before after : State)
    (host : HostWalkAt config controls physical before) (mode : HostEL0ModeAt before.regs)
    (registers : after.regs = fetchGuardRegs query next before.regs) :
    HostWalkAt config controls physical after ∧ HostEL0ModeAt after.regs := by
  have current : HostWalkAt config controls physical (fetchGuardState query next before) := by
    unfold fetchGuardState fetchGuardRegs
    split
    · exact host_walk_at_guarded_page host _
    · exact host
  refine ⟨host_walk_at_regs_frame current registers, ?_⟩
  rw [registers]
  unfold fetchGuardRegs
  split
  · exact mode.guarded_page before.regs _
  · exact mode
/-- Compose a concrete PAST SailM call without unfolding its internal binds. -/
theorem sail_bind_call {α β : Type} (action : SailM α) (next : α → SailM β)
    (before after : State) (value : α) (call : action before = .ok value after) :
    (action >>= next) before = next value after := by
  simp only [Bind.bind, EStateM.bind, call]

#print axioms sail_bind_call
#print axioms HostEL0ModeAt.guarded_page
#print axioms clean_translate_result_frames
#print axioms translate_current_host_mode
end ArmCertWalk
