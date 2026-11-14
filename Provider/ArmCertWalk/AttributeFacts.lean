import ArmCertWalk.AttributeBodyTotal
import ArmCertWalk.AttributeFinishFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Actual attribute decoding from current source features and a pure
admissibility test. Every intermediate value and poststate is derived here. -/
theorem attribute_total (config : AttributeConfig) (params : S1TTWParams)
    (state : State) (current : ActiveAttributesAt config params state)
    (attr : BitVec 8) (sh : BitVec 2) (admissible : AttributeAdmissible config attr) :
    ∃ attrs other, S1DecodeMemAttrs attr sh true params state = .ok attrs other ∧
      AttributeInterprets attr sh params attrs ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨initial, first, initialCall, initialRegs, initialMem, initialEvents⟩ :=
    AttributeStages.initial_total state
  obtain ⟨body, second, bodyCall, bodyMeaning, bodyRegs, bodyMem, bodyEvents⟩ :=
    attribute_body_total config params first (current.of_regs initialRegs) attr admissible initial
  obtain ⟨attrs, other, finishCall, meaning, finishRegs, finishMem, finishEvents⟩ :=
    attribute_finish_total attr sh params body second bodyMeaning
  refine ⟨attrs, other, ?_, meaning, finishRegs.trans (bodyRegs.trans initialRegs),
    finishMem.trans (bodyMem.trans initialMem), finishEvents.trans (bodyEvents.trans initialEvents)⟩
  rw [AttributeSource.source_eq config params state current attr sh admissible,
    AttributeStages.action_eq]
  simp only [AttributeStages.staged, Bind.bind, EStateM.bind, initialCall, bodyCall, finishCall]

theorem selected_attribute_total (config : AttributeConfig) (params : S1TTWParams)
    (state : State) (current : ActiveAttributesAt config params state)
    (descriptor : BitVec 64) (sh : BitVec 2)
    (admissible : AttributeAdmissible config (selectedAttribute config descriptor)) :
    ∃ attrs other,
      (do
        let attr ← AArch64_MAIRAttr (S1MAIRKernel.index descriptor) params.mair2 params.mair
        S1DecodeMemAttrs attr sh true params) state = .ok attrs other ∧
      AttributeInterprets (selectedAttribute config descriptor) sh params attrs ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨attrs, other, actual, meaning, registers, memory, events⟩ :=
    attribute_total config params state current (selectedAttribute config descriptor) sh admissible
  refine ⟨attrs, other, ?_, meaning, registers, memory, events⟩
  simp only [Bind.bind, EStateM.bind, selectedAttribute_active_eq config params state current,
    actual]

#print axioms attribute_total
#print axioms selected_attribute_total

end ArmCertWalk
