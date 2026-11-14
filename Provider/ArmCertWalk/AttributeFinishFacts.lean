import ArmCertWalk.AttributeBodyFacts
import ArmCertWalk.ShareabilityFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem attribute_finish_total (attr : BitVec 8) (sh : BitVec 2) (params : S1TTWParams)
    (initial : MemoryAttributes) (state : State) (meaning : BodyInterprets attr initial) :
    ∃ attrs other, AttributeStages.finish attr sh params initial state = .ok attrs other ∧
      AttributeInterprets attr sh params attrs ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨shareability, other, call, allowed, registers, memory, events⟩ :=
    shareability_total sh state
  simp only [AttributeStages.finish, Bind.bind, EStateM.bind, call, Pure.pure, EStateM.pure]
  refine ⟨_, other, rfl, ?_, registers, memory, events⟩
  constructor
  · rcases meaning with ⟨kind, xs⟩
    by_cases tagged : attr = 240#8 <;> by_cases mtx : params.mtx = 1#1
    all_goals
      simp only [Bool.true_and, beq_iff_eq, tagged, mtx, ↓reduceIte]
      change AttributeBody.mk (attributeProjection initial).kind _ false initial.xs = _
      rw [kind, xs]
      simp only [decodedAttributeBody, tagged, mtx, ↓reduceIte]

  · exact allowed

#print axioms attribute_finish_total

end ArmCertWalk
