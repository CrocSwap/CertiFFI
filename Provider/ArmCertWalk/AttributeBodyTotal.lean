import ArmCertWalk.AttributeBodyFacts

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem attribute_body_total (config : AttributeConfig) (params : S1TTWParams)
    (state : State) (current : ActiveAttributesAt config params state)
    (attr : BitVec 8) (admissible : AttributeAdmissible config attr)
    (initial : MemoryAttributes) :
    ∃ attrs other, AttributeStages.body attr initial state = .ok attrs other ∧
      BodyInterprets attr attrs ∧ other.regs = state.regs ∧
      other.mem = state.mem ∧ other.events = state.events := by
  have highdef : Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb attr 7 4) =
      attributeHigh attr := rfl
  by_cases device : attributeHigh attr = 0#4
  · simp only [AttributeStages.body, highdef, device, BEq.rfl, ↓reduceIte,
      Bind.bind, EStateM.bind, device_eq, Pure.pure, EStateM.pure]
    refine ⟨_, state, rfl, ?_, rfl, rfl, rfl⟩
    simp only [BodyInterprets, attributeProjection, decodedAttributeBody, device,
      ↓reduceIte, S1LogicalReference.AttributeKind.device.injEq, BitVec.not_inj]
    constructor
    · rfl
    · apply BitVec.eq_of_getLsbD_eq
      intro i bound
      have zero : i = 0 := by omega
      subst i
      simp [Sail.BitVec.access, BitVec.join1,
        ← BitVec.getLsbD_eq_getElem]
  · by_cases first : attr = 64#8
    · subst attr
      have feature := xs_current_eq config params state current
      rw [admissible_64_xs config admissible] at feature
      simp only [AttributeStages.body, highdef, device, beq_iff_eq,
        ↓reduceIte, Bind.bind, EStateM.bind, feature,
        Pure.pure, EStateM.pure, ArmFull.assert]
      refine ⟨_, state, rfl, ?_, rfl, rfl, rfl⟩
      simp [BodyInterprets, attributeProjection, decodedAttributeBody, attributeHigh,
        cacheProjection, MemAttr_NC, Sail.BitVec.extractLsb, BitVec.extractLsb]
    · by_cases second : attr = 160#8
      · subst attr
        have feature := xs_current_eq config params state current
        rw [admissible_160_xs config admissible] at feature
        simp only [AttributeStages.body, highdef, device, first, beq_iff_eq,
          ↓reduceIte, Bind.bind, EStateM.bind, feature,
          Pure.pure, EStateM.pure, ArmFull.assert]
        refine ⟨_, state, rfl, ?_, rfl, rfl, rfl⟩
        simp [BodyInterprets, attributeProjection, decodedAttributeBody, attributeHigh,
          cacheProjection, MemAttr_NC, MemAttr_WT, MemHint_No, MemHint_RA,
          Sail.BitVec.extractLsb, BitVec.extractLsb]
      · by_cases third : attr = 240#8
        · subst attr
          have feature := mte2_current_eq config params state current
          rw [admissible_240_mte2 config admissible] at feature
          simp only [AttributeStages.body, highdef, device, first, second, beq_iff_eq,
            ↓reduceIte, Bind.bind, EStateM.bind, feature,
            Pure.pure, EStateM.pure, ArmFull.assert]
          refine ⟨_, state, rfl, ?_, rfl, rfl, rfl⟩
          simp [BodyInterprets, attributeProjection, decodedAttributeBody, attributeHigh,
            cacheProjection, MemAttr_NC, MemAttr_WB, MemHint_No, MemHint_RWA,
            Sail.BitVec.extractLsb, BitVec.extractLsb]
        · obtain ⟨outer, middle, outerCall, outerMeaning, outerRegs, outerMem, outerEvents⟩ :=
            cache_total (Sail.BitVec.extractLsb attr 7 4) state
          obtain ⟨inner, other, innerCall, innerMeaning, innerRegs, innerMem, innerEvents⟩ :=
            cache_total (Sail.BitVec.extractLsb attr 3 0) middle
          have outerAttrs := congrArg (fun cache => cache.attrs) outerMeaning
          have innerAttrs := congrArg (fun cache => cache.attrs) innerMeaning
          change outer.attrs = _ at outerAttrs
          change inner.attrs = _ at innerAttrs
          simp only [AttributeStages.body, highdef, device, first, second, third, beq_iff_eq, ↓reduceIte, Bind.bind, EStateM.bind,
            outerCall, innerCall, Pure.pure, EStateM.pure]
          refine ⟨_, other, rfl, ?_, innerRegs.trans outerRegs,
            innerMem.trans outerMem, innerEvents.trans outerEvents⟩
          simp only [Sail.BitVec.extractLsb, BitVec.extractLsb] at outerMeaning innerMeaning outerAttrs innerAttrs
          by_cases wb : (decodedCache (attr.extractLsb' 0 4)).attrs = MemAttr_WB ∧
              (decodedCache (attr.extractLsb' 4 4)).attrs = MemAttr_WB <;>
            simp [BodyInterprets, attributeProjection, decodedAttributeBody, device,
              first, second, third, outerMeaning, innerMeaning, outerAttrs, innerAttrs, wb]

#print axioms attribute_body_total

end ArmCertWalk
