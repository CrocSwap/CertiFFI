import ArmCertWalk.TranslateOutputAttrs

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- The source's LS64 exclusive-fault guard on actual Normal output attributes.
Ordinary accesses discharge it from their actual ls64=false metadata; LS64
retains its architectural NC requirement instead of being globally excluded. -/
def OutputExclusiveAdmissible (acc : AccessDescriptor) (attrs : MemoryAttributes) : Prop :=
  acc.ls64 = true → attrs.inner.attrs = MemAttr_NC ∧ attrs.outer.attrs = MemAttr_NC

theorem output_exclusive_ordinary (acc : AccessDescriptor) (attrs : MemoryAttributes)
    (ordinary : acc.ls64 = false) : OutputExclusiveAdmissible acc attrs := by
  intro active
  rw [ordinary] at active
  cases active

def outputEffectiveAttrs (attrs : MemoryAttributes) : MemoryAttributes :=
  {attrs with shareability := EffectiveShareability attrs}

/-- The actual final source address constructor and MECID query. Output
attributes are those selected by the source cache queries, with effective
shareability; only their Normal kind is required here. -/
theorem output_finish_total (va : BitVec 64) (acc : AccessDescriptor) (params : S1TTWParams)
    (slot : AddressDescriptor) (descriptor : BitVec 128) (fault : FaultRecord) (next : TTWState)
    (oa : FullAddress) (attrs : MemoryAttributes) (state : State)
    (nonsecure : oa.paspace = .PAS_NonSecure) (normal : attrs.memtype = .MemType_Normal)
    (admissible : OutputExclusiveAdmissible acc attrs) :
    ∃ address other,
      TranslateOutputParts.finish .Regime_EL20 va acc params slot descriptor fault next oa attrs state =
        .ok (.ok (fault, address)) other ∧ address.paddress = oa ∧ address.vaddress = va ∧
      address.memattrs = outputEffectiveAttrs attrs ∧ address.tlbcontext = slot.tlbcontext ∧
      address.s1assured = next.s1assured ∧ address.mecid = DEFAULT_MECID ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  obtain ⟨created, other, createCall, addressPA, addressVA, addressAttrs, registers, memory, events⟩ :=
    create_output_total va oa (outputEffectiveAttrs attrs) state
  let address : AddressDescriptor :=
    {created with tlbcontext := slot.tlbcontext, s1assured := next.s1assured, mecid := DEFAULT_MECID}
  have mecid : AArch64_S1OutputMECID params .Regime_EL20 (AArch64_GetVARange va) oa.paspace descriptor other =
      .ok DEFAULT_MECID other := by rw [nonsecure, output_mecid_nonsecure]; rfl
  have mecidCreated : AArch64_S1OutputMECID params .Regime_EL20 (AArch64_GetVARange va) created.paddress.paspace descriptor other =
      .ok DEFAULT_MECID other := by rw [addressPA]; exact mecid
  have otherRegime : ((.Regime_EL20 : Regime) == .Regime_EL10) = false := rfl
  have isNormal : ((.MemType_Normal : MemType) == .MemType_Normal) = true := rfl
  refine ⟨address, other, ?_, addressPA, addressVA, addressAttrs, rfl, rfl, rfl, registers, memory, events⟩
  have createActual := createCall
  simp only [outputEffectiveAttrs, normal] at createActual
  by_cases ls64 : acc.ls64 = true
  · obtain ⟨inner, outer⟩ := admissible ls64
    simp [TranslateOutputParts.finish, otherRegime, normal, isNormal, ls64, inner, outer,
      outputEffectiveAttrs, createActual, mecidCreated, address, Bind.bind, Pure.pure, Functor.map,
      ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
      EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift]
  · simp [TranslateOutputParts.finish, otherRegime, ls64, normal, outputEffectiveAttrs,
      createActual, mecidCreated, address, Bind.bind, Pure.pure, Functor.map,
      ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
      EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift]

#print axioms output_exclusive_ordinary
#print axioms output_finish_total
end ArmCertWalk
