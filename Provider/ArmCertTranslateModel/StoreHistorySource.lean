import ArmCertTranslateModel.StoreHistory

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmCertWalk
set_option maxHeartbeats 200000
namespace ArmCert.Translate.Model

/-- Derive a concrete step from the actual native swap. Current descriptor
    bytes and authorization are source-walk inputs; success, exact memory effect
    and register frame are conclusions at the SAME actual successor. -/
theorem swap_store_step (params : S1TTWParams) (footprint : Footprint)
    (operation : TableUpdate) (fault : FaultRecord) (acc : AccessDescriptor)
    (addr : AddressDescriptor) (ti : TranslationInfo) (state : State)
    (noRME : state.regs.FeatureImpl[232] = false)
    (ram : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (slot : operation.slot = addr.paddress.address.toNat)
    (covered : operation.slot ∈ footprint.slots) (aligned : operation.slot % 8 = 0)
    (present : S1ByteMemory.DescAt state.mem operation.slot
      (S2Endian.encode params.ee operation.before))
    (allowed : AllowedUpdate params operation.role operation.before operation.after) :
    ∃ next,
      AArch64_MemSwapTableDesc fault operation.before operation.after params.ee acc addr ti state =
        .ok (fault, operation.after) next ∧
      next.regs = state.regs ∧ StoreStep params footprint operation state.mem next.mem := by
  have bytes : S2ByteMemory.DescAt state.mem addr.paddress.address.toNat
      (S2Endian.encode params.ee operation.before) := by
    intro i hi
    simpa only [slot] using present i hi
  obtain ⟨next, call, registers, stored⟩ :=
    S2SwapAnyFrame.total params.ee fault operation.before operation.after acc addr ti state noRME ram bytes
  refine ⟨next, call, registers, covered, aligned, present, allowed, ?_⟩
  change next.mem = S1ByteMemory.store state.mem addr.paddress.address.toNat
    (S2Endian.encode params.ee operation.after) at stored
  simpa only [slot] using stored

#print axioms swap_store_step
end ArmCert.Translate.Model
