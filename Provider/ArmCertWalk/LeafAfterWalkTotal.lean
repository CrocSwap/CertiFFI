import ArmCertWalk.LeafFlagPrepare
import ArmCertWalk.LeafSwapTotal
import ArmCertWalk.TranslateAlignment

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

/-- Check and update THAT walk result. The held next/raw descriptor remain
pre-update values; only StoreHistory describes the new current memory. Actual
IFETCH guarded-page metadata is retained for either GP value. -/
theorem leaf_after_walk_total (params : S1TTWParams) (footprint : Footprint) (va : BitVec 64)
    (aligned : Bool) (acc oldAccess : AccessDescriptor) (slot : AddressDescriptor) (descriptor : BitVec 64)
    (fault : FaultRecord) (memDescriptor newDescriptor : BitVec 128) (a64 s2 : Bool) (next : TTWState) (state : State)
    (d128 : params.d128 = 0#1) (noFault : fault.statuscode = .Fault_None)
    (accessEL : acc.el = EL0) (security : acc.ss = .SS_NonSecure)
    (normal : next.memattrs.memtype = .MemType_Normal)
    (permission : PermissionAdmissible next.permissions params (attributeProjection next.memattrs)
      acc (computedControls next.permissions params state.regs))
    (el : state.regs.PSTATE.EL = 0#2 ∨ state.regs.PSTATE.EL = 1#2)
    (noRME : state.regs.FeatureImpl[232] = false) (aarch64 : state.regs.PSTATE.nRW = 0#1)
    (el3A64 : state.regs.FeatureImpl[7] = true) (noEL3A32 : state.regs.FeatureImpl[3] = false)
    (ram : S2TableRAM.OrdinaryRAM slot.paddress.address)
    (covered : slot.paddress.address.toNat ∈ footprint.slots) (alignment : slot.paddress.address.toNat % 8 = 0)
    (present : S1ByteMemory.DescAt state.mem slot.paddress.address.toNat (S2Endian.encode params.ee descriptor)) :
    ∃ accessOut other,
      TranslateUpdateSource.afterWalk params va aligned acc oldAccess slot (descriptor.setWidth 128)
        fault memDescriptor newDescriptor a64 s2 next state =
        .ok (.ok (accessOut, slot, descriptor.setWidth 128, fault,
          leafSwapMem params acc descriptor memDescriptor, (leafUpdateWord params acc descriptor).setWidth 128,
          a64, s2, next)) other ∧
      other.regs = fetchGuardRegs acc next state.regs ∧
      StoreHistory params footprint state.mem (leafOperations params acc slot.paddress.address.toNat descriptor) other.mem ∧
      LeafUpdateEvents params acc descriptor slot state other := by
  let guarded := fetchGuardState acc next state
  have guardedPSTATE : guarded.regs.PSTATE = state.regs.PSTATE := by
    dsimp [guarded, fetchGuardState, fetchGuardRegs]
    split <;> rfl
  have guardedFeatures : guarded.regs.FeatureImpl = state.regs.FeatureImpl := by
    dsimp [guarded, fetchGuardState, fetchGuardRegs]
    split <;> rfl
  have guardedPermission : PermissionAdmissible next.permissions params (attributeProjection next.memattrs)
      acc (computedControls next.permissions params guarded.regs) := by
    change PermissionAdmissible _ _ _ _ (computedControls _ _ (fetchGuardRegs acc next state.regs))
    rw [computed_controls_fetch_guard]
    exact permission
  have alignmentCall := normal_alignment_false acc aligned params.ntlsmd next.memattrs guarded normal
  obtain ⟨checked, permissionCall, checkedRegs, checkedMem, checkedEvents⟩ :=
    permission_check_total fault next params acc guarded accessEL security guardedPermission
  have pstate : checked.regs.PSTATE = state.regs.PSTATE := by rw [checkedRegs]; exact guardedPSTATE
  have features : checked.regs.FeatureImpl = state.regs.FeatureImpl := by rw [checkedRegs]; exact guardedFeatures
  have memory : checked.mem = state.mem := checkedMem
  have events : checked.events = state.events := checkedEvents
  obtain ⟨accessOut, other, swapCall, otherRegs, history, updateEvents⟩ :=
    leaf_swap_total params footprint va acc oldAccess slot descriptor fault memDescriptor a64 s2 next checked
      d128 (by rw [pstate]; exact el) (by rw [features]; exact noRME) (by rw [pstate]; exact aarch64)
      (by rw [features]; exact el3A64) (by rw [features]; exact noEL3A32) ram covered alignment
      (by rw [memory]; exact present)
  have prepareCall := leaf_flag_prepare_total params acc descriptor fault checked noFault
  have flagCall : TranslateUpdateSource.flagAction params va acc oldAccess slot (descriptor.setWidth 128)
      fault memDescriptor a64 s2 next checked =
      .ok (.ok (accessOut, fault, leafSwapMem params acc descriptor memDescriptor,
        (leafUpdateWord params acc descriptor).setWidth 128, a64, s2)) other := by
    rw [TranslateUpdateSource.flag_action_eq]
    simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
      Pure.pure, EStateM.bind, EStateM.pure, prepareCall, swapCall]
  have noneEq : ((.Fault_None : Fault) == .Fault_None) = true := rfl
  have noneNe : ((.Fault_None : Fault) != .Fault_None) = false := rfl
  refine ⟨accessOut, other, ?_, otherRegs.trans checkedRegs, ?_, ?_⟩
  · by_cases fetch : acc.acctype == .AccessType_IFETCH
    all_goals
      have gpCall := fetch_guard_call acc next state
      have alignmentActual := alignmentCall
      have permissionActual := permissionCall
      simp only [guarded, fetchGuardState, fetchGuardRegs, fetch, Bool.false_eq_true, ↓reduceIte] at gpCall alignmentActual permissionActual
      simp [TranslateUpdateSource.afterWalk, noFault, noneEq, noneNe, fetch, gpCall,
        alignmentActual, permissionActual, flagCall, Bind.bind, Pure.pure, Functor.map,
        ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
        EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift]
  · simpa only [memory] using history
  · simpa only [LeafUpdateEvents, events] using updateEvents

#print axioms leaf_after_walk_total
end ArmCertWalk
