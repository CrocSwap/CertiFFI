import ArmCertWalk.TranslateFinishSource
import ArmCertWalk.WalkPrefixQueries
import Pilot.ObservationSimp

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512

namespace ArmCertWalk

theorem translate_cache_disabled (descriptor memDescriptor newDescriptor : BitVec 128) (state : State)
    (cache : state.regs.bank_Bool .__tlb_enabled = false) :
    TranslateFinishSource.cacheGuard descriptor memDescriptor newDescriptor state = .ok (.ok false) state := by
  have readCall : (readReg ArmFull.Register.__tlb_enabled : SailM Bool) state = .ok false state := by
    change EStateM.Result.ok (state.regs.bank_Bool .__tlb_enabled) state = .ok false state
    rw [cache]
  simp [TranslateFinishSource.cacheGuard, readCall, Bind.bind, Pure.pure, Functor.map,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
    EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
    ]

theorem output_mecid_nonsecure (params : S1TTWParams) (va : BitVec 64) (descriptor : BitVec 128) :
    AArch64_S1OutputMECID params .Regime_EL20 (AArch64_GetVARange va) .PAS_NonSecure descriptor =
      (pure DEFAULT_MECID : SailM (BitVec 16)) := by
  have nonrealm : ((.PAS_NonSecure : PASpace) != .PAS_Realm) = true := rfl
  by_cases emec : params.emec == 0#1 <;>
    simp [AArch64_S1OutputMECID, Sail.BitVec.length, emec, nonrealm,
      ArmFull.assert, PreSail.assert, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
  all_goals rfl

drive_spec create_output_native, create_output_eq : fun (va : BitVec 64) (pa : FullAddress)
  (attrs : MemoryAttributes) (state : State) => CreateAddressDescriptor va pa attrs state

theorem create_output_total (va : BitVec 64) (pa : FullAddress) (attrs : MemoryAttributes) (state : State) :
    ∃ address other, CreateAddressDescriptor va pa attrs state = .ok address other ∧
      address.paddress = pa ∧ address.vaddress = va ∧ address.memattrs = attrs ∧
      other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  rw [create_output_eq]
  delta create_output_native
  exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem normal_nc_total (state : State) :
    ∃ attrs other, NormalNCMemAttr () state = .ok attrs other ∧
      attrs.memtype = .MemType_Normal ∧ other.regs = state.regs ∧ other.mem = state.mem ∧ other.events = state.events := by
  rw [S1EntryCalleesExtra.normalnc_eq]
  delta S1EntryCalleesExtra.normalnc_native
  exact ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

#print axioms translate_cache_disabled
#print axioms output_mecid_nonsecure
#print axioms create_output_eq
#print axioms create_output_total
#print axioms normal_nc_total
end ArmCertWalk
