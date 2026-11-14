import BridgeV2.ConsumerMap

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 100000
namespace ArmCert.Translate.Model
abbrev GPState := SequentialState Regs oracleChoiceSource

/-- The source IFETCH bookkeeping update, retaining the actual guarded-page
    Boolean. No GP=false table restriction is needed for this projection. -/
def gpRegs (regs : Regs) (guarded : Bool) : Regs :=
  {regs with bank_Bool := RegMap.set regs.bank_Bool .InGuardedPage guarded}

theorem set_guarded_page (s : GPState) (guarded : Bool) :
    SetInGuardedPage guarded s = .ok () {s with regs := gpRegs s.regs guarded} := rfl

theorem gp_projected_frame (regs : Regs) (guarded : Bool) :
    ArmCert.Premises.TranslationAgreesV1.ProjRegsEq regs (gpRegs regs guarded) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms set_guarded_page
#print axioms gp_projected_frame
end ArmCert.Translate.Model
