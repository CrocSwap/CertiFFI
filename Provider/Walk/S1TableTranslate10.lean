import Walk.S1WalkTable10
import Pilot.S2VM0Frame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1TableTranslate10
abbrev State := S1WalkInvalid.State

def action (enabled aligned a64 : Bool) (fault s2fault : FaultRecord)
    (walkaddr : AddressDescriptor) (level : Int) (acc : AccessDescriptor) :
    SailME S1WalkInvalid.Return (Bool × AddressDescriptor × Bool × FaultRecord) := do
  if enabled then do
    let (f, pa) ← AArch64_S2Translate fault walkaddr true (some level) true acc
    if bne f.statuscode .Fault_None then S1WalkTable10.early f else pure ()
    pure (true, pa, true, f)
  else pure (aligned, walkaddr, a64, s2fault)

theorem total (enabled aligned a64 : Bool) (fault s2fault : FaultRecord)
    (walkaddr : AddressDescriptor) (level : Int) (acc : AccessDescriptor)
    (cfg : S2Interface.Config) (s : State)
    (hConfig : S2Interface.ConfigAt cfg s)
    (hVM : _get_HCR_EL2_Type_VM cfg.hcr = 0#1)
    (hDC : _get_HCR_EL2_Type_DC cfg.hcr = 0#1)
    (hSS : acc.ss = .SS_NonSecure) :
    ∃ (alignedOut a64Out : Bool) (f : FaultRecord) (t : State),
      action enabled aligned a64 fault s2fault walkaddr level acc s =
        .ok (.ok (alignedOut, walkaddr, a64Out, f)) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  have hNoFault : ((.Fault_None : Fault) != .Fault_None) = false := by decide
  cases enabled with
  | false => exact ⟨aligned, a64, s2fault, s, rfl, rfl, rfl, rfl⟩
  | true =>
    rcases S2VM0Frame.total cfg fault walkaddr true (some level) true acc s
      hConfig hVM hDC hSS with ⟨t, h, hr, hm, he⟩
    refine ⟨true, true, S2VM0Frame.faultOut fault walkaddr acc, t, ?_, hr, hm, he⟩
    simp [action, Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, EStateM.bind, EStateM.map, EStateM.pure,
      liftM, MonadLiftT.monadLift, MonadLift.monadLift, h, S2VM0Frame.status, hNoFault]
#print axioms total
end S1TableTranslate10
