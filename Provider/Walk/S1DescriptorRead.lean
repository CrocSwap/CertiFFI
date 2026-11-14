import Walk.S1TableTranslate10
import Pilot.S2FetchFrame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
namespace S1DescriptorRead
abbrev State := S1WalkInvalid.State
abbrev Return := S1WalkInvalid.Return
abbrev Value := Bool × BitVec 64 × FaultRecord × Bool × FaultRecord × Bool

def action (enabled aligned a64 s2fs1mro : Bool) (ee : BitVec 1)
    (fault s2fault : FaultRecord) (addr : AddressDescriptor) (level : Int)
    (acc : AccessDescriptor) (ti : TranslationInfo) : SailME Return Value := do
  if enabled then do
    let (s2fault, pa) ← AArch64_S2Translate fault addr true (some level) true acc
    if bne s2fault.statuscode .Fault_None then S1WalkTable10.early s2fault else pure ()
    let (fault, d) ← FetchDescriptor ee pa acc fault 64 ti
    pure (true, d, fault, true, s2fault, pa.s2fs1mro)
  else do
    let (fault, d) ← FetchDescriptor ee addr acc fault 64 ti
    pure (aligned, d, fault, a64, s2fault, s2fs1mro)

theorem total (enabled aligned a64 s2fs1mro : Bool) (ee : BitVec 1)
    (fault s2fault : FaultRecord) (addr : AddressDescriptor) (level : Int)
    (acc : AccessDescriptor) (ti : TranslationInfo) (data : BitVec 64)
    (cfg : S2Interface.Config) (s : State)
    (hConfig : S2Interface.ConfigAt cfg s)
    (hVM : _get_HCR_EL2_Type_VM cfg.hcr = 0#1)
    (hDC : _get_HCR_EL2_Type_DC cfg.hcr = 0#1)
    (hSS : acc.ss = .SS_NonSecure)
    (hNoRME : s.regs.FeatureImpl[232] = false)
    (hRAM : S2TableRAM.OrdinaryRAM addr.paddress.address)
    (hOld : S2ByteMemory.DescAt s.mem addr.paddress.address.toNat data) :
    ∃ (alignedOut a64Out : Bool) (s2faultOut : FaultRecord) (t : State),
      action enabled aligned a64 s2fs1mro ee fault s2fault addr level acc ti s =
        .ok (.ok (alignedOut, S2FetchFrame.decoded ee data, fault, a64Out, s2faultOut,
          if enabled then addr.s2fs1mro else s2fs1mro)) t ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  have hNoFault : ((.Fault_None : Fault) != .Fault_None) = false := by decide
  cases enabled with
  | false =>
    rcases S2FetchFrame.total ee fault data acc addr ti s hNoRME hRAM hOld with
      ⟨t, hf, hr, hm⟩
    refine ⟨aligned, a64, s2fault, t, ?_, hr, hm⟩
    simp [action, Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, EStateM.bind, EStateM.map, EStateM.pure,
      liftM, MonadLiftT.monadLift, MonadLift.monadLift, hf]
  | true =>
    rcases S2VM0Frame.total cfg fault addr true (some level) true acc s
      hConfig hVM hDC hSS with ⟨t1, ht, hr1, hm1, _⟩
    rcases S2FetchFrame.total ee fault data acc addr ti t1
      (by simpa only [hr1] using hNoRME) hRAM
      (by simpa only [hm1] using hOld) with ⟨t, hf, hr2, hm2⟩
    refine ⟨true, true, S2VM0Frame.faultOut fault addr acc, t, ?_, hr2.trans hr1, hm2.trans hm1⟩
    simp [action, Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, EStateM.bind, EStateM.map, EStateM.pure,
      liftM, MonadLiftT.monadLift, MonadLift.monadLift, ht, hf, S2VM0Frame.status, hNoFault]
#print axioms total
end S1DescriptorRead
