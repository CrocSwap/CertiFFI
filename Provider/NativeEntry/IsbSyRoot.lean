import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
import NativeEntry.IsbSyDispatch

import NativeEntry.Fields

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace NativeEntry.IsbSy

/- GENERATED from the official selected decoder, using the existing driver.
Keeps actual undefined-choice state/counters; op's unused choice is overwritten.
No outer decode, modelStep, fetch/landing-pad or final program/CT claim. -/
set_option maxHeartbeats 400000 in
drive_spec effect_native, effect_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      
      (el : s.regs.PSTATE.EL = 0#2)
      (a64 : s.regs.PSTATE.nRW = 0#1)
      (aa64 : s.regs.FeatureImpl[4]! = true)
      (aa32el2 : s.regs.FeatureImpl[2]! = false)
      (aa32el3 : s.regs.FeatureImpl[3]! = false)
      (aa64el2 : s.regs.FeatureImpl[6]! = true)
      (aa64el3 : s.regs.FeatureImpl[7]! = true)
      (rme : s.regs.FeatureImpl[232]! = false)
      (e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
      (tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
      (ns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
      (brbe : s.regs.FeatureImpl[230]! = false)
      (spe : s.regs.bank_Bool .SPESampleInFlight = false) =>
    ((do let _ ← (decode_isb_aarch64_instrs_system_barriers_isb 2#2 15#4 : SailM Unit)
         let u ← get
         pure (u.regs, u.mem, u.events)) : SailM _) s

#print axioms effect_complete
end NativeEntry.IsbSy
