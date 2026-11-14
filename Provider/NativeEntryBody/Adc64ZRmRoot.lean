import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary

import NativeEntry.Fields

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace NativeEntryBody.Adc64ZRm

/- GENERATED from the official selected decoder, using the existing driver.
Keeps actual undefined-choice state/counters; op's unused choice is overwritten.
No outer decode, modelStep, fetch/landing-pad or final program/CT claim. -/
set_option maxHeartbeats 100000 in
drive_spec effect_native, effect_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      (Rd : BitVec 5) (Rn : BitVec 5)
      (rd : Rd.toNat < 31)
      (rn : Rn.toNat < 31)
      (el : s.regs.PSTATE.EL = 0#2)
      (a64 : s.regs.PSTATE.nRW = 0#1)
      (aa64 : s.regs.FeatureImpl[4]! = true)
      (btype : s.regs.PSTATE.BTYPE = 0#2)
      (btn : s.regs.BTypeNext = 0#2) =>
    ((do let _ ← (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 0#1 0#1 1#1 : SailM Unit)
         let u ← get
         pure (u.regs, u.mem, u.events)) : SailM _) s

#print axioms effect_complete
end NativeEntryBody.Adc64ZRm
