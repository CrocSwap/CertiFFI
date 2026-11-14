import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary


open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace NativeEntry.BtiC

/- GENERATED from the official selected decoder, using the existing driver.
Keeps actual undefined-choice state/counters; op's unused choice is overwritten.
No outer decode, modelStep, fetch/landing-pad or final program/CT claim. -/
set_option maxHeartbeats 100000 in
drive_spec effect_native, effect_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      
       =>
    ((do let _ ← (decode_bti_aarch64_instrs_system_hints 2#3 4#4 : SailM Unit)
         let u ← get
         pure (u.regs, u.mem, u.events)) : SailM _) s

#print axioms effect_complete
end NativeEntry.BtiC
