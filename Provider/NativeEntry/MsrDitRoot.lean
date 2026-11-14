import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
import NativeEntry.MsrDitDispatch

import NativeEntry.Fields

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
namespace NativeEntry.MsrDit

/- GENERATED from the official selected decoder, using the existing driver.
Keeps actual undefined-choice state/counters; op's unused choice is overwritten.
No outer decode, modelStep, fetch/landing-pad or final program/CT claim. -/
set_option maxHeartbeats 400000 in
drive_spec effect_native, effect_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      (Rt : BitVec 5)
      (rt : Rt.toNat < 31)
      (el : s.regs.PSTATE.EL = 0#2)
      (a64 : s.regs.PSTATE.nRW = 0#1)
      (aa64 : s.regs.FeatureImpl[4]! = true)
      (btype : s.regs.PSTATE.BTYPE = 0#2)
      (btn : s.regs.BTypeNext = 0#2)
      (dit : s.regs.FeatureImpl[103]! = true)
      (bti : s.regs.FeatureImpl[123]! = true)
      (tme : s.regs.FeatureImpl[227]! = false)
      (pmuLower : 0 ≤ s.regs.bank_Int .NUM_PMU_COUNTERS)
      (pmuUpper : s.regs.bank_Int .NUM_PMU_COUNTERS ≤ 31)
      (ns : _get_SCR_EL3_Type_NS (s.regs.bank_BitVec_64 .SCR_EL3) = 1#1)
      (aa32el2 : s.regs.FeatureImpl[2]! = false)
      (aa32el3 : s.regs.FeatureImpl[3]! = false)
      (aa64el2 : s.regs.FeatureImpl[6]! = true)
      (aa64el3 : s.regs.FeatureImpl[7]! = true)
      (rme : s.regs.FeatureImpl[232]! = false)
      (e2h : _get_HCR_EL2_Type_E2H (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
      (tge : _get_HCR_EL2_Type_TGE (s.regs.bank_BitVec_64 .HCR_EL2) = 1#1)
      (not_br : Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 .__ThisInstr) 31 25 ≠ 107#7)
      (not_bti : Sail.BitVec.extractLsb (s.regs.bank_BitVec_32 .__ThisInstr) 21 12 ≠ 50#10) =>
    ((do let _ ← (decode_msr_reg_aarch64_instrs_system_register_system Rt 5#3 2#4 4#4 3#3 1#1 0#1 : SailM Unit)
         let u ← get
         pure (u.regs, u.mem, u.events)) : SailM _) s

#print axioms effect_complete
end NativeEntry.MsrDit
