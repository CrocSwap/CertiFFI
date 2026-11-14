import Pilot.Driver
import Pilot.EvalProfile
import Pilot.UndefSummaries
import Pilot.NativeExport
import Pilot.GPRSummary
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
set_option linter.unusedVariables false

/- GCS PCR at EL0 is disabled by SCR_EL3.GCSEn = 0, a source literal (TRM RES0: FEAT_GCS is absent on
GB10), together with FEAT_AA64EL0. GCSCRE0_EL1.PCRSEL is not assumed. -/
drive_spec gcs_native, gcs_complete :
  fun (s : SequentialState Regs oracleChoiceSource)
      (gcsEn : _get_SCR_EL3_Type_GCSEn (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1)
    => (GCSPCREnabled 0#2 : SailM Bool) s

theorem gcs_disabled (s : SequentialState Regs oracleChoiceSource)
    (gcsEn : _get_SCR_EL3_Type_GCSEn (s.regs.bank_BitVec_64 .SCR_EL3) = 0#1)
    (aa64 : s.regs.FeatureImpl[4] = true) :
    (GCSPCREnabled 0#2 : SailM Bool) s = .ok false s := by
  rw [gcs_complete s gcsEn]
  unfold gcs_native
  split <;> (try split) <;> simp_all
attribute [step_summary] gcs_disabled

#print axioms gcs_complete
#print axioms gcs_disabled
end NativeEntryCallerParts
