import HookQuietCounters.OverflowFacts
import Lean.Elab.Command
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option profiler true
set_option profiler.threshold 1000
set_option Elab.async false
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false
namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.OverflowTail.overflow_tail"
  (← IO.getStderr).flush

theorem overflow_tail (check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool)
    (ovsf : BitVec 64) (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true) :
    ∃ b, OverflowParts.tail check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc exclude_sync ovsf s = .ok b s := by
  have hA := have_a64 s ha
  have hI : (HavePMUv3ICNTR () : SailM Bool) s = .ok (featureValue s .FEAT_PMUv3_ICNTR) s := rfl
  cases check_e <;> cases check_cnten <;> cases check_inten <;>
    cases include_lo_name <;> cases exclude_cyc <;>
    cases hIC : featureValue s .FEAT_PMUv3_ICNTR <;>
    simp [OverflowParts.tail, bind_assoc, bind_if, pure_bind, bind_app,
      hA, hI, hIC, read_apply, pure_apply, map_apply, if_apply]

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.OverflowTail.overflow_tail_masked"
  (← IO.getStderr).flush

theorem overflow_tail_masked (check_e check_cnten include_hi_name include_lo_name exclude_cyc exclude_sync : Bool)
    (ovsf : BitVec 64) (s : NativeState) (ha : featureValue s .FEAT_AA64EL0 = true)
    (hm : s.regs.bank_BitVec_64 .PMINTENCLR_EL1 = 0#64) :
    OverflowParts.tail check_e check_cnten true include_hi_name include_lo_name exclude_cyc exclude_sync ovsf s = .ok false s := by
  have hA := have_a64 s ha
  have hI : (HavePMUv3ICNTR () : SailM Bool) s = .ok (featureValue s .FEAT_PMUv3_ICNTR) s := rfl
  have hM : (readReg PMINTENCLR_EL1 : SailM (BitVec 64)) s = .ok 0#64 s := by
    rw [read_apply]
    congr 1
  cases check_e <;> cases check_cnten <;> cases include_lo_name <;> cases exclude_cyc <;>
    cases hIC : featureValue s .FEAT_PMUv3_ICNTR <;>
    simp [OverflowParts.tail, bind_assoc, bind_if, pure_bind, bind_app,
      hA, hI, hM, hIC, read_apply, pure_apply, map_apply, if_apply, IsZero, Zeros]
#print axioms overflow_tail
#print axioms overflow_tail_masked
end HookQuietCounters
