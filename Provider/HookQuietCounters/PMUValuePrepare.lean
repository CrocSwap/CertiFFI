import HookQuietCounters.PMUValueParts
import HookQuietCounters.QueryM
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
namespace HookQuietCounters

run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.PMUValuePrepare.pmu_value_prepare_query"
  (← IO.getStderr).flush

theorem pmu_value_prepare_query (n : Nat) (Vb : Int) (hn : n < 31) :
    QueryM (PMUValueParts.prepare n Vb) := by
  simp only [PMUValueParts.prepare, HavePMUv3TH, HavePMUv3EDGE,
    map_as_bind, bind_assoc, pure_bind]
  refine QueryM.bind (QueryM.occ 545) (fun l0 => ?_)
  refine QueryM.bind (QueryM.bool l0) (fun Vp => ?_)
  refine QueryM.bind (QueryM.occ 546) (fun l1 => ?_)
  refine QueryM.bind (QueryM.bits l1 2) (fun tc => ?_)
  refine QueryM.bind (QueryM.feature .FEAT_PMUv3_TH) (fun haveTH => ?_)
  refine QueryM.bind ?_ (fun w2 => ?_)
  · apply QueryM.ite
    · exact QueryM.pure true
    · exact QueryM.bind QueryM.have_a64 (fun a64 => QueryM.pure (!a64))
  · cases w2 with
    | true => exact QueryM.pure none
    | false =>
      simp only [Bool.false_eq_true, reduceIte]
      refine QueryM.bind (QueryM.read PMEVTYPER_EL0) (fun row0 => ?_)
      refine QueryM.bind (QueryM.occ 547) (fun l2 => ?_)
      refine QueryM.bind (QueryM.bool l2) (fun Vc0 => ?_)
      refine QueryM.bind (QueryM.read PMEVTYPER_EL0) (fun row1 => ?_)
      refine QueryM.bind (QueryM.occ 548) (fun l3 => ?_)
      refine QueryM.bind (QueryM.int l3) (fun Vt0 => ?_)
      refine QueryM.bind (QueryM.read PMEVTYPER_EL0) (fun row2 => ?_)
      refine QueryM.bind (QueryM.occ 549) (fun l4 => ?_)
      refine QueryM.bind (QueryM.int l4) (fun v0 => ?_)
      refine QueryM.bind (QueryM.feature .FEAT_PMUv3_EDGE) (fun haveEDGE => ?_)
      refine QueryM.bind ?_ (fun active => ?_)
      · apply QueryM.ite
        · exact QueryM.bind (QueryM.read PMEVTYPER_EL0) (fun row3 => QueryM.pure _)
        · exact QueryM.pure false
      · refine QueryM.bind ?_ (fun v => QueryM.pure _)
        apply QueryM.ite
        · refine QueryM.bind ?_ (fun _ => ?_)
          · apply QueryM.assert
            simp; omega
          · refine QueryM.bind (QueryM.read PMULastThresholdValue) (fun threshold => ?_)
            refine QueryM.bind (QueryM.read PMEVTYPER_EL0) (fun row4 => ?_)
            refine QueryM.bind ?_ (fun tc1 => QueryM.pure _)
            apply QueryM.ite
            · refine QueryM.bind (QueryM.occ 550) (fun l5 => ?_)
              refine QueryM.bind (QueryM.constraint l5) (fun c0 => ?_)
              refine QueryM.bind QueryM.restc (fun p => QueryM.pure _)
            · exact QueryM.pure _
        · exact QueryM.pure _
#print axioms pmu_value_prepare_query
end HookQuietCounters
