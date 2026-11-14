import HookQuietCounters.ICNTRParts
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
  IO.eprintln "CURRENT_DECL HookQuietCounters.ICNTRBody.icntr_body_success"
  (← IO.getStderr).flush

theorem icntr_body_success (inc : Int) (s : NativeState) :
    ∃ t, ICNTRParts.body inc s = .ok () t := by
  simp only [ICNTRParts.body, bind_app, read_apply, write_apply]
  split
  · simp only [bind_app, read_apply, write_apply]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
#print axioms icntr_body_success
end HookQuietCounters
