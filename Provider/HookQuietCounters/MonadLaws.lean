import HookQuietCounters.PMUQueries
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
namespace HookQuietCounters
/- Normalize the compiler's map optimization using actual EStateM semantics. -/
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.MonadLaws.map_as_bind"
  (← IO.getStderr).flush

theorem map_as_bind {α β : Type} (f : α → β) (x : SailM α) :
    (f <$> x) = (x >>= fun a => pure (f a)) := by
  funext s
  simp only [map_apply, bind_app]
  cases x s <;> rfl
run_cmd do
  IO.eprintln "CURRENT_DECL HookQuietCounters.MonadLaws.bind_dif"
  (← IO.getStderr).flush

theorem bind_dif {m : Type → Type} [Monad m] {α β : Type}
    (p : Prop) [Decidable p] (x : p → m α) (y : ¬p → m α) (f : α → m β) :
    ((if h : p then x h else y h) >>= f) =
      (if h : p then x h >>= f else y h >>= f) := by
  split <;> rfl
#print axioms bind_dif
#print axioms map_as_bind
end HookQuietCounters
