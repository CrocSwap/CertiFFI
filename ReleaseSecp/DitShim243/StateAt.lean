-- Generic stateAt bridge, source-lifted from RtDit/DitBody without its heap run.
import TranslateSpan.DefaultScalarTrace
open Sail ArmFull ArmFull.Functions ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxCore CertiFFI.Prog.Generic.ModelRunView
set_option autoImplicit false
namespace RtDit

theorem stateAt_succ_of {real : Type} [Sail.SailReal real] {s fin : NativeState} {k : Nat}
    (run : modelStep real (stateAt real s k) = .ok () fin) : stateAt real s (k + 1) = fin := by
  show next real (stateAt real s k) = fin
  unfold next; rw [run]
end RtDit
