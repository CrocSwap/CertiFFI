import BridgeDraft.StateProjection
import Pilot.GPRSummary
open Sail.ConcurrencyInterfaceV1
open ArmBridge.Draft
-- d193 split (certiffi): Sail-side content only; the LNSym content moved to Bridge.ProjLNSym.
namespace ArmBridge.Proj

theorem key_val : ∀ n, n < 31 → (GPRSummary.key n).val = n := by decide

end ArmBridge.Proj

