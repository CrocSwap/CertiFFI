import Walk.S1LeafOutputPerms
import Walk.S2Frame
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1LeafOutputPermsFrame
abbrev State := SequentialState Regs oracleChoiceSource
def Frame (s : State) : EStateM.Result (Sail.Error exception) State Permissions → Prop
  | .ok _ t => t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events
  | .error _ _ => False
theorem native_frame (p : Permissions) (d : BitVec 64) (wp : S1TTWParams) (s : State) :
    Frame s (S1LeafOutputPerms.native p d wp s) := by
  observe_simp [Frame, S1LeafOutputPerms.native]
theorem total (p : Permissions) (d : BitVec 64) (wp : S1TTWParams) (s : State)
    (hD128 : wp.d128 = 0#1) :
    ∃ (out : Permissions) (t : State),
      AArch64_S1ApplyOutputPerms p d .Regime_EL20 wp s = .ok out t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rw [S1LeafOutputPerms.complete p d wp s hD128]
  have hf := native_frame p d wp s
  cases hr : S1LeafOutputPerms.native p d wp s with
  | error err t => simp only [hr, Frame] at hf
  | ok out t => exact ⟨out, t, rfl, by simpa only [hr, Frame] using hf⟩
#print axioms total
end S1LeafOutputPermsFrame
