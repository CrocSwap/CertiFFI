import M1a.Outer
import Walk.S1NextTable20Shape
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a

/-- Inherited table permissions unchanged by a table step. -/
def PermKeep (current : TTWState) :
    EStateM.Result (Sail.Error exception) State TTWState → Prop
  | .ok next _ => next.permissions.ap_table = current.permissions.ap_table ∧
      next.permissions.uxn_table = current.permissions.uxn_table
  | .error _ _ => False

/-- Table descriptor with APTable = UXNTable = 0 (PXNTable unconstrained: real Linux
    user tables set it; it does not affect EL0 accesses). -/
def TablePermsZero (d : BitVec 64) : Prop :=
  Sail.BitVec.extractLsb d 62 61 = 0#2 ∧ BitVec.join1 [BitVec.access d 60] = 0#1

theorem perm_native (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams) (d : BitVec 64)
    (s : State) (hz : TablePermsZero d) :
    PermKeep current (S1NextTable.native current s2fs1mro wp d s) := by
  rcases hz with ⟨h62, h60⟩
  observe_simp [PermKeep, S1NextTable.native]
  all_goals simp [h62, h60]

/-- The actual EL2&0 table step keeps the inherited table permissions. -/
theorem perm_certificate (wp : S1TTWParams) (current : TTWState) (d va : BitVec 64)
    (s2fs1mro : Bool) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hz : TablePermsZero d) (c : S1TablePrefix.Certificate wp current d va s2fs1mro s) :
    c.next.permissions.ap_table = current.permissions.ap_table ∧
    c.next.permissions.uxn_table = current.permissions.uxn_table := by
  have h := perm_native current s2fs1mro wp d s hz
  rw [← S1NextTable.complete current s2fs1mro wp d s hD128 hDS hTG, c.next_eq] at h
  exact h

#print axioms perm_native
#print axioms perm_certificate

end ArmCert.Eval.M1a
