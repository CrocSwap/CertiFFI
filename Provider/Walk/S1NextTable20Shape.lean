import Walk.S1NextTable20PAS
import Walk.S1NextTable10Facts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
set_option maxRecDepth 1000000
namespace S1NextTable20Shape
abbrev State := S1TablePrefix.State
def Effect (current : TTWState) (d : BitVec 64) :
    EStateM.Result (Sail.Error exception) State TTWState → Prop
  | .ok next _ => S1NextTable10Facts.Shape current d next
  | .error _ _ => False

theorem native (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams)
    (d : BitVec 64) (s : State) (hPAS : current.baseaddress.paspace = .PAS_NonSecure) :
    Effect current d (S1NextTable.native current s2fs1mro wp d s) := by
  observe_simp [Effect, S1NextTable10Facts.Shape, S1NextTable10Facts.base, S1NextTable.native]

theorem certificate_shape (wp : S1TTWParams) (current : TTWState) (d va : BitVec 64)
    (s2fs1mro : Bool) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (c : S1TablePrefix.Certificate wp current d va s2fs1mro s) :
    S1NextTable10Facts.Shape current d c.next := by
  have h := native current s2fs1mro wp d s hPAS
  rw [← S1NextTable.complete current s2fs1mro wp d s hD128 hDS hTG, c.next_eq] at h
  exact h
#print axioms certificate_shape
end S1NextTable20Shape
