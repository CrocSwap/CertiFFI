import Walk.S1TablePrefix
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 300000
set_option maxRecDepth 1000000
namespace S1NextTable20PAS
abbrev State := S1TablePrefix.State
def pas : EStateM.Result (Sail.Error exception) State TTWState → Option PASpace
  | .ok next _ => some next.baseaddress.paspace
  | .error _ _ => none

theorem native (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams)
    (d : BitVec 64) (s : State) (hPAS : current.baseaddress.paspace = .PAS_NonSecure) :
    pas (S1NextTable.native current s2fs1mro wp d s) = some .PAS_NonSecure := by
  observe_simp [pas, S1NextTable.native]

theorem certificate_pas (wp : S1TTWParams) (current : TTWState) (d va : BitVec 64)
    (s2fs1mro : Bool) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (c : S1TablePrefix.Certificate wp current d va s2fs1mro s) :
    c.next.baseaddress.paspace = .PAS_NonSecure := by
  have h := native current s2fs1mro wp d s hPAS
  rw [← S1NextTable.complete current s2fs1mro wp d s hD128 hDS hTG, c.next_eq] at h
  exact Option.some.inj h
#print axioms certificate_pas
end S1NextTable20PAS
