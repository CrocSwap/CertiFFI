import Walk.S1NextTable10
import Walk.S1Normality
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1NextTable10Facts
open S1Normality

def base (d : BitVec 64) : BitVec 56 :=
  Sail.BitVec.updateSubrange (0#56) 47 12 (Sail.BitVec.extractLsb d 47 12)
def Shape (current : TTWState) (d : BitVec 64) (next : TTWState) : Prop :=
  next.istable = true ∧ next.level = current.level + 1 ∧
  next.baseaddress.address = base d ∧ next.baseaddress.paspace = .PAS_NonSecure ∧
  next.memattrs = current.memattrs ∧ next.nG = current.nG ∧ next.disch = 0#1

def Effect (current : TTWState) (d : BitVec 64) (s : State) :
    EStateM.Result (Sail.Error exception) State TTWState → Prop
  | .ok next t => Frame s t ∧ Shape current d next
  | .error _ _ => False

theorem native_effect (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams)
    (d : BitVec 64) (s : State)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure) :
    Effect current d s (S1NextTable10.native current s2fs1mro wp d s) := by
  observe_simp [Effect, Frame, Shape, base, S1NextTable10.native]

theorem total (current : TTWState) (s2fs1mro : Bool) (wp : S1TTWParams)
    (d : BitVec 64) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure) :
    ∃ next t, AArch64_S1NextWalkStateTable current s2fs1mro .Regime_EL10 wp d s =
      .ok next t ∧ Frame s t ∧ Shape current d next := by
  rw [S1NextTable10.complete current s2fs1mro wp d s hD128 hDS hTG]
  have hf := native_effect current s2fs1mro wp d s hPAS
  cases hr : S1NextTable10.native current s2fs1mro wp d s with
  | error err t => simp only [hr, Effect] at hf
  | ok next t => exact ⟨next, t, rfl, by simpa only [hr, Effect] using hf⟩
#print axioms total
end S1NextTable10Facts
