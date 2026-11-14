import ArmCertCTNative.EventObservation

set_option autoImplicit false
set_option maxHeartbeats 100000

/-! Additive traffic vocabulary for AF/dirty updates. This is not a complete
V2 observer or native CT theorem. V1 remains unchanged. Terminal BRK/barriers,
history-aware public recovery and the actual update frame require final heads. -/
namespace ArmCertCT.Native.V2
open Sail.ConcurrencyInterfaceV1

inductive TrafficKind where
  | ttwRead | ttwWrite | ifetch | translationStart | translationEnd
  deriving DecidableEq, Repr

structure TrafficRec where
  pa : Nat
  size : Nat
  kind : TrafficKind
  deriving DecidableEq, Repr

def promote (r : DerivedRec) : TrafficRec :=
  ⟨r.pa, r.size, match r.kind with
    | .ttw => .ttwRead
    | .ifetch => .ifetch
    | .translationStart => .translationStart
    | .translationEnd => .translationEnd⟩

variable [Arch]

def IsTTWWrite : Event → Prop
  | .memWrite _ _ _ (.AK_ttw _) _ _ => True
  | _ => False

/-- One ordered stream, with direction, actual PA and actual request size.
TTW writes are never silently classified as other or separated from reads.
Write payload/tag erasure needs the final public descriptor-update proof;
this definition supplies no such proof or fault-free/terminal claim. -/
def trafficRec : Event → Option TrafficRec
  | .memRead pa size _ (.AK_ttw _) _ => some ⟨pa, size, .ttwRead⟩
  | .memWrite pa size _ (.AK_ttw _) _ _ => some ⟨pa, size, .ttwWrite⟩
  | .memRead pa size _ (.AK_ifetch _) _ => some ⟨pa, size, .ifetch⟩
  | .translationStart _ => some ⟨0, 0, .translationStart⟩
  | .translationEnd _ => some ⟨0, 0, .translationEnd⟩
  | _ => none

def trafficOf (delta : Array Event) : List TrafficRec :=
  delta.toList.filterMap trafficRec

def projectEvent (e : Event) : Projected :=
  match e with
  | .memWrite _ _ _ (.AK_ttw _) _ _ => .derived
  | _ => ArmCertCT.Native.projectEvent e

/-- This intermediate coverage predicate is deliberately NOT a BRK/barrier
contract. Those remain other until the actual terminal/control API is bound. -/
def NoOtherEvents (delta : Array Event) : Prop :=
  ∀ e ∈ delta.toList, projectEvent e ≠ .other

theorem ttw_write_record (pa size : Nat) (va : Option Nat) (u : Unit)
    (value : Option (BitVec (8 * size))) (tag : Option Bool) :
    trafficRec (.memWrite pa size va (.AK_ttw u) value tag) =
      some ⟨pa, size, .ttwWrite⟩ := rfl

theorem ttw_write_derived (pa size : Nat) (va : Option Nat) (u : Unit)
    (value : Option (BitVec (8 * size))) (tag : Option Bool) :
    projectEvent (.memWrite pa size va (.AK_ttw u) value tag) = .derived := rfl

theorem trafficOf_append (a b : Array Event) :
    trafficOf (a ++ b) = trafficOf a ++ trafficOf b := by
  simp [trafficOf, Array.toList_append, List.filterMap_append]

/-- Compatibility is only asserted when actual TTW writes are absent. -/
theorem trafficRec_legacy (e : Event) (quiet : ¬ IsTTWWrite e) :
    trafficRec e = (derivedRec e).map promote := by
  cases e <;> simp_all [trafficRec, derivedRec, IsTTWWrite, promote]
  all_goals split <;> simp_all [promote]

end ArmCertCT.Native.V2
