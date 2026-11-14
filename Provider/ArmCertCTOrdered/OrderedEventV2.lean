import ArmFull.Defs
import ArmCertCTNative.EventTransport
import ArmCertCTNative.UpdateTrafficV2

set_option autoImplicit false
set_option maxHeartbeats 100000

/-! Development component. This is ordered event vocabulary, not a
complete observer certificate, actual step theorem, new runner or CT result.
Old observers and frozen UpdateTrafficV2 remain unchanged. -/
namespace ArmCertCTOrdered.OrderedEventV2
open Sail.ConcurrencyInterfaceV1 ArmFull
open ArmCertCT.Native

inductive Record where
  | access (value : DataAccess)
  | traffic (value : V2.TrafficRec)
  | isb
  deriving DecidableEq, Repr

/- The concrete Arm Arch instance is required for its actual ISB constructor. -/

/-- ISB is an actual control event. Other unsupported events remain explicit
coverage holes; no claim that a hole has no secret-dependent payload or effect.
Existing payload/tag/translation-marker erasure obligations remain separate. -/
def record (event : Event) : Option Record :=
  match event with
  | .barrier (.Barrier_ISB _) => some .isb
  | _ =>
    match V2.trafficRec event with
    | some value => some (.traffic value)
    | none =>
      match ArmCertCT.Native.projectEvent event with
      | .access value => some (.access value)
      | _ => none

/-- Exactly one slot per actual raw event, in its original order, including
unsupported slots. In particular an ISB cannot disappear through filterMap.
Explicit access splitting is retained in addition to the legacy merged view. -/
def recordsOf (delta : Array Event) : List (Option Record) :=
  delta.toList.map record

def Covered (delta : Array Event) : Prop :=
  ∀ event ∈ delta.toList, (record event).isSome = true

structure Observation where
  legacy : ArmCertCT.Native.Observation
  events : List (Option Record)

/-- A pure observation constructor only. The final consumer must bind delta
to the SAME actual appended native-step events, and pc/word/nextPC to that step.
Covered is not enough: all erased fields and timing operands need their own
actual profile/public-state/dependence proofs. No public recovery answer or
future history certificate is accepted or constructed here. -/
def ofDelta (pc : BitVec 64) (word : BitVec 32) (nextPC : BitVec 64)
    (delta : Array Event) : Observation :=
  ⟨⟨pc, word, nextPC, obsAccesses delta⟩, recordsOf delta⟩

theorem record_isb : record (.barrier (.Barrier_ISB ())) = some .isb := rfl

theorem record_ttw_write (pa size : Nat) (va : Option Nat) (u : Unit)
    (value : Option (BitVec (8 * size))) (tag : Option Bool) :
    record (.memWrite pa size va (.AK_ttw u) value tag) =
      some (.traffic ⟨pa, size, .ttwWrite⟩) := rfl

theorem recordsOf_append (left right : Array Event) :
    recordsOf (left ++ right) = recordsOf left ++ recordsOf right := by
  simp [recordsOf]

/-- Even unsupported events retain their slot; classification does not silently
shorten a trace. Coverage and semantic erasure are still separate obligations. -/
theorem recordsOf_size (delta : Array Event) :
    (recordsOf delta).length = delta.size := by
  simp [recordsOf]

theorem recordsOf_push_isb (delta : Array Event) :
    recordsOf (delta.push (.barrier (.Barrier_ISB ()))) = recordsOf delta ++ [some .isb] := by
  simp [recordsOf, record]

theorem covered_append (left right : Array Event) :
    Covered (left ++ right) ↔ Covered left ∧ Covered right := by
  simp only [Covered, Array.toList_append, List.mem_append]
  constructor
  · intro h
    exact ⟨fun event member => h event (Or.inl member),
      fun event member => h event (Or.inr member)⟩
  · intro h event member
    exact member.elim (h.1 event) (h.2 event)

theorem covered_push_isb (delta : Array Event) :
    Covered (delta.push (.barrier (.Barrier_ISB ()))) ↔ Covered delta := by
  simp only [Covered, Array.toList_push, List.mem_append, List.mem_singleton]
  constructor
  · intro h event member
    exact h event (Or.inl member)
  · intro h event member
    rcases member with member | rfl
    · exact h event member
    · rfl

theorem ofDelta_legacy (pc : BitVec 64) (word : BitVec 32) (nextPC : BitVec 64)
    (delta : Array Event) :
    (ofDelta pc word nextPC delta).legacy =
      ⟨pc, word, nextPC, obsAccesses delta⟩ := rfl

#print axioms record_isb
#print axioms record_ttw_write
#print axioms recordsOf_append
#print axioms recordsOf_size
#print axioms recordsOf_push_isb
#print axioms covered_append
#print axioms covered_push_isb
#print axioms ofDelta_legacy
end ArmCertCTOrdered.OrderedEventV2
